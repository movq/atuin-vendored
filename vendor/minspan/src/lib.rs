

// We want to make sure we are getting the shortest match possible
// without getting tripped up by pathological cases.
pub mod minspan {

    pub fn span<A>(query: &Vec<A>, history : &Vec<A>) -> Option<(usize,usize)>
	where
    	A: PartialEq {

	let mut starting_at : Vec<Option<(usize,usize)>> = query.iter().map(|_| None).collect();
	let mut best_complete_solution : Option<(usize,usize)> = None;

	if query.len() == 0 { return Some((0,0)); }

	for (bodyindex, bodychr) in history.iter().enumerate() {
	    for (keyindex, keychr) in query.iter().enumerate() {
		if keychr==bodychr {
		    // we have a match, therefore record it: it ends at bodyindex,
		    // and by construction, starts at starting_at[0]
		    starting_at[keyindex] = if keyindex==0 {
			// we got nothing yet! set to beginning
			Some ((bodyindex,bodyindex))
		    } else {
			match starting_at[keyindex-1] {
			    // no continuation to be had anyway, might as well break
			    None => break,
			    Some((start,_end)) => Some((start,bodyindex)),
			}
		    };
		    // are we finished?
		    if (keyindex + 1) == query.len() {
			best_complete_solution = match (best_complete_solution, starting_at[keyindex]) {
			    (None, Some((from,to))) => Some((from, to)), // 1+to - from),
			    (Some((currfrom,currto)), Some((from,to))) =>
				Some(
				    if to - from < currto - currfrom {
					(from,to)
				    } else {
					(currfrom,currto)
				    }),
			    (_,None) => panic!("this should be impossible"),
			}
		    }

		    // this doesn't matter except as an optimisation.
		    // debug this later.
		    //
		    // would be nice to have an empty range here but nah,doesn't work.
		    //
		    // if false { // 3keyindex > 0 {
		    // 	for deletable in (0_usize..(keyindex - 1)).rev() {
		    // 	    min_match = min_match - 1;
		    // 	    match starting_at[deletable] {
		    // 		Some(deletable_index) =>
		    // 		// if the index in the body is less than min_match,
		    // 		// it's never going to be part of the smallest match,
		    // 		// so reset to None
		    // 		    if deletable_index <= min_match {
		    // 			println!("resetting {:?}, min_match = {:?}", deletable_index, min_match);
		    // 			starting_at[deletable]=None
		    // 		    },
		    // 		None => (),
		    // 	    }
		    // 	}
		    // }
		}
	    }
	}
	best_complete_solution
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_minimal_match() {
	let wrapper = |needle: &str,haystack: &str| {
	    match minspan::span( &needle.chars().collect(),
				  &haystack.chars().collect()) {
		Some ((from,to)) => Some(1+to-from),
		None => None,
	    }
	};

	assert_eq!(wrapper("ab", "ab").unwrap(), 2);
	assert_eq!(wrapper("a", "ab").unwrap(), 1);
	assert_eq!(wrapper("ab", "abc").unwrap(), 2);
	assert_eq!(wrapper("abc", "abcd").unwrap(), 3);
	assert_eq!(wrapper("curl", "curly").unwrap(), 4);
	assert_eq!(wrapper("curl", "acccccurlycurrelly").unwrap(), 4);
	assert_eq!(wrapper("z", "acccccurlycurrelly"), None);
    }
}
