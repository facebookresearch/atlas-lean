# The sentinel stops every prefix match

A sentinel-free word `P` is a prefix of `u ++ ⊥ :: v` (letters lifted to `WithBot α`) exactly
when it is a prefix of `u`: the sentinel `⊥` stops every match.
