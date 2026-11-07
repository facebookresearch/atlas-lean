# Binary search for the boundary of a predicate

Binary search for the boundary of a predicate on `[lo, hi)`: the first index at which `p`
is false, assuming `p` holds on an initial segment of `[lo, hi)` (`lowerBound_spec`). Each call
probes the midpoint and recurses on one half.
