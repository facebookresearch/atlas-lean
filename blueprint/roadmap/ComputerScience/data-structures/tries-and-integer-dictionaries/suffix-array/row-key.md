# Truncated suffix of a suffix-array row

The suffix of row `r` of the (precomputed) suffix array `sa` of `s`, truncated to
`m` letters: the key compared with the pattern during the search. `sa` is computed once
by `saSearch` and passed in, so probes do not rebuild the suffix array.
