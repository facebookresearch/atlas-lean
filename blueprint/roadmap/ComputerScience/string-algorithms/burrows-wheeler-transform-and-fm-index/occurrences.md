# Occurrences of a pattern reported by the FM-index

The occurrences of `P` reported by the FM-index: the suffix-array entries
`SA[sp], …, SA[ep - 1]` of the backward-search interval. The BWT and the interval are
bound once with `let` and reused, so one query builds the BWT and runs the backward search
once, not three times.
