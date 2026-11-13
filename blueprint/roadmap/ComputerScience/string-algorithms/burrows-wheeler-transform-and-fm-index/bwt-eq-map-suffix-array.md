# The transform from the suffix array

`bwt[r] = t$[SA[r] - 1]`, the letter cyclically
before the suffix of row `r` (the sentinel for the row of the whole text, `SA[r] = 0`).
