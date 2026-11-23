# Discrete Convolution

Discrete-convolution outflow at step `k` from rainfall excess `p` and
unit response `u`. This is `AdditiveCombinatorics.sumConv` under its
hydrologic name; indices are 0-based where the engineering sources are
1-based (`p i = P (i+1)`, `u j = U (j+1)`, outflow `q k = Q (k+1)`).
Nonnegativity of the sequences is not assumed: the identity holds for
all real sequences.
