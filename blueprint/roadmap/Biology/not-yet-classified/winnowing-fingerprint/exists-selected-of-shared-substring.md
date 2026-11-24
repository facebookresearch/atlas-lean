# Local algorithms find every long match

**Local algorithms find every long match** (Schleimer, Wilkerson and Aiken 2003, Lemma 1): for
`k ≥ 1`, `w ≥ 1`, guarantee `t = w + k - 1`, any hash `g` of `k`-grams, any selection function
`S` and any local algorithm `F` with selection function `S`: if documents `u` and `v` share a
substring of length `L ≥ t`, at offset `p` in `u` and `q` in `v`, then some `j ≤ L - k` gives
selected `k`-gram positions `p + j` in `u` and `q + j` in `v`, both of which hash the same
`k`-gram of the shared substring.

## Sources

- Schleimer, Wilkerson and Aiken (2003), Lemma 1.
