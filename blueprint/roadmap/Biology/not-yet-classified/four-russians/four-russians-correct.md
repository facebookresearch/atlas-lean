# Four-Russians block correctness and table bound

**Four-Russians block correctness and table bound** (Masek-Paterson 1980,
Algorithm Y): hypotheses are a finite alphabet, integral costs (`hdiscrete`:
every cost is a natural multiple of one positive `c0`), block size `m`
(`hm`), a step range `B`, a table `entries` answering every in-range block
with the true distance (`htable`), and inputs `X`, `Y` with at least `m`
symbols each (`hXY`). Conclusions: the target block problem `P` is matched in
the table with the true distance value, and the table has at most
`|Σ|^(2m) * (2B+1)^(2m)` entries.

## Sources

- Masek-Paterson (1980), Algorithm Y.
