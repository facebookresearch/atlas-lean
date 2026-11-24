# TGREEDY is a 3-approximation

**TGREEDY is a 3-approximation** (Blum, Jiang, Li, Tromp and Yannakakis 1994, Theorem 11): for
a nonempty, substring-free list `S` without repetition, for every run of MGREEDY from `S` with an
empty finished list that ends with the finished list `T`, and every result `r` of a run of GREEDY
on `T`, `r` is a common superstring of `S` of length at most `3 OPT(S)`.

## Sources

- Blum, Jiang, Li, Tromp and Yannakakis (1994), Theorem 11.
