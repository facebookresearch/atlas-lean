# MGREEDY is a 4-approximation

**MGREEDY is a 4-approximation** (Blum, Jiang, Li, Tromp and Yannakakis 1994, Theorems 8 and
10: MGREEDY builds an optimal cycle cover, and concatenating the opened cycles of an optimal cycle
cover costs at most `4 OPT(S)`): for a nonempty, substring-free list `S` without repetition, for
every run of MGREEDY from `S` with an empty finished list that ends with the finished list `T`,
the concatenation of `T` is a common superstring of `S` of length at most `4 OPT(S)`.

## Sources

- Blum, Jiang, Li, Tromp and Yannakakis (1994), Theorems 8 and 10.
