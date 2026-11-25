# I/O complexity of permuting

In the single-disk [external-memory model](the-external-memory-model.md), with $N$ indivisible records, internal memory of $M$ records and blocks of $B$ records, the number of I/Os required to permute $N$ records, in the worst case over the $N!$ target permutations and on average over a uniformly random target permutation, for deterministic algorithms and for randomized algorithms averaged over their coins and the uniform target, is

$$\Theta\Bigl(\min\Bigl\{N,\ \frac{N}{B} \cdot \frac{\log(1 + N/B)}{\log(1 + M/B)}\Bigr\}\Bigr).$$

The lower bound holds for every algorithm that realizes all $N!$ permutations; no comparison model is used, since the target permutation is given. When $B \log(1 + M/B) = o(\log(1 + N/B))$, the term $N$ attains the minimum and moving the records one per I/O is optimal. Otherwise the second term attains it, and permuting is as hard as sorting, whose bound is the second term.

**Lower-bound proof.** One may assume that every I/O is *simple*: an input deposits the transferred records into empty internal locations and an output into empty disk locations, so exactly one copy of each record exists throughout. This assumption costs no extra I/Os. Count the orderings of the $N$ records that the algorithm can have produced after $t$ I/Os.
- An output can multiply this number by at most $N/B + t \le N(1 + \log N)$, the number of places for the written block.
- An input of a block can multiply it by at most $(N/B + t - 1)\binom{M}{B}$, the choice of block and of the positions of its records among the internal ones.
- An extra factor $B!$, for the order of a block that has never been in internal memory together, can occur at most $N/B$ times.
Realizing all permutations therefore requires $(B!)^{N/B}\bigl(N(1 + \log N)\binom{M}{B}\bigr)^t \ge N!$, which gives the stated lower bound.

## Depends on

- [The external-memory model](the-external-memory-model.md)

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988: Theorem 3.2 (the bound for permuting) and the discussion after it, with $P = 1$; Lemma 4.1 (simple I/Os) and the counting argument for permuting in Section 4, inequality (4.1) and the bounds leading to the $N!$ comparison.
