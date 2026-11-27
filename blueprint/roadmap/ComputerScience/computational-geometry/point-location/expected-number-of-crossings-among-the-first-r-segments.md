# Expected number of crossings among the first r segments

Let $S$ be a set of $n \ge 2$ segments with $K$ pairwise crossings, inserted in uniformly random order, and for $2 \le r \le n$ let $k_r$ be the number of crossings among the first $r$ segments (for $r < 2$ there are none). Then

$$\mathbb{E}[k_r] = K\,\frac{\binom{n-2}{r-2}}{\binom{n}{r}} = K\,\frac{r(r-1)}{n(n-1)},$$

since each crossing pair is among the first $r$ segments with probability $\binom{n-2}{r-2}/\binom{n}{r}$.

## Depends on

- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 10 (Trapezoidal maps), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2010.pdf>: Lemma 10.12
