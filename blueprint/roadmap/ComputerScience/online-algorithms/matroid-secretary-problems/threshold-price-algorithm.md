# Threshold Price Algorithm: O(log k)-competitive matroid secretary

Let $M$ be a loopless matroid on $n \ge 2$ elements of rank $k$, with nonnegative well-behaved weights, elements arriving in uniformly random order. The *Threshold Price Algorithm* observes the first $s = \lceil n/2 \rceil$ elements without accepting, lets $w^\ast$ be the largest weight among them, draws $j$ uniformly from $\{0, 1, \dots, \lceil\log_2 k\rceil\}$, sets the threshold $w^\ast/2^j$, and then greedily accepts each later positive-weight element above the threshold whose addition keeps the accepted set independent. Its output is always independent and its expected weight is at least

$$
\frac{\mathrm{OPT}}{32\,(\lceil \log_2 k\rceil + 1)},
$$

and at least $\mathrm{OPT}/(64\lceil\log_2 k\rceil)$ when $k \ge 2$.

## Proof sketch

Any two elements are split by the sampling phase with probability at least $1/4$. When the sample contains the heaviest element and an optimal element of weight in $(w^\ast/2^{j+1}, w^\ast/2^j]$ is unsampled, the random exponent hits its scale with probability $1/(\lceil\log_2 k\rceil+1)$, and greedy acceptance at that scale captures a constant fraction of the optimal weight at that scale by the matroid exchange property. Summing over scales gives the bound.

## Depends on

- [Matroid secretary problem](matroid-secretary-problem.md)

## Proof depends on

- [Matroid secretary problem](matroid-secretary-problem.md)

## Sources

- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007.
