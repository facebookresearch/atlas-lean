# Selected entries of ranked subset convolution

Let $f$ and $g$ be integer-valued set functions on $2^{[d]}$, given sparsely, with $f$ supported on sets of size $t_1$ and $g$ on sets of size $t_2$, and let $\mathcal{C}$ be a list of query sets each of size $t_1 + t_2$. Fix $s \le t_1 + t_2$. Then the values $(f \ast g)(C)$ for all $C \in \mathcal{C}$ can be computed on the word RAM with at most

$$
200\,(d+1)^2\Big(\mathrm{low}(d, s) + |\mathcal{C}| \cdot \mathrm{high}(t_1 + t_2, s)\Big)
$$

instructions, where $\mathrm{low}(d, s) = \sum_{i < s}\binom{d}{i}$ counts the sets of size below $s$ and $\mathrm{high}(r, s) = \sum_{i \le r - s}\binom{r}{i}$ counts the subsets of a query set needed above the threshold (Chan-Itakura-Ma-Yu, Theorem 2.2, with $t_1 = t_2 = t$).

## Proof sketch

Precompute ranked zeta transforms of both inputs and the Möbius stage tables on all sets of size below $s$, using sparse tries for the inputs. For each query of size at least $s$, run the three trimmed transforms (two zeta, pointwise product, one Möbius) on the subsets obtained by complementation within the query, falling back to the precomputed tables below the threshold.

## Depends on

- [Subset convolution and ranked zeta transforms](ranked-subset-convolution.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Trimmed Yates passes](trimmed-yates-passes.md)
- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](yates-algorithm.md)

## Sources

- T. M. Chan, R. Itakura, Z. Ma and Y. Yu, "3SUM Made Simpler (Without Matrix Multiplication), k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP", 2026.
- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Trimmed Moebius Inversion and Graphs of Bounded Degree", Theory of Computing Systems 47(3), 2010.
- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
