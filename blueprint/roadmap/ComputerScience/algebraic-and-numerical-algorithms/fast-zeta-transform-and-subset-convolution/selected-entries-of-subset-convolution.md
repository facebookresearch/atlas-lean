# Selected entries of ranked subset convolution

Let $f$ and $g$ be integer-valued set functions on $2^{[d]}$, given sparsely with $n$ nonzero entries in total and both supported on sets of size $t$, and let $\mathcal{C}$ be a list of query sets each of size $2t$. Fix $0 \le s \le 2t$. Then the values $(f \ast g)(C)$ for all $C \in \mathcal{C}$ can be computed on the word RAM in time

$$
\Bigl(n + \binom{d}{\le s} + |\mathcal{C}|\,\binom{2t}{\ge s}\Bigr)\,d^{O(1)},
$$

where $\binom{d}{\le s} = \sum_{i \le s}\binom{d}{i}$ counts the subsets of $[d]$ of size at most $s$ and $\binom{2t}{\ge s} = \sum_{i \ge s}\binom{2t}{i}$ counts the subsets of a query set of size at least $s$ (Chan, Itakura, Ma and Yu, Problem 2.1 and Theorem 2.2).

## Proof sketch

Precompute ranked zeta transforms of both inputs and the Möbius stage tables on all sets of size below $s$, using sparse tries for the inputs. For each query of size at least $s$, run the three trimmed transforms (two zeta, pointwise product, one Möbius) on the subsets obtained by complementation within the query, falling back to the precomputed tables below the threshold.

## Depends on

- [Subset convolution and ranked zeta transforms](ranked-subset-convolution.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Trimmed Yates passes](trimmed-yates-passes.md)
- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](yates-algorithm.md)

## Sources

- T. M. Chan, R. Itakura, Z. Ma and Y. Yu, "3SUM Made Simpler (Without Matrix Multiplication), k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized", arXiv:2610.42012v1, 2026, Problem 2.1 and Theorem 2.2.
- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Trimmed Moebius Inversion and Graphs of Bounded Degree", Theory of Computing Systems 47(3), 2010.
- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Fourier Meets Möbius: Fast Subset Convolution", Proceedings of the 39th ACM Symposium on Theory of Computing (STOC), 2007.
