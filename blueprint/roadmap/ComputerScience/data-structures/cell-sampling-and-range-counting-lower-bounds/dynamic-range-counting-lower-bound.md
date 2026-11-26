# Larsen's lower bound for dynamic range counting

Every dynamic cell-probe structure for two-dimensional weighted orthogonal range counting with $n$ insertions, $w$-bit cells and amortized update time $t_u$ has query time $t_q = \Omega\!\left(\left(\frac{\lg n}{\lg(w t_u)}\right)^{2}\right)$. With $w = \Theta(\lg n)$ and $t_u = (\lg n)^{O(1)}$ this is $t_q = \Omega\big((\lg n / \lg\lg n)^2\big)$, almost a quadratic improvement over the previous best $\Omega(\lg n)$, and it is tight for $t_u = \lg^{2 + \Omega(1)} n$.

## Proof sketch

There are $\Theta(\log_\beta n)$ epochs, and by the epoch-wise lemma a random query probes $\Omega(\log_\beta n)$ cells written in each of them; the sets of cells attributed to distinct epochs are disjoint because each cell is charged to the epoch of its last write. Summing gives $\Omega((\log_\beta n)^2)$. A range-tree style structure with fan-out $\lg^{\Omega(1)} n$ over a dominance counting structure achieves the matching query time with $\lg^{2+\Omega(1)} n$ update time.

## Depends on

- [Epoch-wise cell sampling for weighted range counting](epochwise-cell-sampling.md)
- [Larsen's static lower bound for polynomial evaluation](polynomial-evaluation-lower-bound.md)

## Proof depends on

- [Epoch-wise cell sampling for weighted range counting](epochwise-cell-sampling.md)
- [Larsen's static lower bound for polynomial evaluation](polynomial-evaluation-lower-bound.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
- Joseph JaJa, Christian W. Mortensen, Qingmin Shi, "Space-Efficient and Fast Algorithms for Multidimensional Dominance Reporting and Counting", ISAAC (2004).
