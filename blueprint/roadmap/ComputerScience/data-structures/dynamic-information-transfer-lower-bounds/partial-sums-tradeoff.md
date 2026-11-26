# Pătraşcu–Demaine tradeoff for dynamic partial sums

For dynamic partial sums over $\mathbb{Z}/2^{\delta}\mathbb{Z}$ with $\delta = w = \Theta(\lg n)$, every randomized cell-probe structure with amortized costs $t_u, t_q$ satisfies $t_q \lg(t_u/t_q) = \Omega(\lg n)$ and $t_u \lg(t_q/t_u) = \Omega(\lg n)$. In particular $\max\{t_u, t_q\} = \Omega(\lg n)$, which is matched by balanced aggregation trees and breaks the $\Omega(\lg n/\lg\lg n)$ barrier of the chronogram method for problems with $\Theta(\lg n)$-bit answers.

## Proof sketch

By the entropy lemma, a node at depth $d$ whose left interval contains $k = \Theta(m/2^{d})$ updates has $|\mathrm{IT}(v)| = \Omega(k)$, whereas the reads available in $R_v$ number $O(k t_q)$. Summing over the $\Theta(\lg n)$ levels and charging each read once gives $\Omega(m \lg n)$ total probes, which yields $\max(t_u,t_q) = \Omega(\lg n)$; the tradeoff form comes from grouping $\lg(t_u/t_q)$ consecutive levels into one, so that queries pay for transfer across several levels at once while updates pay for the rest.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Amortized update and query cost of a dynamic cell-probe structure](amortized-cell-probe-costs.md)

## Proof depends on

- [Information transfer must carry the entropy of the interleaved updates](transfer-entropy-bound.md)
- [Each cell read is charged to at most one tree node](reads-charged-to-one-node.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
