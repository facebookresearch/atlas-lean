# Pătraşcu–Demaine tradeoff for dynamic partial sums

For dynamic partial sums over $\mathbb{Z}/2^{\delta}\mathbb{Z}$ with $\delta = w = \Theta(\lg n)$, every cell-probe structure, possibly Las Vegas randomized, with amortized expected costs $t_u, t_q$ satisfies $t_q \lg(t_u/t_q) = \Omega(\lg n)$ and $t_u \lg(t_q/t_u) = \Omega(\lg n)$. In particular $\max\{t_u, t_q\} = \Omega(\lg n)$, which is matched by balanced aggregation trees and breaks the $\Omega(\lg n/\lg\lg n)$ barrier of the chronogram method for problems with $\Theta(\lg n)$-bit answers.

## Proof sketch

By the entropy lemma with $\delta = w$, a node at depth $d$ whose intervals contain $k = \Theta(m/2^{d})$ updates and queries has $\mathbb{E}|\mathrm{IT}(v)| = \Omega(k)$. Summing over the $\Theta(\lg n)$ levels and charging each read to one node gives $\Omega(m \lg n)$ total probes, so $\max(t_u,t_q) = \Omega(\lg n)$. For the tradeoff, the hard instance consists of blocks of $t_u + t_q$ operations, each with $t_q$ updates and $t_u$ queries, so updates and queries cost the same per block, and the analysis uses a tree of branching factor $B = 2\max\{t_u/t_q, t_q/t_u\}$. Each block then costs $\Omega(\max\{t_u, t_q\}\log_B n)$ in expectation and at most $2 t_u t_q$, which rearranges to the two branches.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Amortized update and query cost of a dynamic cell-probe structure](amortized-cell-probe-costs.md)

## Proof depends on

- [Information transfer must carry the entropy of the interleaved updates](transfer-entropy-bound.md)
- [Each cell read is charged to at most one tree node](reads-charged-to-one-node.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
