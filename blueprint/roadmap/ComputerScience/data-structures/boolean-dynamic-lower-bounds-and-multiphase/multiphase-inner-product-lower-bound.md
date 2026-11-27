# Ko's $\Omega((\log n / \log\log n)^2)$ lower bound for the multiphase problem

Let $f$ be inner product over $\mathbb{F}_2$ and let $k = n^{1 + \Omega(1)}$. Every cell-probe structure for the multiphase problem for $f$ with $w$-bit cells, $w = (\log n)^{O(1)}$, and update time $t_u = n^{o(1)}$ satisfies $t_{tot} \ge \Omega\!\left(\left(\frac{\log n}{\log(t_u w)}\right)^{2}\right)$; in particular $\max\{t_u, t_{tot}\} \ge \Omega\big((\log n / \log\log n)^2\big)$ (Theorem 1.1). The same holds for every function $f$ that is hard in the sense of Ko's Definition B.1, small discrepancy under product distributions with large min-entropy (Theorem B.3). Some bound on $w$ is needed: with $w \ge n$ each vector fits in one cell.

## Proof sketch

Ko introduces a $2.5$-round *multiphase communication game* that augments the usual one-way simulation of a data structure with a verification round in which Bob checks that Alice's claimed simulation of the query's probes is consistent with the actual memory. Verification removes the need for the peak-to-average machinery that limited earlier one-way arguments to $\lg^{1.5} n$. The bits of $y$ are split into $\ell = \Theta(\log n/\log(t_u w))$ geometrically shrinking epochs (Fredman–Saks chronogram), and a simulation theorem converts the small discrepancy of inner product into the bound that a random query probes $\Omega(\log n/\log(t_u w))$ cells last written in some epoch; summing over the epochs gives the square.

## Depends on

- [Pătraşcu's multiphase problem](multiphase-problem.md)
- [Amortized update and query cost of a dynamic cell-probe structure](../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)

## Proof depends on

- [Distributional communication complexity](../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/dist-complexity.md)

## Sources

- Young Kun Ko, "An Omega((log n / log log n)^2) Cell-Probe Lower Bound for Dynamic Boolean Data Structures", FOCS (2026), arXiv:2603.25914.
