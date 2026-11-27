# Goemans-Williamson rounding for MAX-DICUT

Let $v_0, \dots, v_n$ be $\varepsilon$-optimal unit vectors for the MAX-DICUT relaxation (which has an optimum, attained by a finite family). Random-hyperplane rounding with respect to $v_0$ produces a directed cut of expected weight at least $\beta_{GW}(Z_{\mathrm{SDP}} - \varepsilon)$, hence at least $\beta_{GW}$ times the weight of every directed cut minus $\beta_{GW}\varepsilon$, with $\beta_{GW} > 0.79607$. If the digraph is **balanced** (every vertex has equal in- and out-weight), then every dicut has half the weight of the underlying undirected cut, and MAX-CUT rounding achieves the ratio $\alpha_{GW} > 0.87856$.

## Proof sketch

For a triple of unit vectors the probability that the hyperplane puts $v_0, v_i$ on one side and $v_j$ on the other is $\frac{1}{2\pi}(\theta_{0j} + \theta_{ij} - \theta_{0i})$; under the triangle constraints this is at least $\beta_{GW}$ times the SDP term.

## Depends on

- [The semidefinite relaxation of MAX-DICUT and the constant beta](max-dicut-semidefinite-relaxation.md)

## Proof depends on

- [Goemans–Williamson Lemma 3.2: probability that a random hyperplane separates two unit vectors](../goemans-williamson-max-cut-algorithm/measure-real-sign-ne.md)
- [Goemans-Williamson rounding for MAX-2SAT](goemans-williamson-max-two-sat.md)

## Sources

- M. X. Goemans and D. P. Williamson, "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming", Journal of the ACM 42(6), 1995.
