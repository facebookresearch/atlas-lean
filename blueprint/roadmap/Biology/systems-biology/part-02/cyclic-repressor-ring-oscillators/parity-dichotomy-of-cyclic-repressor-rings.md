# Parity dichotomy of cyclic repressor rings

**Setting.** Consider the ring model of $n \ge 2$ genes in which each protein $P_{i-1}$ represses the next gene $G_i$ (indices modulo $n$), with mRNA $r_i$ and protein $p_i$ obeying

$$\dot r_i = -(a_i + \mu)\, r_i + \beta_i\, g\, h_i(p_{i-1}), \qquad \dot p_i = -(b_i + \mu)\, p_i + c_i\, r_i,$$

where all rate constants are positive and each repression function $h_i(p) = K_{i-1}^{\nu_i} / (K_{i-1}^{\nu_i} + p^{\nu_i})$ is strictly decreasing on $p > 0$.

**Species graph.** Ignoring self-loops, the signed species graph has the $2n$ edges $r_i \to p_i$ (sign $+$) and $p_{i-1} \to r_i$ (sign $-$). It is a single cycle, directed or undirected, with exactly $n$ negative edges, so its sign is $(-1)^n$.

**Statement.**

1. *Even rings are monotone.* If $n$ is even, the cycle has an even number of negative edges, the graph is balanced, and the system is monotone with respect to an orthant order. Its Jacobian is irreducible at every positive state and its solutions are bounded, so it is strongly monotone: it has no attracting periodic orbits, and almost every solution converges to the set of equilibria.
2. *Odd rings are negative feedback loops.* If $n$ is odd, the single loop is negative and the system is not monotone for any orthant order. For any graph containing a negative feedback loop there are systems with that graph that have stable periodic orbits.

## Expansion

For even $n$ the spin assignment $\sigma(r_i) = \sigma(p_i) = (-1)^i$ is consistent: each positive edge $r_i \to p_i$ joins equal spins and each negative edge $p_{i-1} \to r_i$ joins opposite spins, and the wrap-around edge $p_n \to r_1$ is consistent exactly because $n$ is even. Irreducibility holds because the cycle is strongly connected and each off-diagonal Jacobian entry ($c_i$ or $\beta_i g h_i'(p_{i-1})$) is nonzero for $p_{i-1} > 0$. Boundedness follows because each production term is bounded ($0 < h_i \le 1$) and each variable decays linearly. Hirsch's generic convergence theorem then rules out sustained oscillations, leaving multistability as the typical outcome.

For odd $n$ the statement does not assert that this particular ring oscillates. Whether it does is the subject of the oscillation criterion for cyclic repressor rings: by the source's "Model" paragraph, the odd ring has a unique equilibrium and its proteins oscillate when the Jacobian there has an eigenvalue in the open right half-plane, which by Eqs. (9)–(10) holds only in part of parameter space and fails, for example, for homogeneous rings with Hill coefficient $\nu \le 1$.

Cell-free experiments in a microfluidic reactor that emulates growth by periodic dilution confirm the dichotomy. A $4$-node ring of LacI, TetR, PhlF and SrpR on linear DNA settled into one of two stable steady states, selected by an initial pulse of the inducer IPTG or aTc, reached after an adjustment phase of $5$ to $10$ h, and stayed there until the experiment ended at $22$ h. New $3$-node and $5$-node rings oscillated over a broad range of dilution times, with $5$-node periods (up to $19$ h) longer than $3$-node periods (up to $8$ h). The prototyped $3$- and $5$-node oscillators transferred to *E. coli*, where period again tracked the doubling time, consistent with periods of negative feedback rings being set mainly by degradation and dilution rates.

## Depends on

- [Balanced species graphs and orthant monotonicity](../../part-01/monotone-systems-and-sign-consistency/balanced-species-graphs-and-orthant-monotonicity.md)

## Sources

- H. Niederholtmeyer, Z. Z. Sun, Y. Hori, E. Yeung, A. Verpoorte, R. M. Murray, S. J. Maerkl, "Rapid cell-free forward engineering of novel genetic ring oscillators", eLife 4 (2015) e09771, Results, section "Engineering novel negative feedback circuits" (odd versus even rings, Figure 3D to 3F), section "Transfer of cell-free prototyped 3- and 5-node oscillators to E. coli" (Figure 4), Discussion, and Materials and methods, section "Model" (Equation 6, the paragraph on the unique equilibrium and oscillations, and Equations 9 and 10), <https://doi.org/10.7554/eLife.09771>, PMCID PMC4714972.
- E. D. Sontag, "Monotone and near-monotone biochemical networks", Systems and Synthetic Biology 1 (2007) 59 to 87, sections "Spin assignments and consistency", "Dynamical behavior of monotone systems" and "Directed cycles" (balance criterion, generic convergence, and stable periodic orbits for graphs with a negative loop), <https://doi.org/10.1007/s11693-007-9005-9>, PMCID PMC2533521.
