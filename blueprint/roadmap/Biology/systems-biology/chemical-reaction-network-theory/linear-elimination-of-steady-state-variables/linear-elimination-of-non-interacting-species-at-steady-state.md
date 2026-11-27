# Linear elimination of non-interacting species at steady state

**Setting.** For a chemical reaction network with mass-action kinetics, steady states solve polynomial equations $\dot c = 0$ in the species concentrations. A subset $\mathcal S_\alpha$ of species is *non-interacting* if no two of its species appear together in a complex and every stoichiometric coefficient of a species in $\mathcal S_\alpha$ is $0$ or $1$ (typical of enzymes and intermediate complexes). Then the steady-state equations for $c_i \in C_\alpha$ are linear in the variables $C_\alpha$, with coefficients that are polynomials in the rate constants and the remaining concentrations $C^c_\alpha$, and they are encoded by a labelled digraph $G_{\mathcal S_\alpha}$ on $\mathcal S_\alpha$ (edge $S_i \to S_j$ when a reaction converts $S_i$ into $S_j$). $\mathcal S_\alpha$ is a *cut* if no reaction creates or destroys $\mathcal S_\alpha$-molecules from outside, in which case $\sum_{S_i \in \mathcal S_\alpha} S_i$ is a P-semiflow (a conserved total, minimal iff $G_{\mathcal S_\alpha}$ is connected). Otherwise one adds an auxiliary vertex $*$ representing inflow and outflow, giving $\widehat G_{\mathcal S_\alpha}$. A polynomial or rational function is *S-positive* if it is a ratio of nonzero polynomials with nonnegative coefficients.

**Theorem.**
1. *(Cut case.)* If $\mathcal S_\alpha$ is a cut, $G_{\mathcal S_\alpha}$ is connected, and $G_{\mathcal S_\alpha}$ has a spanning tree rooted at $S_i$, then the steady-state equations for $C_\alpha$ hold iff each $c_j \in C_\alpha$ equals $c_i$ times a zero-or-S-positive rational function of $C^c_\alpha$ and the rate constants; combined with the conservation law, every $c_j$ is determined by the conserved total.
2. *(Non-cut case.)* If $\mathcal S_\alpha$ is non-interacting, not a cut, and $\widehat G_{\mathcal S_\alpha}$ has a spanning tree rooted at $*$, then the equations hold iff $c_i = \varphi_i(C^c_\alpha)$ for zero-or-S-positive rational functions $\varphi_i$ with coefficients in the rate constants, and there is no conservation law among $C_\alpha$.

Positive steady states of the full network therefore correspond to positive solutions of a smaller polynomial system in the core variables $C^c_\alpha$.

## Expansion

The linear system has the form $A x + z = 0$ with nonnegative off-diagonal entries of $A$, nonpositive column sums and nonnegative $z$, i.e. it is the balance equation of a Laplacian-type matrix of $G_{\mathcal S_\alpha}$ (or $\widehat G$). By the matrix-tree theorem, its solution is a ratio of sums over rooted spanning trees of products of edge labels; all labels are monomials in rate constants and core concentrations with positive coefficients, which yields S-positivity, and existence of a rooted spanning tree is equivalent to the matrix having maximal rank. This makes elimination of enzymes and intermediates in signalling cascades (e.g. multisite phosphorylation) systematic.

## Sources

- Elisenda Feliu and Carsten Wiuf, "Variable Elimination in Chemical Reaction Networks with Mass-Action Kinetics", SIAM Journal on Applied Mathematics 72 (2012), 959–981, <https://doi.org/10.1137/110847305>; numbering as in arXiv:1109.1505: Proposition 7.2, Corollaries 7.3–7.4 and Propositions 8.2, 8.4, 8.5 and 8.6.
