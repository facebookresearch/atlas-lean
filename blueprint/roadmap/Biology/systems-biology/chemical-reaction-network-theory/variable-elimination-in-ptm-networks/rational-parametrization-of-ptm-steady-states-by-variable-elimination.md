# Rational parametrization of PTM steady states by variable elimination

**Setting.** A post-translational modification (PTM) system with mass-action kinetics has *substrates* $\mathcal S = \{S_1,\dots,S_N\}$ (modification states of proteins and the enzymes acting on them) and *intermediate complexes* $\mathcal Y = \{Y_1,\dots,Y_P\}$. Every reaction either joins two substrates into an intermediate ($S_i + S_j \to Y_k$), converts intermediates into each other, or releases substrates from an intermediate ($Y_k \to S_i + S_j$); substrates may also interconvert directly. Write $\mathcal K$ for the rate constants and call a rational function *S-positive* if it is a ratio of polynomials with positive coefficients. Conservation laws fix total amounts $\bar S_l$.

**Theorem.**
1. *(Intermediates.)* $\dot Y_k = 0$ for all $k$ if and only if

$$Y_k = \sum_{i \le j}\mu^k_{i,j}\,S_iS_j$$

with each $\mu^k_{i,j} \in \mathbb R(\mathcal K)$ zero or S-positive; when the intermediate graph is strongly connected, $\mu^k_{i,j} \ne 0$ exactly when $S_i + S_j$ ultimately reacts to $Y_k$.
2. *(Substrates.)* Suppose there is a *cut* $\mathcal S_\alpha \subseteq \mathcal S$, a set of substrates whose steady-state equations, after eliminating intermediates, are linear in $\mathcal S_\alpha$ with coefficients depending on the remaining substrates $\mathcal S_\alpha^c$, and that each connected component of the associated graph has a rooted spanning tree. Then at steady state every $S_j \in \mathcal S_\alpha$ is a zero or S-positive rational function of $\mathcal S_\alpha^c$, and the non-negative steady states with prescribed total amounts and positive values on $\mathcal S_\alpha^c$ are in one-to-one correspondence with the positive solutions of a reduced polynomial system in the variables $\mathcal S_\alpha^c$ alone.
3. If the intermediate graph and, for every substrate, some cut graph containing it are strongly connected, then no steady state has a vanishing substrate or intermediate concentration.

## Expansion

For fixed substrate concentrations the intermediates enter the dynamics linearly, so their steady-state equations form a linear system governed by a graph Laplacian; the matrix-tree theorem expresses the solution as sums over spanning trees, hence with positive coefficients. The same argument applied to a cut of substrates, whose equations are linear in the cut variables, eliminates them as well. What remains is a small polynomial system in a few core substrates, which is how multistationarity and the number of steady states of multisite phosphorylation, kinase cascades and two-component systems can be analyzed by hand.

## Sources

- Elisenda Feliu and Carsten Wiuf, "Variable elimination in post-translational modification reaction networks with mass-action kinetics", Journal of Mathematical Biology 66 (2012), 281–310, <https://doi.org/10.1007/s00285-012-0510-4>; numbering as in arXiv:1107.3531: Proposition 3.1, Proposition 3.9, Theorem 3.10 and Corollary 3.11.
