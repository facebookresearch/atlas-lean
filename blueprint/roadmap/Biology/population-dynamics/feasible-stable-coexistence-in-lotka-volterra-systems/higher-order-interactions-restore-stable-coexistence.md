# Higher-order interactions restore stable coexistence

**Higher-order Lotka-Volterra systems.** Allow interactions among several species at once:

$$\dot x_i=x_i\Big(r_i+\sum_jS^1_{ij}x_j+\sum_{j,k}S^2_{ijk}x_jx_k+\dots+\sum_{j_1,\dots,j_{d-1}}S^{d-1}_{ij_1\cdots j_{d-1}}x_{j_1}\cdots x_{j_{d-1}}\Big).$$

**Theorem (stabilization).** For any $n\ge1$ and **arbitrary** growth rates $r\in\mathbb R^n$ and pairwise coefficients $S^1\in\mathbb R^{n\times n}$, there are third- and fourth-order tensors $S^2,S^3$ such that the resulting system has a feasible asymptotically stable equilibrium at $\mathbf 1=(1,\dots,1)$. Hence every pairwise sign obstruction ("impossible ecology") disappears once higher-order interactions are allowed.

**Replicator correspondence.** Hofbauer's map between replicator dynamics on the simplex $\Delta_n$ and Lotka-Volterra dynamics on $\mathbb R^n_{\ge0}$ extends to degree $d$: a payoff tensor $A$ of a symmetric $d$-player game with $n+1$ strategies maps to coefficients $(r,S^1,\dots,S^{d-1})$, orbits correspond under the diffeomorphism $\Phi$, adding a payoff term independent of the focal strategy leaves the replicator field unchanged, and each class has a canonical representative with vanishing last row slice. Interior equilibria of the higher-order LV system correspond to totally mixed symmetric Nash equilibria of the game.

**Counting and robustness.** If the equilibrium equations have finitely many solutions in $(\mathbb C^*)^n$, there are at most $(d-1)^n$ feasible equilibria, and the bound is attained by real feasible equilibria for generic systems with full support. For squarefree interactions of order $k=d-1<n$, the bound improves to $\sum_{\ell=0}^k(-1)^\ell\binom n\ell(k-\ell)^n$. A feasible equilibrium with nonsingular Jacobian gives a **payoff-robust** totally mixed Nash equilibrium: every small, possibly asymmetric, perturbation of the game has a totally mixed equilibrium nearby. In particular any pairwise LV community can be embedded in a symmetric four-player game whose uniform profile is a payoff-robust totally mixed symmetric Nash equilibrium.

**ESS obstruction.** Every impossible ecology determines a non-empty open class of symmetric two-player games with no totally mixed evolutionarily stable strategy.

## Depends on

- [Impossible ecologies for generalized Lotka-Volterra systems](impossible-ecologies-for-generalized-lotka-volterra-systems.md)
- [Replicator and Lotka-Volterra equivalence](../replicator-and-lotka-volterra-equivalence/README.md)

## Expansion

The stabilization proof uses polynomials in $T(x)=\sum x_i$ with only degree-2 and degree-3 terms, such as $\phi_0=3(T/n)^2-2(T/n)^3$ with $\phi_0(\mathbf 1)=1$, $\nabla\phi_0(\mathbf 1)=0$, and $\phi_j=Tx_j/n-2(T/n)^2+(T/n)^3$ vanishing at $\mathbf 1$ with controlled gradient. Combining them cancels the prescribed linear part at $\mathbf 1$ and replaces it with a chosen negative-definite Jacobian, without touching $r$ and $S^1$. The equilibrium count is a Bézout-Bernstein bound for the polynomial system $G=0$ of degree $d-1$, with a sharper mixed-volume count under squarefree support. Payoff-robustness follows from the implicit function theorem applied to the equilibrium equations of the perturbed game. A totally mixed ESS of a two-player game would give a feasible stable equilibrium of the associated LV system with the same sign pattern, which impossibility rules out on an open set of games.

## Sources

- T. Ö. Çelik, V. A. Isoldi, I. Portakal, G. Zucal, "Stable coexistence in ecologies and games", arXiv:2609.09286 (2026), Section 4 (Theorems 4.1-4.4, Propositions 4-7, Definitions 1-4, Corollaries 2-3) and Section 4.3, <https://doi.org/10.48550/arXiv.2609.09286>.
