# Minimal-deficiency weakly reversible linearly conjugate networks

**Definitions.** For a mass-action network with $m$ stoichiometrically distinct complexes, $\ell$ linkage classes and stoichiometric subspace of dimension $s$, the **deficiency** is $\delta = m - \ell - s$. Two networks $\mathcal N, \mathcal N'$ with flows $\Phi, \Psi$ are **linearly conjugate** if there is a bijective linear map $h : \mathbb R^n_{>0} \to \mathbb R^n_{>0}$ (necessarily a positive rescaling and reindexing of coordinates) with $h(\Phi(x_0, t)) = \Psi(h(x_0), t)$ for all $x_0$ and $t$; dynamical equivalence (alternative realizations of the same ODE) is the case $h = \mathrm{id}$.

**Theorem (kernel characterization of weak reversibility).** Let $A_k$ be the kinetics (weighted Laplacian) matrix of a reaction graph with linkage-class supports $\Lambda_1, \dots, \Lambda_\ell$. The graph is weakly reversible if and only if $\ker A_k$ has a basis $b^{(1)}, \dots, b^{(\ell)}$ with $b^{(i)}_j > 0$ for $j \in \Lambda_i$ and $b^{(i)}_j = 0$ otherwise.

**Result (mixed-integer linear program).** Given a mass-action system and a finite set of candidate complexes, the linear constraints describing all linearly conjugate realizations, the kernel characterization of weak reversibility, and integer variables counting used complexes and linkage classes can be combined into a mixed-integer linear program whose optimum is a weakly reversible linearly conjugate network of **minimal deficiency** (when one exists). Since the Deficiency Zero and Deficiency One theorems transfer through linear conjugacy, a minimal-deficiency realization yields the strongest available conclusions on the number and stability of positive equilibria of the original system.

## Depends on

- [Weak reversibility is equivalent to strongly connected linkage classes](../../complex-balancing-and-the-deficiency-zero-theore/is-weakly-reversible-iff-reachable.md)
- [Deficiency-zero theorem, weakly reversible case](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium.md)

## Proof sketch

Linear conjugacy preserves the qualitative dynamics (equilibria, their stability, compatibility-class structure) up to a diagonal rescaling, so properties certified for any conjugate network hold for the original. The deficiency is linear in the numbers of complexes and linkage classes once $s$ is fixed by the dynamics, and the kernel characterization turns "weakly reversible" into linear sign constraints on a basis of $\ker A_k$; integer indicator variables then switch complexes and linkage classes on or off. Minimizing $m - \ell$ over the feasible set is a standard MILP, solvable for networks of practical size.

## Sources

- Matthew D. Johnston, David Siegel and Gábor Szederkényi, "Computing weakly reversible linearly conjugate chemical reaction networks with minimal deficiency", *Mathematical Biosciences* 241 (2013), 88–98, <https://doi.org/10.1016/j.mbs.2012.09.008>. Preprint version: arXiv:1203.5140 (2012), Definitions 2.1 and 2.3, Theorems 2.1–2.4 (Section 2), Theorem 3.1 and the mixed-integer linear programming procedure (Section 3), <https://doi.org/10.48550/arXiv.1203.5140>.
