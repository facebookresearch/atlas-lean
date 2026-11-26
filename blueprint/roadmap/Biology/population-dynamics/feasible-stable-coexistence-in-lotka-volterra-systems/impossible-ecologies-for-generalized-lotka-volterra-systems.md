# Impossible ecologies for generalized Lotka-Volterra systems

**Setting.** The generalized Lotka-Volterra (GLV) system $\dot x_i=x_i\big(a_i-\sum_jb_{ij}x_j\big)$, with self-limitation $b_{ii}>0$, has the ordered sign pattern $\operatorname{sign}(a,B)\in\{\pm\}^{n+n^2}$: $a_i>0$ for species that grow alone, and for $i\ne j$ the pair $(b_{ij},b_{ji})$ is competitive $(+,+)$, mutualistic $(-,-)$, or predator-prey ($b_{ij}<0<b_{ji}$, $i$ eats $j$). This signed graph is the **ecological network**. A network is **impossible** if no parameters with that sign pattern give a feasible ($x^*=B^{-1}a>0$) asymptotically stable equilibrium, i.e. one at which $J(x^*)=-\operatorname{diag}(x^*)B$ is Hurwitz.

**Tools.** A $Z$-matrix is a nonsingular M-matrix iff $M^{-1}\ge0$ iff all principal minors are positive, and Schur complements give $\det B=\det B_{QQ}\det(B/B_{QQ})$. A feasible equilibrium whose Jacobian has spectrum in the closed left half-plane can be made asymptotically stable by an arbitrarily small perturbation of $B$ that preserves the signs. So impossibility is a robust, open condition.

**Theorem (families of impossible ecologies).** For every number of species:
1. every network in **obligate mutualism** (all species mutualistic, none growing alone) is impossible;
2. every network of two competing mutualistic groups, at least one in obligate mutualism, is impossible;
3. for $n\ge4$, every network made of an odd number of disjoint obligate predator-prey cycles with competition between cycles is impossible, and it stays impossible after adding a self-growing species competing with everyone, or a self-growing super-predator;
4. a pair in obligate mutualism competing against an even number of such cycles is impossible.

**Theorem (four species).** Together with three explicitly analyzed asymmetric networks, this completes the classification of impossible ecologies with at most four species: exactly 11 four-species networks are impossible.

## Depends on

- [Lotka-Volterra predator-prey model](../lotka-volterra-predator-prey-model/README.md)

## Expansion

Feasibility and stability together force sign conditions on determinants: at a feasible stable equilibrium $\det(-\operatorname{diag}(x^*)B)$ has sign $(-1)^n$, so $\det B>0$, and Cramer's rule forces each $x^*_i=\det B_i/\det B$ to be positive, where $B_i$ replaces column $i$ by $a$. For obligate mutualism $B$ is a $Z$-matrix with $a<0$; stability makes it an M-matrix, so $B^{-1}\ge0$ and $x^*=B^{-1}a\le0$, which contradicts feasibility. Cycle families are handled by Schur complements: an odd number of predator-prey cycles makes a key principal minor or Schur complement negative, forcing $\det B<0$, incompatible with stability. The sign obstructions are specific to pairwise interactions: higher-order interactions can always restore coexistence.

## Sources

- T. Ö. Çelik, V. A. Isoldi, I. Portakal, G. Zucal, "Stable coexistence in ecologies and games", arXiv:2609.09286 (2026), Section 2 (GLV framework, Propositions 1-3) and Section 3 (Theorems 3.1-3.7, Corollary 1, Lemmas 1-3), <https://doi.org/10.48550/arXiv.2609.09286>.
