# Global attractor conjecture for single linkage class networks

**Setting.** A chemical reaction network has species $S_1,\dots,S_N$, complexes $y\in\mathbb Z_{\ge0}^N$ and reactions $y_k\to y_k'$; its *linkage classes* are the connected components of the reaction graph on complexes, and it is *weakly reversible* if each linkage class is strongly connected. Under mass-action kinetics with rate constants $\kappa_k>0$,

$$\dot x(t)=\sum_k\kappa_k\,x(t)^{y_k}\,(y_k'-y_k),\qquad x^{y}=\prod_ix_i^{y_i},$$

and trajectories stay in the positive stoichiometric compatibility class $(x_0+S)\cap\mathbb R^N_{>0}$, $S=\mathrm{span}\{y_k'-y_k\}$. An equilibrium $c$ is *complex-balanced* if for every complex $y$, $\sum_{k:y_k=y}\kappa_kc^{y_k}=\sum_{k:y_k'=y}\kappa_kc^{y_k}$; Horn and Jackson showed that then every positive compatibility class contains exactly one positive equilibrium, which is complex-balanced and locally asymptotically stable.

**Theorem (persistence).** Let the network be weakly reversible with a single linkage class, under mass-action kinetics, or more generally *bounded* mass-action kinetics $R_k(x,t)=\kappa_k(t)x^{y_k}$ with $\eta<\kappa_k(t)<1/\eta$. If a trajectory $\phi(t,x_0)$ with $x_0\in\mathbb R^N_{>0}$ is bounded and its $\omega$-limit set lies either entirely in $\partial\mathbb R^N_{\ge0}$ or entirely in $\mathbb R^N_{>0}$, then $\omega(\phi(\cdot,x_0))\cap\partial\mathbb R^N_{\ge0}=\emptyset$, i.e. $\liminf_{t\to\infty}\phi_i(t,x_0)>0$ for all $i$.

**Corollary (global attractor conjecture, one linkage class).** For a complex-balanced mass-action system whose reaction graph has one linkage class, the complex-balanced equilibrium in the interior of a positive compatibility class attracts every trajectory starting in that class.

## Depends on

- [Complex-balanced concentrations](../../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Horn–Jackson: one equilibrium per compatibility class](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-is-complex.md)

## Expansion

For complex-balanced systems the pseudo-Helmholtz free energy $\sum_ix_i(\log(x_i/c_i)-1)$ is a Lyapunov function, so trajectories are bounded and their $\omega$-limit sets consist of equilibria; the only obstruction to global convergence is an $\omega$-limit point on the boundary. Suppose a trajectory approaches a boundary point $z$. Along a subsequence, the monomials $x_n^{y}$ of the complexes can be partitioned into *tiers* of comparable growth. A key lemma then produces a non-negative conservation relation $w$, supported exactly on the species vanishing at $z$, that is constant across complexes in the same tier. Projecting the dynamics onto the vanishing species gives a lower-dimensional (reduced) network that is again weakly reversible with one linkage class, and the dominant tier pushes mass back into the interior, contradicting $x_n\to z$. Persistence gives global attraction because the Lyapunov function leaves only the unique interior equilibrium as a possible limit.

## Sources

- David F. Anderson, "A Proof of the Global Attractor Conjecture in the Single Linkage Class Case", SIAM Journal on Applied Mathematics 71 (2011), 1487–1508, <https://doi.org/10.1137/11082631x>; numbering as in arXiv:1101.0761: Section 2.1 (complex-balanced equilibria), Section 3 (projected dynamics and reduced networks), Section 4.1 (partitions along a sequence and the conservation-relation theorem) and Section 4.2 (main persistence theorem and its corollaries).
