# Permanence of strongly endotactic networks

**Definitions.** Let $(\mathcal S,\mathcal C,\mathcal R)$ be a reaction network with reaction vectors $y'-y$ and stoichiometric subspace $H$. For $w\in\mathbb R^{\mathcal S}$, order complexes by $\langle w,\cdot\rangle$; the $w$-essential reactions are those with $\langle w,y'-y\rangle\neq0$, and the $w$-support is the set of $\langle w,\cdot\rangle$-maximal reactants among them. The network is *endotactic* if for every $w$, each $w$-essential reaction whose reactant lies in the $w$-support satisfies $\langle w,y'-y\rangle<0$ (reactions from extreme reactants point back into the reactant polytope). It is *strongly endotactic* if, moreover, for every $w$ not orthogonal to $H$ there is a reaction $y\to y'$ with $\langle w,y'-y\rangle<0$ whose reactant $y$ is $\langle w,\cdot\rangle$-maximal among **all** reactants. A *confined reaction system* fixes a positive compatibility class $(x_0+H)\cap\mathbb R^{\mathcal S}_{\ge0}$ and a compact positive interval $\kappa(r)=[a_r,b_r]$ for each rate; its mass-action differential inclusion allows $\dot x\in\{\sum_rk_rx^{y_r}(y_r'-y_r):k_r\in\kappa(r)\}$. It is *permanent* if there is a compact subset of the open positive compatibility class that every trajectory eventually enters and never leaves.

**Theorem.** Every strongly endotactic reaction network is permanent (for every choice of compatibility class and rate intervals). Consequently the global attractor conjecture holds for strongly endotactic complex-balanced systems: every trajectory with positive initial condition converges to the unique positive equilibrium of its compatibility class. Weakly reversible networks with a single linkage class, and more generally weakly reversible networks whose linkage classes all have the same stoichiometric subspace as the whole network, are strongly endotactic.

## Depends on

- [Complex-balanced concentrations](../../../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Horn–Jackson: one equilibrium per compatibility class](../../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-is-complex.md)
- [Global attractor conjecture for single linkage class networks](global-attractor-conjecture-for-single-linkage-class-networks.md)
- [Stoichiometric subspace](../../../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md)
- [Weakly reversible reaction network](../../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Proof depends on

- [The pseudo-Helmholtz function does not increase along solutions](../../../complex-balancing-and-the-deficiency-zero-theore/antitone-on-pseudo-helmholtz.md)
- [Equality in the Horn–Jackson inequality](../../../complex-balancing-and-the-deficiency-zero-theore/helmholtz-rate-eq-zero-iff.md)
- [Birch's theorem, existence](../../../complex-balancing-and-the-deficiency-zero-theore/exists-pos-sub-mem-log-orthogonal.md)
- [Birch's theorem, uniqueness](../../../complex-balancing-and-the-deficiency-zero-theore/eq-of-sub-mem-log-orthogonal.md)

## Expansion

The argument is combinatorial-geometric. Far from the positive interior along a *toric ray* $\alpha*\theta^w$, the monomial of the $\langle w,\cdot\rangle$-maximal reactant dominates the vector field, and strong endotacticity guarantees that some dominating reaction pushes in the direction $-w$, back towards the interior; the Lyapunov-type function $g_\alpha(x)=\sum_ix_i\log(x_i/\alpha_i)-x_i$ decreases along such rays. Gluing these local repulsions uses a projection argument, which analyses the system near a boundary face via a lower-dimensional projected network that inherits strong endotacticity, together with an extension of Birch's theorem (the compatibility class meets the toric pencil $\alpha*\theta^{H^\perp}$ in exactly one interior point). Permanence rules out boundary $\omega$-limit points, and for complex-balanced systems the free-energy Lyapunov function then forces convergence. The statement extends the single linkage class case and covers power-law and time-varying rates through the differential-inclusion setting; the full extended permanence conjecture for all endotactic networks remains open.

## Sources

- Manoj Gopalkrishnan, Ezra Miller and Anne Shiu, "A Geometric Approach to the Global Attractor Conjecture", SIAM Journal on Applied Dynamical Systems 13 (2014), 758–797, <https://doi.org/10.1137/130928170>; numbering as in arXiv:1305.5303: Theorems 1.1–1.3, Definitions 3.9 and 3.14, Corollaries 3.19 and 3.20, Section 4 (persistence and permanence conjectures) and Section 5 (Birch's theorem and toric rays).
