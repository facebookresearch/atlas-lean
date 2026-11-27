# Bounded trajectories of weakly reversible single-linkage-class mass action systems

**Setting.** A mass action system $\{\mathscr{S},\mathscr{C},\mathscr{R},\mathscr{K}(t)\}$ with species $S_1,\dots,S_N$ evolves by

$$\dot\phi(t)=\sum_{y\to y'\in\mathscr{R}}\kappa_{y\to y'}(t)\,\phi(t)^{y}\,(y'-y),\qquad \phi(0)=x_0\in\mathbb{R}^N_{>0}.$$

It is *weakly reversible* if every reaction lies on a directed cycle of the reaction graph, has a *single linkage class* if the reaction graph is connected, and has *bounded kinetics* if there is $\eta>0$ with $\eta<\kappa_{y\to y'}(t)<1/\eta$ for all reactions and all $t$ (the non-autonomous case includes constant rates).

**Statements.**

1. *(Boundedness.)* For a single-linkage-class, weakly reversible, non-autonomous mass action system with bounded kinetics, $\limsup_{t\to\infty}|\phi(t,x_0)|<\infty$ for every $x_0\in\mathbb{R}^N_{>0}$.
2. *(Persistence upgrades to permanence.)* If moreover, on a positive stoichiometric compatibility class $P$, there is $\delta>0$ with $\liminf_t\phi_i(t,x_0)>\delta$ for all $i$ and all $x_0\in P$, then there is $\rho>0$ with $\rho<\liminf_t\phi_i(t,x_0)\le\limsup_t\phi_i(t,x_0)<1/\rho$ for all $i$ and $x_0\in P$.
3. *(Tier lemma.)* Let $x_n\in\mathbb{R}^N_{>0}$ be a partially monotonic sequence with some coordinate tending to $0$ or $\infty$, let $U$ and $V$ be the sets of coordinates tending to $0$ and to $\infty$, and partition the complexes into tiers $T_1,\dots,T_P$ by the asymptotic size of $x_n^{y}$ (complexes in the same tier are comparable within a constant factor, higher tiers dominate lower ones). Then there is a conservation relation $w\in\mathbb{R}^N$ that respects $(U,V,\{T_i\})$: the positive support of $w$ is exactly $U$, its negative support is exactly $V$, and $w\cdot(y-y')=0$ whenever $y,y'$ lie in the same tier (proved via a Stiemke-type alternative).

## Depends on

- [Weak reversibility is equivalent to strongly connected linkage classes](../../complex-balancing-and-the-deficiency-zero-theore/is-weakly-reversible-iff-reachable.md)
- [Weakly reversible reaction network](../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Expansion

Suppose a trajectory were unbounded; extract times along which $|\phi|\to\infty$ and a partially monotonic subsequence, and sort complexes into tiers by the size of their monomials. Along such a sequence the dominant term of $\dot\phi$ comes from reactions whose source lies in the top tier. Weak reversibility and a single linkage class force reactions leaving the top tier, and the tier lemma gives a linear function $w\cdot\phi$ that these dominant reactions decrease while being large exactly when $\phi$ diverges. Hence $w\cdot\phi$ must decrease whenever $\phi$ is far out, contradicting unboundedness. Bounded kinetics keeps the rate constants from changing tier orderings. The permanence corollary follows by compactness once both persistence and boundedness hold uniformly on $P$.

## Sources

- David F. Anderson, "Boundedness of trajectories for weakly reversible, single linkage class reaction systems", Journal of Mathematical Chemistry 49 (2011), 2275–2290, <https://doi.org/10.1007/s10910-011-9886-4>; numbering as in arXiv:1104.4992: Corollary 3.5, Theorem 3.9, Theorem 3.12 and Corollary 3.15.
