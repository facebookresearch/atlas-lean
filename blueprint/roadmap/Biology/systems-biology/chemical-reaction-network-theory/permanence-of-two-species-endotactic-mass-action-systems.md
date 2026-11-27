# Permanence of two-species endotactic mass-action systems

A reaction network is endotactic if for every direction $v$ the following holds (Definition 4.3 of the source): first discard the reactions $y \to y'$ orthogonal to $v$, that is, with $\langle v, y' - y\rangle = 0$; then every remaining reaction whose source complex is maximal in the direction $v$ among the sources of the remaining reactions satisfies $\langle v, y' - y\rangle < 0$. Discarding the orthogonal reactions first matters, since otherwise an extreme reaction tangential to $v$ could hide an outward-pointing reaction from the test. A $\kappa$-variable mass-action system (Definition 2.6 of the source) is a mass-action system whose rate constants are given by a piecewise differentiable $\kappa : [0, \infty) \to (\eta, 1/\eta)^{\mathcal R}$ for some $0 < \eta < 1$, where $\mathcal R$ is the set of reactions. Craciun, Nazarov and Pantea (2013, Theorem 6.4) prove that every two-species endotactic $\kappa$-variable mass-action system is permanent in the sense of their Definitions 2.9 and 2.10: for each stoichiometric compatibility class $S$ meeting the open positive orthant there is a compact set $K$ contained in the intersection of $S$ with the open positive orthant such that every trajectory starting in that intersection eventually enters $K$ and never leaves. The compact set is chosen for the compatibility class, before the trajectory, not separately for each initial condition. The same paper proves the global attractor conjecture for complex-balanced systems with three species (its Theorem 7.2); that result is a separate statement and is not claimed here.

## Depends on

- [Stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md)

## Expansion

1. Definitions: endotactic networks (with orthogonal reactions discarded before the extreme sources are found), $\kappa$-variable mass-action systems with a piecewise differentiable rate-constant function, and permanence with one compact set per compatibility class.
2. The construction of a family of invariant polygons $P(\alpha)$ in the positive quadrant, decreasing with $\alpha$, from the endotactic condition (the source's construction before Theorem 6.4).
3. The proof that trajectories enter and remain in a polygon, giving permanence.
4. The relation with the [extended permanence conjecture](../../../Biology/systems-biology/extended-permanence-conjecture.md).

## Sources

- G. Craciun, F. Nazarov and C. Pantea, Persistence and permanence of mass-action and power-law dynamical systems, SIAM J. Appl. Math. 73 (2013), 305–329, Theorem 6.4. <https://arxiv.org/abs/1010.3050>
