# Almost-sure directional transience implies ballisticity

Let $d\ge2$. Use the [annealed nearest-neighbor walk in an independently sampled fixed environment](nearest-neighbor-environment-law.md), with row law $\nu$ uniformly elliptic: for some $\kappa>0$ all $2d$ transition probabilities are at least $\kappa$, almost surely under $\nu$. Let $\ell\in\mathbb R^d$ have $\langle\ell,\ell\rangle=1$. If $\langle X_n,\ell\rangle\to+\infty$ almost surely under the annealed law from zero, there exists a deterministic $v\in\mathbb R^d$ with $\langle v,\ell\rangle>0$ such that $X_n/n\to v$ almost surely.

**Conventions.** Use the fixed-environment trajectory law, a common ellipticity constant, and convergence of the rescaled positions in the finite product topology.

## Depends on

- [IID nearest-neighbor environments and the annealed path law](nearest-neighbor-environment-law.md)

## Expansion

Directional regeneration with control of the expected regeneration time, and the regeneration law of large numbers. Almost-sure escape by itself does not give a strictly positive velocity.

Build the regeneration blocks in a fixed environment, identify their annealed law and obtain finite expected time with the source hypotheses. Separate the resulting law of large numbers from the proof of strictly positive longitudinal speed. Keep $d=2$ in scope and do not use a $d\ge3$ zero–one statement to eliminate it.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectionalBallisticity.lean#L95-L97)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/220.md)
- [Accompanying manuscript: Directional transience implies ballisticity](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf)
