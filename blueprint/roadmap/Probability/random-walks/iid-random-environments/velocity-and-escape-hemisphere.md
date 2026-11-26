# Positive-probability transience and the velocity hemisphere

Let $d\ge3$. Use the [annealed law from the origin in a fixed independent environment](nearest-neighbor-environment-law.md) with uniform ellipticity as defined there. For a direction $u$ let $A_u=\{\langle X_n,u\rangle\to+\infty\}$. If $P_\nu(A_\ell)>0$ for any nonzero $\ell$, there exists a nonzero $v$ with $\langle v,\ell\rangle>0$, $P_\nu(X_n/n\to v)=1$, and no other vector with that probability-one limit.

On the unit sphere, the set where $P_\nu(A_u)=1$ equals the set where $P_\nu(A_u)>0$ and both equal $\{u:\|u\|_2=1,\ \langle v,u\rangle>0\}$. Each unit $u$ with $\langle v,u\rangle\le0$ has $P_\nu(A_u)=0$, including the equator.

**Conventions.** Use the annealed path law, uniform ellipticity, and the projection escape events, with no unit-length restriction on the triggering direction $\ell$.

## Depends on

- [IID nearest-neighbor environments and the annealed path law](nearest-neighbor-environment-law.md)

## Proof depends on

- [Directional zero–one law](directional-zero-one.md)
- [Positive velocity from almost-sure directional transience](directional-transience-implies-ballisticity.md)

## Proof outline

Normalize only the initial nonzero direction for the ballisticity step. For $\langle v,u\rangle>0$, apply the almost-sure vector limit; for the other implication apply the zero–one and ballisticity results in direction $u$ and identify the two probability-one velocities. The latter step rules out escape in zero-projection directions; the vector limit alone does not.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VelocityHemisphere.lean#L85-L99)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/220.md)
- [Accompanying manuscript: Directional transience implies ballisticity](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf)
