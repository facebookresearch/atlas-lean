# The Gaussian propeller partition bound and attainment

For positive integers $d,k$, let $\gamma_d=N(0,I_d)$ on Euclidean $\mathbb R^d$. For measurable sets $(A_i)_{i<k}$ such that $\gamma_d$-almost every point belongs to exactly one of them, put $b_i=\int_{A_i} x\,d\gamma_d(x)$, with no division by the measure of $A_i$. Then $\sum_{i<k}\|b_i\|_2^2\le 9/(8\pi)$.

If $d\ge2$ and $k\ge3$, equality is attained by the following partition: in the first two coordinates $(u,v)$, take the three closed sectors $|v|\le\sqrt3 u$, $v\ge0$ and $v\ge\sqrt3 u$, and $v\le0$ and $-v\ge\sqrt3 u$. Take their products with the remaining coordinates and set all other parts empty. Boundary rays overlap only on Gaussian-null sets. This is not a uniqueness claim and does not assert attainment in $d=1$ or with only two parts.

**Conventions.** Use the standard Gaussian measure on finite-dimensional Euclidean space, the almost-everywhere partition condition, and the Bochner first moments restricted to measurable sets.

## Depends on

- [First moments of Gaussian partitions](gaussian-partition-moment.md)

## Expansion

The sharp all-partitions upper bound needs a reduction to Gaussian partitions determined by centroid directions and a sharp bound on the resulting finite-dimensional optimization. The equality direction instead needs the Gaussian first moments of planar sectors.

Separate the dimension- and part-count-uniform upper bound from the two-dimensional construction. Establish integrability of the coordinate map; for a sector of opening $2\pi/3$, integrate the polar radial term and the cosine of the angle to obtain first moment magnitude $\sqrt{3/(8\pi)}$, and use product Gaussian symmetry to make the remaining coordinates zero. Verify the closed-sector boundary multiplicities only almost everywhere.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianPropeller.lean#L38-L40)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/096.md)
- [Accompanying manuscript: The Gaussian propeller bound in every dimension](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf)
