# Some computable map of the circle has no computable invariant probability measure

There is a computable map of the circle none of whose invariant probability measures is computable, although every continuous map of a compact space has invariant measures; on the interval this cannot happen.

Let $S = \mathbb{R}/\mathbb{Z}$ be the unit circle with its standard computable metric structure. A map $T\colon S \to S$ is *computable* if an algorithm with an oracle giving approximations of $x$ outputs approximations of $T(x)$ to any requested precision. A Borel probability measure $\mu$ on $S$ is *computable* if the numbers $\int f \, d\mu$ can be computed uniformly to any precision for $f$ in a fixed countable family of test functions; equivalently, $\mu$ is a computable point of the space of probability measures with the weak topology. A measure is *invariant* if $\mu(T^{-1}A) = \mu(A)$ for every Borel set $A$. A set $K$ is *recursively compact* if it is compact and the finite covers of $K$ by rational balls can be enumerated.

**Theorem (Galatolo–Hoyrup–Rojas).** There is a computable map $T\colon S \to S$ of the unit circle that has no computable invariant probability measure (Proposition 5.1.2 of the source).

By contrast, the source notes that every computable map of the interval $[0, 1]$ has some computable invariant measure, so no such example exists on the interval. The same source gives a computable dynamical system with a physical (SRB) measure that is not computable.

## Depends on

- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

There is a nonempty recursively compact set $K \subset (0, 1)$ that contains no computable point (Proposition 2.6.2 of the source, a classical fact of computable analysis). Its complement $U = (0,1) \setminus K$ is an effectively open set, a computable union of intervals $(a_i, b_i)$. On each interval one places a computable bump that pushes points to the right inside $(a_i, b_i)$ and fixes the endpoints, and these bumps are summed with weights $2^{-i}$, together with a term that moves the ends of $[0,1]$. The result is a computable non-decreasing map $T\colon [0,1] \to \mathbb{R}$ with $T(1) = T(0) + 1$, so it descends to the circle, and with $T(x) > x$ exactly for $x \notin K$. Each interval $(a_i, b_i)$ is wandering, since the orbits of its endpoints converge to a non-computable point, so by Poincaré recurrence every invariant probability measure gives no mass to it, and its support lies in $K$. But the support of a computable probability measure always contains computable points (a proposition of the source), and $K$ has none. The existence of recursively compact sets without computable points is a prerequisite still to be added.

## Sources

- S. Galatolo, M. Hoyrup and C. Rojas, "Dynamics and abstract computability: computing invariant measures", Discrete and Continuous Dynamical Systems 31 (2011), no. 1, 193–212, https://doi.org/10.3934/dcds.2011.29.193; read in arXiv:0903.2385v2 (Proposition 2.6.2, Proposition 5.1.2 and the construction before it in Section 5 of arXiv:0903.2385v2; that version numbers each kind of statement within its subsection, and the numbers agree with the rendered copy).
