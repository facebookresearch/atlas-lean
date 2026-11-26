# The complete volume-weighted torus packet measure

Fix $n=d+1$, a totally real number field $K$ of degree $n$, an ordered enumeration $\sigma$ of its
real embeddings and a full rank-$n$ $\mathbb Z$-lattice $M\subset K$ spanning $K$ over $\mathbb Q$; $M$ need not be contained in $\mathcal O_K$.
In $X_n=\mathrm{SL}_n(\mathbb Z)\backslash\mathrm{SL}_n(\mathbb R)$, associate to a lattice $M'$
the unimodular row lattice given by dividing the embedding matrix of an integral basis by
$|\det|^{1/n}$. Take every $M'$ whose $\mathbb Z_p$-span in $K\otimes\mathbb Q_p$ differs from
that of $M$ by multiplication by a unit of $K\otimes\mathbb Q_p$ at each prime $p$. Take the orbits
of their lattice points, allowing right translation by every diagonal sign matrix of determinant
one, and count each distinct orbit only once. The acting positive diagonal group is parametrized
by $(u_1,\ldots,u_d)\mapsto \operatorname{diag}(e^{u_1},\ldots,e^{u_d},e^{-\sum u_j})$.

For each orbit the volume is the additive covolume of the period subgroup of $\mathbb R^d$.
Push the Lebesgue restriction to a fundamental domain of that subgroup along the orbit map, and
normalize by the orbit volume. The complete packet measure is the sum of these orbital probability
measures weighted by their volumes, divided by the sum of the volumes. The multiplier discriminant
is $|\operatorname{disc} K|[\mathcal O_K:\mathcal O_M]^2$, with
$\mathcal O_M=\{a\in K:aM\subseteq M\}$, using the relative additive index.

## Expansion

Give the normalized lattice, right action and local homothety model a common interface and verify that the normalized-lattice choice, fundamental domain, and orbit representatives cannot change the measure. Prove existence of the fundamental domains and finite positive total weights so fallback values are never used on these packets.

## Sources

- [DukePrimeDegree.lean — `prime_degree_packet_measure_equidistribution_unconditional`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DukePrimeDegree.lean#L198-L212)
- [DukePrimeDegree.lean — `prime_degree_packet_measures_tendsto_haar_unconditional`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DukePrimeDegree.lean#L213-L228)
- [Source lattice, packet and convergence definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DukePrimeDegree.lean#L11-L185)
