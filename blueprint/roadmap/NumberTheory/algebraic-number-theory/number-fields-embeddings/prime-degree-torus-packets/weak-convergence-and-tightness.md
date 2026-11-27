# Weak convergence and tightness of complete prime-degree torus packets

Fix a prime $n\ge5$. For each natural index $i$, take a totally real degree-$n$ number field
$K_i$, a full $\mathbb Z$-lattice $M_i$ spanning $K_i$ over $\mathbb Q$, and an ordering $\sigma_i$ of
all its real embeddings. If the multiplier discriminants of $M_i$ tend to $+\infty$, then there is
a right-$\mathrm{SL}_n(\mathbb R)$-invariant Haar probability $\nu$ on $X_n$ such that each complete
volume-weighted packet measure $\mu_i$ is a probability and, for every bounded continuous
$f:X_n\to\mathbb R$, $\int f\,d\mu_i\to\int f\,d\nu$. In addition the full family
$\{\mu_i:i\in\mathbb N\}$ is tight. The fields and finite local lattice types may both vary.

## Depends on

- [Complete packet measure and multiplier discriminant](complete-packet-measure.md)

## Expansion

Separate tightness (no escape of mass) from identifying the weak limit using the prime-degree entropy/discriminant estimates and invariant-measure rigidity. Establish the estimates for complete packets of arbitrary local type rather than just maximal-order packets.

## Sources

- [DukePrimeDegree.lean — `prime_degree_packet_measure_equidistribution_unconditional`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DukePrimeDegree.lean#L198-L212)
