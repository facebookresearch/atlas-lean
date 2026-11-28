# Sum of the ℓ¹ norms of the reaction vectors

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and finite reaction set $\rho$. The sum of the [ℓ¹ norms](l1-norm.md) of its
[reaction vectors](reaction-vector.md) $\zeta_r$ is

$$Z = \sum_{r \in \rho} \|\zeta_r\|_1 =
\sum_{r \in \rho} \sum_{i \in S} \left|\mathrm{prod}(r)_i - \mathrm{src}(r)_i\right|.$$

It enters the constants of [Kurtz's pathwise estimate](deviation-le.md).
