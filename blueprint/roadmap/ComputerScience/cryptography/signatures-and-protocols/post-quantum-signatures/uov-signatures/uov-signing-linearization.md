# UOV signing reduces to solving a linear system

For a UOV public map with oil subspace spanned by $\binom{\mathbf{O}}{I_o}$ and any vinegar vector $u \in \mathbb{F}^v$, define $S_i = (P_i^{(1)} + P_i^{(1)\mathsf T})\mathbf{O} + P_i^{(2)}$. Then for every $x \in \mathbb{F}^o$,

$$
p_i\!\left(\binom{u}{0} + \binom{\mathbf{O}}{I_o} x\right) = u^{\mathsf T} P_i^{(1)} u + (u^{\mathsf T} S_i)\, x ,
$$

in every characteristic. Hence $\mathcal{P}(\binom{u}{0} + \binom{\mathbf{O}}{I}x) = y + L x$ is affine in $x$, and a preimage of a target $t$ is found by choosing random vinegar values $u$ and solving the $o \times o$ linear system $L x = t - y$, retrying when $L$ is singular.

## Proof sketch

Expand the quadratic form at a point of the coset of $\mathcal{O}$; the oil–oil part vanishes by the choice of $P^{(3)}$, leaving the constant term and a bilinear cross term that is linear in $x$.

## Depends on

- [Oil-and-vinegar quadratic maps and the UOV trapdoor](oil-and-vinegar-maps.md)

## Sources

- Ward Beullens et al., "UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting Documentation", Version 3.0, 2026.
