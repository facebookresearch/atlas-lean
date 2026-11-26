# Rescaling attacks separate preimage-security notions for homogeneous maps

Let $\mathbb{F}$ have at least $4$ elements and $\mathcal{P} : \mathbb{F}^n \to \mathbb{F}^o$ be homogeneous of degree $2$, so $\mathcal{P}(a x) = a^2 \mathcal{P}(x)$. In a game where the adversary may request one preimage of a target of its choice and must then invert a fresh unqueried target $y \ne 0$, one query suffices: request a preimage $x'$ of $a^{-2}y$ for some $a \ne 0, \pm 1$ and output $a x'$, which is a valid preimage of $y$ with probability $1$. Hence for hash-and-sign signatures on homogeneous maps (as in UOV), security must be stated with respect to preimages of random-oracle outputs on fresh messages, not adversarially chosen targets.

## Proof sketch

Homogeneity: $\mathcal{P}(a x') = a^2 \mathcal{P}(x') = a^2 a^{-2} y = y$.

## Depends on

- [Oil-and-vinegar quadratic maps and the UOV trapdoor](oil-and-vinegar-maps.md)
- [Multi-target and one-more preimage games](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/one-more-preimage-games.md)

## Sources

- Ward Beullens et al., "UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting Documentation", Version 3.0, 2026.
- Haruhisa Kosuge and Keita Xagawa, "Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model", Cryptology ePrint Archive, Paper 2022/1359, 2022.
