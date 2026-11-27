# UOV is EUF-CMA secure in the random oracle model

Instantiate salted hash-and-sign with the UOV trapdoor: to sign $m$, draw a salt $r$, set $t = H(m, r)$, and sample a preimage of $t$ by the vinegar-and-linear-solve procedure (retrying on singular systems). Assume the *UOV problem* (finding a preimage of a uniform target under a public UOV map) is hard and that, for a uniform target, the signer's preimage is within statistical distance $\zeta$ of a uniform preimage of that target. Then, in the classical random oracle model, every forger making $q_S$ signing and $q_H$ hash queries succeeds with probability at most $(q_H + 1)$ times the UOV-inversion advantage of an explicit reduction, plus a salt-collision term $q_S(q_S + q_H)/|\mathcal{R}|$ and $q_S\,\zeta$.

## Proof sketch

Apply the hash-and-sign theorem with the UOV public map as trapdoor function; the homogeneity attack shows why targets must be random-oracle outputs on fresh messages.

## Depends on

- [Oil-and-vinegar quadratic maps and the UOV trapdoor](oil-and-vinegar-maps.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/rom-signature-unforgeability.md)

## Proof depends on

- [EUF-CMA security of deterministic and salted hash-and-sign signatures in the random oracle model](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/hash-and-sign-trapdoor-signatures-rom.md)
- [UOV signing reduces to solving a linear system](uov-signing-linearization.md)

## Sources

- Ward Beullens et al., "UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting Documentation", Version 3.0, 2026.
- Haruhisa Kosuge and Keita Xagawa, "Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model", Cryptology ePrint Archive, Paper 2022/1359, 2022.
