# UOV is EUF-CMA secure in the random oracle model

Instantiate salted hash-and-sign with the UOV trapdoor as in the UOV signature scheme: to sign a message $\mu$, draw a salt $r$ from a set $\mathcal{R}$, set $t = H(\mu, r)$, and compute a preimage of $t$ under the public map $\mathcal{P} : \mathbb{F}_q^n \to \mathbb{F}_q^m$ by the vinegar-and-linear-solve inverter $I$, which retries the vinegar variables until the linear system is nonsingular (so $H$ is queried once per signature). The *UOV inversion (INV) advantage* of an adversary is its probability of finding a preimage under $\mathcal{P}$ of a uniform target in $\mathbb{F}_q^m$; the *preimage-sampling (PS) advantage* of a distinguisher given $\mathcal{P}$ and $q_S$ sampling queries is the difference between its probabilities of outputting $1$ when each query returns $I(y)$ for a fresh uniform $y \in \mathbb{F}_q^m$ and when each query returns a uniform $x \in \mathbb{F}_q^n$. Then, in the classical random oracle model, for every forger making $q_S$ signing and $q_H$ hash queries there are an INV adversary $B$ and a PS distinguisher $D$ making $q_S$ sampling queries, both running in about the forger's time, such that the forger's EUF-CMA advantage is at most

$$
(q_H + 1)\,\mathrm{Adv}^{\mathrm{INV}}(B) + \mathrm{Adv}^{\mathrm{PS}}(D) + \frac{q_S\,(q_S + q_H + 1)}{|\mathcal{R}|}.
$$

Because the vinegar retries make the output of $I$ non-uniform, no statistical bound on the PS advantage is known for this scheme, so the statement gives EUF-CMA security when UOV inversion is hard and $I$ is computationally preimage-simulatable.

## Proof sketch

Take the uniform distribution on $\mathbb{F}_q^n$ as the domain sampler and apply the classical-random-oracle bound of Kosuge and Xagawa for probabilistic hash-and-sign with retry: signing queries are answered by programming $H(\mu, r) := \mathcal{P}(x)$ for uniform $x$, which costs the PS advantage and the salt-collision term; a forgery then inverts $\mathcal{P}$ on one of the $q_H + 1$ hash answers. With one salt per signature, the term for salt retries vanishes. The homogeneity attack shows why targets must be random-oracle outputs on fresh messages.

## Depends on

- [Oil-and-vinegar quadratic maps and the UOV trapdoor](oil-and-vinegar-maps.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/rom-signature-unforgeability.md)

## Proof depends on

- [EUF-CMA security of deterministic and salted hash-and-sign signatures in the random oracle model](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/hash-and-sign-trapdoor-signatures-rom.md)
- [UOV signing reduces to solving a linear system](uov-signing-linearization.md)

## Sources

- Ward Beullens et al., "UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting Documentation", Version 3.0, 2026.
- Haruhisa Kosuge and Keita Xagawa, "Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model", Public-Key Cryptography – PKC 2024, 2024.
