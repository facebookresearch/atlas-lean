# EUF-CMA security of deterministic and salted hash-and-sign signatures in the random oracle model

Let $(f_{pk}, \mathrm{Inv}_{sk})$ be a trapdoor preimage-sampleable function family whose preimage sampler, on a uniform target, outputs a preimage whose distribution is within statistical distance $\zeta$ of the distribution of $x$ conditioned on $f_{pk}(x) = y$ for a uniform $x$ (or, for a non-uniform function, any law that can be simulated from the public key). (i) *Salted* hash-and-sign signs $m$ by drawing a salt $r$ of $\ell$ bits and returning $(r, \mathrm{Inv}_{sk}(H(r, m)))$. Against a forger making $q_S$ signing and $q_H$ hash queries, the EUF-CMA success probability is at most $(q_H + 1)$ times the one-wayness (single-target inversion) advantage of an explicit reduction, plus a salt-collision term $q_S (q_S + q_H)/2^{\ell}$ and $q_S\,\zeta$. (ii) *Deterministic unsalted* hash-and-sign $\sigma = \mathrm{Inv}_{sk}(H(m))$, where signing the same message twice returns the same preimage, satisfies the same bound without the salt term, provided the signer derandomizes its preimage sampling with a function of the message. Hence, if $f$ is one-way, both schemes are EUF-CMA secure in the random oracle model.

## Proof sketch

The reduction guesses which hash query will be forged on and plants the inversion challenge there; every other hash query $H(r, m)$ is programmed as $f_{pk}(x)$ for a sampled preimage $x$, which also answers signing queries. A forgery at the guessed query inverts the challenge.

## Depends on

- [Signature schemes and (strong) unforgeability in the random oracle model](rom-signature-unforgeability.md)
- [Trapdoor permutations](../../../public-key/hardness-assumptions/trapdoor-permutations.md)
- [Hash-and-sign](../../../public-key/random-oracle-constructions/hash-and-sign.md)

## Sources

- Haruhisa Kosuge and Keita Xagawa, "Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model", Cryptology ePrint Archive, Paper 2022/1359, 2022.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
