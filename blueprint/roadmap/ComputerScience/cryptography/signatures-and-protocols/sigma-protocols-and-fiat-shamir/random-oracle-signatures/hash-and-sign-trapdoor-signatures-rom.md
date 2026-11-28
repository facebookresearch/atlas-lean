# EUF-CMA security of deterministic and salted hash-and-sign signatures in the random oracle model

Let $(f_{pk}, \mathrm{Inv}_{sk})$ be a trapdoor preimage-sampleable function family with a domain distribution $\mathcal{D}_{pk}$ that can be sampled from $pk$ alone, such that the pairs $(\mathrm{Inv}_{sk}(y), y)$ for a uniform $y$ in the range and $(x, f_{pk}(x))$ for $x \leftarrow \mathcal{D}_{pk}$ are within statistical distance $\zeta$; in particular $f_{pk}(x)$ for $x \leftarrow \mathcal{D}_{pk}$ is within statistical distance $\zeta$ of uniform. Let the one-wayness advantage be the probability of finding a preimage of a uniform target. (i) *Salted* hash-and-sign signs $m$ by drawing a fresh uniform salt $r$ of $\ell$ bits and returning $(r, \mathrm{Inv}_{sk}(H(r, m)))$. Against a forger making $q_S$ signing and $q_H$ hash queries, the EUF-CMA success probability is at most $(q_H + 1)$ times the one-wayness advantage of an explicit reduction, plus a salt-collision term $q_S (q_S + q_H + 1)/2^{\ell}$ and $q_S\,\zeta$ (Kosuge and Xagawa's classical random-oracle bound for probabilistic hash-and-sign with one salt per signature, whose preimage-sampling advantage is at most $q_S\,\zeta$ here). (ii) *Deterministic unsalted* (full-domain-hash) signing $\sigma = \mathrm{Inv}_{sk}(H(m))$ with a trapdoor permutation, that is, $f_{pk}$ a permutation with inverse $\mathrm{Inv}_{sk}$ (the case $\zeta = 0$ with $\mathcal{D}_{pk}$ uniform), has EUF-CMA success probability at most $(q_H + 1)$ times the one-wayness advantage of an explicit reduction (Boneh and Shoup, Theorem 13.3). Hence, if $f$ is one-way and $\zeta$ and $2^{-\ell}$ are negligible, the salted scheme is EUF-CMA secure in the random oracle model, and so is full domain hash with a one-way trapdoor permutation.

## Proof sketch

The reduction guesses which hash query will be forged on and plants the inversion challenge there. In the salted scheme, each signing query picks a fresh salt, aborts if the point $(r, m)$ is already defined, and otherwise programs $H(r, m) := f_{pk}(x)$ for $x \leftarrow \mathcal{D}_{pk}$ and returns $(r, x)$, at cost $\zeta$ per signing query. In full domain hash every hashed message except the guessed one is programmed this way with $\zeta = 0$. A forgery at the guessed query inverts the challenge. The following extension of (ii) beyond trapdoor permutations is derived here and stated by neither cited source: if the signer of $\sigma = \mathrm{Inv}_{sk}(H(m))$ runs the preimage sampler on coins $R(m)$ for a uniformly random function $R$, independent of everything else, so that signing the same message twice returns the same preimage, the EUF-CMA success probability is at most $(q_H + 1)$ times the one-wayness advantage of an explicit reduction plus $(2 q_H + q_S + 2)\,\zeta$, and if $R$ is instead a keyed pseudorandom function, add the PRF advantage of an explicit reduction. Every hashed message except the guessed one is programmed as above, since it may be signed later; this costs $\zeta$ per hashed message (at most $q_H + q_S + 1$ of them) and replacing the guessed point's value $f_{pk}(x)$ by the uniform challenge costs another $\zeta$, which the $(q_H + 1)$-fold guessing loss multiplies.

## Depends on

- [Signature schemes and (strong) unforgeability in the random oracle model](rom-signature-unforgeability.md)
- [Trapdoor permutations](../../../public-key/hardness-assumptions/trapdoor-permutations.md)
- [Hash-and-sign](../../../public-key/random-oracle-constructions/hash-and-sign.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [PRF advantage](../../../symmetric-key/pseudorandom-functions/prf-advantage.md)

## Sources

- Haruhisa Kosuge and Keita Xagawa, "Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model", Public-Key Cryptography – PKC 2024, LNCS, Springer, 2024.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023, Theorem 13.3.
