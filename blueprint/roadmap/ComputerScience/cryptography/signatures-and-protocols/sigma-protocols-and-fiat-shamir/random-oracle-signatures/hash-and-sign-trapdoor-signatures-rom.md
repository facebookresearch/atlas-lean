# EUF-CMA security of deterministic and salted hash-and-sign signatures in the random oracle model

Let $(f_{pk}, \mathrm{Inv}_{sk})$ be a trapdoor preimage-sampleable function family with a domain distribution $\mathcal{D}_{pk}$ that can be sampled from $pk$ alone, such that the pairs $(\mathrm{Inv}_{sk}(y), y)$ for a uniform $y$ in the range and $(x, f_{pk}(x))$ for $x \leftarrow \mathcal{D}_{pk}$ are within statistical distance $\zeta$; in particular $f_{pk}(x)$ for $x \leftarrow \mathcal{D}_{pk}$ is within statistical distance $\zeta$ of uniform. Let the one-wayness advantage be the probability of finding a preimage of a uniform target. (i) *Salted* hash-and-sign signs $m$ by drawing a fresh uniform salt $r$ of $\ell$ bits and returning $(r, \mathrm{Inv}_{sk}(H(r, m)))$. Against a forger making $q_S$ signing and $q_H$ hash queries, the EUF-CMA success probability is at most $(q_H + 1)$ times the one-wayness advantage of an explicit reduction, plus a salt-collision term $q_S (q_S + q_H)/2^{\ell}$ and $q_S\,\zeta$. (ii) *Deterministic unsalted* hash-and-sign $\sigma = \mathrm{Inv}_{sk}(H(m))$, where the signer runs the preimage sampler on coins $R(m)$ for a uniformly random function $R$, independent of everything else, so that signing the same message twice returns the same preimage, has EUF-CMA success probability at most $(q_H + 1)$ times the one-wayness advantage of an explicit reduction plus $(2 q_H + q_S + 2)\,\zeta$; if $R$ is instead a keyed pseudorandom function, add the PRF advantage of an explicit reduction. Hence, if $f$ is one-way and $\zeta$ and $2^{-\ell}$ are negligible (and the PRF, if used, is secure), both schemes are EUF-CMA secure in the random oracle model.

## Proof sketch

The reduction guesses which hash query will be forged on and plants the inversion challenge there. In the salted scheme, each signing query picks a fresh salt, aborts if the point $(r, m)$ is already defined, and otherwise programs $H(r, m) := f_{pk}(x)$ for $x \leftarrow \mathcal{D}_{pk}$ and returns $(r, x)$, at cost $\zeta$ per signing query. In the deterministic scheme every hashed message except the guessed one is programmed this way, since it may be signed later; this costs $\zeta$ per hashed message (at most $q_H + q_S + 1$ of them) and replacing the guessed point's value $f_{pk}(x)$ by the uniform challenge costs another $\zeta$, which the $(q_H + 1)$-fold guessing loss multiplies. A forgery at the guessed query inverts the challenge.

## Depends on

- [Signature schemes and (strong) unforgeability in the random oracle model](rom-signature-unforgeability.md)
- [Trapdoor permutations](../../../public-key/hardness-assumptions/trapdoor-permutations.md)
- [Hash-and-sign](../../../public-key/random-oracle-constructions/hash-and-sign.md)
- [PRF advantage](../../../symmetric-key/pseudorandom-functions/prf-advantage.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Haruhisa Kosuge and Keita Xagawa, "Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model", Public-Key Cryptography – PKC 2024, LNCS, Springer, 2024.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
