# Security of Schnorr signatures in the random oracle model

Let $\mathbb{G}$ be a cyclic group of prime order $q$, and let $H$ be modelled as a random oracle. If Schnorr's identification scheme is secure against eavesdropping attacks, then Schnorr's signature scheme, obtained from it by the Fiat–Shamir transform with challenge $H(m, g^r)$, is existentially unforgeable under chosen-message attacks: for an adversary $A$ making at most $Q_s$ signing and $Q_{\mathrm{ro}}$ random-oracle queries there is a $(Q_{\mathrm{ro}} + 1)$-impersonation adversary $B$ against the identification scheme under eavesdropping with

$$\mathrm{Adv}^{\mathrm{SIG}}[A] \le \frac{Q_s(Q_s + Q_{\mathrm{ro}} + 1)}{q} + \mathrm{Adv}^{\mathrm{rID2}}[B, Q_{\mathrm{ro}} + 1].$$

Combined with the security of Schnorr identification under the discrete logarithm assumption, which is proved by rewinding, this gives security of Schnorr signatures under the discrete logarithm assumption.

## Depends on

- [Polynomial-query unforgeability of signatures](../../security-games/asymptotic-security/poly-query-sig-secure.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Special soundness](../schnorr-identification-scheme/extract-spec.md)
- [Schnorr identification is secure against direct attacks](schnorr-identification-is-secure-against-direct.md)
- [The rewinding lemma](the-rewinding-lemma.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 19.7
- C. P. Schnorr, "Efficient signature generation by smart cards", *Journal of Cryptology* 4(3):161–174, 1991
