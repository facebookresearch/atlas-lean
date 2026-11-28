# The Fujisaki–Okamoto transform

Let $\mathcal{E}_a$ be a public-key encryption scheme with message space $X$ and randomizer space $R$ that is one-way and $\varepsilon$-unpredictable (every ciphertext arises from a given message with probability at most $\varepsilon$ over the encryption randomness), let $\mathcal{E}_s$ be a symmetric cipher secure against one-time chosen-ciphertext attacks, and let $H : X \to K$ and $U : X \to R$ be random oracles. The Fujisaki–Okamoto scheme encrypts $m$ by choosing a uniform $x \in X$ and outputting $(y, c)$ with $y = \mathcal{E}_a(pk, x; U(x))$ and $c = \mathcal{E}_s(H(x), m)$; decryption computes $x = \mathcal{D}_a(sk, y)$, rejects unless $\mathcal{E}_a(pk, x; U(x)) = y$, and otherwise returns $\mathcal{D}_s(H(x), c)$. It is secure against chosen-ciphertext attacks: for a one-challenge (1CCA) adversary making at most $Q_d$ decryption queries and $Q_H$, $Q_U$ random-oracle queries,

$$\mathrm{Adv}^{\mathrm{1CCA}}[A, \mathcal{E}_{\mathrm{FO}}] \le 2(Q_H + Q_U)\cdot \mathrm{Adv}^{\mathrm{OW}}[B_a, \mathcal{E}_a] + 2 Q_d \varepsilon + \mathrm{Adv}^{\mathrm{1CCA}}[B_s, \mathcal{E}_s]$$


for derived adversaries $B_a$ and $B_s$; for public-key schemes 1CCA security implies CCA security.

## Depends on

- [The random oracle model](the-random-oracle-model.md)
- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 12.11
- Original transformation: E. Fujisaki and T. Okamoto, "Secure integration of asymmetric and symmetric encryption schemes", *CRYPTO 1999*, LNCS 1666, Springer, 1999. The variant and the bound stated above follow Boneh and Shoup, Section 12.6.1 and Theorem 12.11.
