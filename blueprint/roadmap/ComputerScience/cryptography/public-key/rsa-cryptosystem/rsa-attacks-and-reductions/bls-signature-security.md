# BLS signatures are strongly unforgeable in the random oracle model

If the co-CDH problem (given $g_1^{\alpha}, g_2^{\alpha}$ and $h \in G_1$, compute $h^{\alpha}$) is hard, then BLS signatures are EUF-CMA secure in the random oracle model, and since signatures are unique also SUF-CMA secure. A forger with success probability $\varepsilon$ that makes $Q_H$ hash and $Q_S$ signing queries, and queries $H$ on the message it forges, yields a co-CDH solver with advantage at least $\varepsilon/(e(Q_S+1))$ using Coron's biased programming with probability $1/(Q_S+1)$, since $(1 - 1/(Q_S+1))^{Q_S} \ge 1/e$, or $\varepsilon/Q_H$ by guessing the forgery's hash query.

## Proof sketch

Program $H(m) = g_1^{r}$ on most queries, so that signatures $(g_1^{\alpha})^{r}$ can be produced from $g_1^\alpha$, and $H(m) = h\,g_1^{r}$ on the guessed forgery query, so that a forgery yields $h^\alpha$. Uniqueness of signatures (the verification equation determines $\sigma$) gives strong unforgeability.

## Depends on

- [BLS signatures](bls-signatures.md)
- [Pairing-based assumptions: BDH and t-SDH](../../advanced-encryption-and-pairings/pairing-based-assumptions-bdh-and-t-sdh.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)

## Proof depends on

- [Full-domain-hash signatures](../../random-oracle-constructions/full-domain-hash-signatures.md)

## Sources

- D. Boneh, B. Lynn and H. Shacham, "Short Signatures from the Weil Pairing", Journal of Cryptology 17(4), 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
