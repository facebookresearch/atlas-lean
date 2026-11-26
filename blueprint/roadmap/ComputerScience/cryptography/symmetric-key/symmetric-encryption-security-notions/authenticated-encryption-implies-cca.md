# Authenticated encryption implies chosen-ciphertext security

Every authenticated-encryption cipher is CCA secure. Concretely, for a CCA adversary making $Q_d$ decryption queries,

$$\mathrm{CCAadv} \le \mathrm{CPAadv}(B_1) + 2 Q_d \cdot \mathrm{CIadv}(B_2)$$

for reductions $B_1, B_2$ whose running times exceed that of the CCA adversary by at most the time of recording its encryption queries with their answers and one lookup in that record for each decryption query. The same holds for one-time authenticated encryption and one-time CCA security.

## Proof sketch

Replace the decryption oracle by one that rejects every ciphertext not returned by the encryption oracle (and answers those with the known plaintext). The change is visible only if some decryption query is a valid forgery, which a ciphertext-integrity adversary that guesses the query index exploits; the modified game is a CPA game.

## Depends on

- [Authenticated encryption](authenticated-encryption.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Proof depends on

- [Planted-query guessing: bounding a bad event by a reduction that guesses its index](../../security-games/identical-until-bad-oracle-handlers/planted-query-guessing-bound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
