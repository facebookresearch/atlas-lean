# Real/ideal authenticated encryption equals CCA security plus plaintext integrity

For a symmetric cipher on fixed $n$-bit messages with $2^{-n}$ negligible (so the message space is super-poly), the following are equivalent: (a) the cipher is AE secure, that is, CPA secure with ciphertext integrity; (b) it is (adaptive, left-or-right) CCA secure and has plaintext integrity. Here (a) gives CCA security by Boneh and Shoup, Theorem 9.1, and plaintext integrity because ciphertext integrity implies it (their Exercise 9.15 introduces plaintext integrity as a weaker notion than the ciphertext integrity of Attack Game 9.1 and Definition 9.1); and (b) gives (a) by their Exercise 9.15(b). AE security in turn makes the real implementation of encryption indistinguishable from the ideal one, in which the sender encrypts a dummy message of the same length and the receiver delivers the message behind each ciphertext the sender generated and discards every other ciphertext (their Section 9.3).

## Proof sketch

(a) to (b): the proof of Theorem 9.1 replaces decryption by rejection of every ciphertext the encryption oracle did not return, a change that ciphertext integrity makes invisible, and what remains is a CPA game. Every plaintext-integrity win is a ciphertext-integrity win: by correctness, a ciphertext that decrypts to a message outside $\{m_1, m_2, \dots\}$ was not returned by the encryption oracle.

(b) to (a): CCA security includes CPA security. For ciphertext integrity, a new ciphertext that decrypts to a plaintext never queried for encryption is a plaintext-integrity forgery. A new ciphertext that decrypts to an earlier queried plaintext $m_j$ is handled by a CCA reduction that answers each encryption query $m$ with the challenge pair $(m, m')$ for an independent uniform $m'$ and submits the candidate as its one decryption query: in the world that encrypts the $m'$, such a ciphertext is a plaintext-integrity forgery unless some uniform $m'$ equals a queried plaintext, which has probability at most $Q^2/2^n$ for $Q$ queries and is negligible because $2^{-n}$ is.

Real and ideal implementations: Section 9.3 passes from the real to the ideal implementation in three steps, delivering generated ciphertexts by lookup (correctness), discarding all other ciphertexts (ciphertext integrity), and encrypting the dummy messages (CPA security, as decryption is no longer used). Conversely, indistinguishability of the two implementations gives CPA security, since encryptions of either challenge message are indistinguishable from encryptions of the dummy message, and ciphertext integrity, since a fresh ciphertext that real decryption accepts is discarded in the ideal world; so the real/ideal notion is equivalent to (a) and to (b). As for every two-world game, the advantage is twice the deviation of the hidden-bit guessing probability from $\tfrac12$ (for CCA security, $\mathrm{CCAadv} = 2\,\mathrm{CCAadv}^*$, Boneh and Shoup, equation (9.1)).

## Depends on

- [Authenticated encryption](authenticated-encryption.md)
- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Proof depends on

- [Authenticated encryption implies chosen-ciphertext security](authenticated-encryption-implies-cca.md)
- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Attack Game 9.1 and Definitions 9.1-9.2 (ciphertext integrity; AE security is CPA security with ciphertext integrity), Theorem 9.1 (AE security implies CCA security) with equation (9.1), Section 9.3 (AE security makes the real implementation indistinguishable from the ideal one that encrypts a dummy message and delivers only ciphertexts the sender generated) and Exercise 9.15 (plaintext integrity, a weaker notion than ciphertext integrity; (b) CCA security and plaintext integrity imply AE security, for a super-poly message space).
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
- P. Rogaway and T. Shrimpton, "A Provable-Security Treatment of the Key-Wrap Problem", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
