# Real/ideal authenticated encryption equals CCA security plus plaintext integrity

For a symmetric cipher on fixed $n$-bit messages with $2^{-n}$ negligible, consider the real/ideal AE experiment: in the real world the adversary has oracles $\mathrm{Enc}_k$ and $\mathrm{Dec}_k$; in the ideal world encryption returns the encryption of a fixed message $0^n$ and decryption rejects everything except earlier encryption replies (which both worlds refuse to decrypt). The cipher is real/ideal AE secure if and only if it is (adaptive, left-or-right) CCA secure and has plaintext integrity. The two-world advantage equals twice the deviation of the hidden-bit guessing probability from $\tfrac12$.

## Proof sketch

From real/ideal security, both CCA security and plaintext integrity follow by hybrids through the ideal world. Conversely, first replace real decryption by rejection. A new ciphertext that decrypts to a plaintext never queried for encryption is a plaintext-integrity forgery. A new ciphertext that decrypts to an earlier queried plaintext $m_j$ is handled by a CCA reduction that answers each encryption query $m$ with the challenge pair $(m, m')$ for an independent uniform $m'$: in the world that encrypts the $m'$, such a ciphertext is a plaintext-integrity forgery unless some uniform $m'$ equals a queried plaintext, which has probability at most $Q^2/2^n$ for $Q$ queries and is negligible because $2^{-n}$ is. Then replace real encryption by encryption of $0^n$ (left-or-right CCA, with decryption no longer used). This direction combines Boneh and Shoup, Exercise 9.15(b) (CCA security and plaintext integrity give AE security when the message space is super-poly) with their Section 9.3 (AE security makes the real and ideal implementations indistinguishable); for the other direction compare their Theorem 9.1 (AE security implies CCA security).

## Depends on

- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Proof depends on

- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Theorem 9.1 (AE security implies CCA security), Section 9.3 (AE security makes the real implementation indistinguishable from the ideal one that encrypts a dummy message and delivers only earlier ciphertexts) and Exercise 9.15(b) (CCA and plaintext integrity imply AE security, for a super-poly message space).
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
- P. Rogaway and T. Shrimpton, "A Provable-Security Treatment of the Key-Wrap Problem", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
