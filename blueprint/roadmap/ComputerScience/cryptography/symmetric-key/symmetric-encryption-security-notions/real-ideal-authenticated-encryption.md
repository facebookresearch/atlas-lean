# Real/ideal authenticated encryption equals CCA security plus plaintext integrity

For a symmetric cipher on fixed $n$-bit messages, consider the real/ideal AE experiment: in the real world the adversary has oracles $\mathrm{Enc}_k$ and $\mathrm{Dec}_k$; in the ideal world encryption returns the encryption of a fixed message $0^n$ and decryption rejects everything except earlier encryption replies (which both worlds refuse to decrypt). The cipher is real/ideal AE secure if and only if it is (adaptive, left-or-right) CCA secure and has plaintext integrity. The two-world advantage equals twice the deviation of the hidden-bit guessing probability from $\tfrac12$.

## Proof sketch

From real/ideal security, both CCA security and plaintext integrity follow by hybrids through the ideal world. Conversely, replace real decryption by rejection (plaintext integrity bounds the difference, since fixed-length forgeries of unqueried plaintexts are the only detectable change) and then real encryption by encryption of $0^n$ (left-or-right CCA).

## Depends on

- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Proof depends on

- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
- P. Rogaway and T. Shrimpton, "A Provable-Security Treatment of the Key-Wrap Problem", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
