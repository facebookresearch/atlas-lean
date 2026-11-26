# Davies–Meyer compression function

Given a block cipher $E : K \times X \to X$ on a group $X$ (usually $\{0,1\}^n$ under XOR), the *Davies–Meyer* compression function is $h_{\mathrm{DM}}(k, x) = E(k, x) + x$, mapping a message block $k$ and a chaining value $x$ to a new chaining value.

## Depends on

- [Block cipher (uniform family)](../../symmetric-key/block-ciphers-and-strong-prps/block-cipher.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Black, P. Rogaway and T. Shrimpton, "Black-Box Analysis of the Block-Cipher-Based Hash-Function Constructions from PGV", Advances in Cryptology (CRYPTO 2002), LNCS 2442, 2002.
