# Regular words and the regular syndrome decoding problem

Fix integers $w$ (number of chunks) and $m$ (chunk size), so words have length $n = w m$ and are indexed by pairs (chunk, position). A binary word $x \in \mathbb{F}_2^{n}$ is regular if each of its $w$ chunks is an elementary vector, having exactly one nonzero coordinate; regular words have Hamming weight exactly $w$ and are in bijection with the choices of one position per chunk. Given a parity-check matrix $H \in \mathbb{F}_2^{r \times n}$ and a syndrome $y \in \mathbb{F}_2^r$, the regular syndrome decoding problem asks for a regular word $x$ with $H x = y$. It is the hardness assumption behind code-based signature schemes built from the syndrome-decoding-in-the-head paradigm and regular variants of code-based cryptosystems.

## Depends on

- [Syndrome](../linear-codes/syndrome.md)
- [Code with a given parity-check matrix](../linear-codes/of-parity-check.md)

## Sources

- D. Augot, M. Finiasz and N. Sendrier, "A Family of Fast Syndrome Based Cryptographic Hash Functions", Mycrypt 2005, Lecture Notes in Computer Science 3715, 2005.
- T. Feneuil, A. Joux and M. Rivain, "Syndrome Decoding in the Head: Shorter Signatures from Zero-Knowledge Proofs", Advances in Cryptology (CRYPTO 2022), 2022.
- E. Carozza, G. Couteau and A. Joux, "Short Signatures from Regular Syndrome Decoding in the Head", Advances in Cryptology (EUROCRYPT 2023), 2023.
