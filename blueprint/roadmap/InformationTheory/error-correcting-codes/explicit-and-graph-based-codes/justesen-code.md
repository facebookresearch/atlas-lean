# Wozencraft encodings and Justesen codes

Let $F$ be a finite field with $q = 2^b$ elements, identified with $\{0,1\}^b$ by an additive bijection $\varphi$. The Wozencraft encoding at position $u \in F^\times$ maps a symbol $a \in F$ to the $2b$ bits $(\varphi(a), \varphi(u a))$; nonzero symbols (equal or not) at distinct positions have distinct encodings. The Justesen code of outer dimension $K \le q - 1$ takes a Reed-Solomon codeword $(p(u))_{u \in F^\times}$ of a polynomial $p$ of degree less than $K$, evaluated at the nonzero field elements, and replaces each symbol $p(u)$ by its Wozencraft encoding at $u$. It is a binary code of length $2b(q - 1)$ with $q^K = 2^{bK}$ codewords; its inner codes vary with the position, so no search for a good inner code is needed.

## Depends on

- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Sources

- J. Justesen, "Class of Constructive Asymptotically Good Algebraic Codes", IEEE Transactions on Information Theory, 1972.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
