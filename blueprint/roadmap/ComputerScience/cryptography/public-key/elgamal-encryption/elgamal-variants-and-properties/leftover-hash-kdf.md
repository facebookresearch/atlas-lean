# Matrix hashing with a public seed is an unconditionally secure KDF

Let group elements be encoded injectively into $\{0,1\}^{w}$ and let $H_S(x) = S x$ for a uniform public binary matrix $S$ of size $\ell \times w$. For a uniform element of a group of order $q$, $(S, H_S(g^\gamma))$ is within statistical distance $\tfrac12\sqrt{2^\ell/q}$ of $(S, U_\ell)$. Hence $H$ is a secure KDF, with no computational assumption, whenever $2^\ell/q$ is negligible.

## Proof sketch

The matrix family is $2^{-\ell}$-universal and a uniform group element has min-entropy $\log_2 q$; apply the leftover hash lemma.

## Depends on

- [Secure key derivation function for a group](secure-key-derivation-function.md)

## Proof depends on

- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)

## Sources

- V. Shoup, "A Computational Introduction to Number Theory and Algebra", 2nd edition, Cambridge University Press, 2009, Section 8.9 (leftover hash lemma).
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023 (universality of the binary-matrix family).
