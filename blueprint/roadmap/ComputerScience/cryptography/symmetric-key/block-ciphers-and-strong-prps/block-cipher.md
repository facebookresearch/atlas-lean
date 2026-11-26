# Block cipher (uniform family)

A *block cipher* is a family of keyed permutations: polynomial-time computable lengths $\kappa(n)$ (key) and $b(n)$ (block), and deterministic polynomial-time algorithms $E, D$ with $E(k, \cdot) : \{0,1\}^{b(n)} \to \{0,1\}^{b(n)}$ a permutation for every $k \in \{0,1\}^{\kappa(n)}$ and $D(k, E(k, x)) = x$. It is a *PRP* if $E(k, \cdot)$ for uniform $k$ is indistinguishable from a uniform permutation by efficient adaptive forward-query adversaries.

## Depends on

- [Asymptotic PRP security relative to a class of distinguishers](../pseudorandom-permutations/prpsecure.md)
- [PRP advantage](../pseudorandom-permutations/prp-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
