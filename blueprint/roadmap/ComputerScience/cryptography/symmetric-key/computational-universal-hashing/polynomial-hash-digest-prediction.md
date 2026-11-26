# One revealed polynomial-hash digest predicts another

Let $H_k(m_1, \dots, m_\ell) = k^{\ell+1} + m_1 k^{\ell} + \cdots + m_\ell k$ be the variable-length polynomial hash over a finite field $\mathbb{F}$ (the variant with the leading monomial $k^{\ell+1}$, so the empty message hashes to $k$). An adversary that queries the empty message, obtaining $t = k$, and then predicts the digest $t^2$ of the one-block message $(0)$ wins with probability $1$. Hence this hash is not pairwise unpredictable, although it is difference universal for bounded lengths.

## Proof sketch

$H_k(()) = k$ and $H_k((0)) = k^2 + 0\cdot k = k^2$.

## Depends on

- [A difference-universal hash with a uniform offset is pairwise unpredictable](pairwise-unpredictable-from-difference-universal.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
