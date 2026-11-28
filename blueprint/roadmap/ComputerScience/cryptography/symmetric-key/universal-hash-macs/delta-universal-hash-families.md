# $\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families

Let $H : K \times M \to Y$ be a keyed hash with $K$ finite and $Y$ a finite abelian group. $H$ is *$\varepsilon$-almost-$\Delta$-universal* ($\varepsilon$-AXU, $\varepsilon$-DUF) on a set of inputs if for all distinct $m_0, m_1$ in the set and every $\delta \in Y$,

$$
\Pr_{k}\bigl[H(k, m_1) - H(k, m_0) = \delta\bigr] \le \varepsilon ;
$$

over $Y = \{0,1\}^b$ with XOR this is an *XOR-DUF*. $H$ is *$\varepsilon$-pairwise unpredictable* if for all distinct $m_0, m_1$ and all $y_0, y_1$, $\Pr_k[H(k, m_1) = y_1 \mid H(k, m_0) = y_0] \le \varepsilon$. An $\varepsilon$-AXU family with $\delta = 0$ is $\varepsilon$-almost universal.

## Depends on

- [Carter–Wegman MACs](../macs-and-modes/carterwegman-macs.md)
- [Universal hash family](../../../data-structures/hashing/universal-hashing/is-universal.md)

## Sources

- Mark N. Wegman and J. Lawrence Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
