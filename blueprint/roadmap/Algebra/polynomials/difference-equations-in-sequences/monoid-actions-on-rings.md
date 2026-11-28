# Monoid action on a semiring by semiring endomorphisms

An action of a monoid on a semiring by semiring endomorphisms is a monoid action under which every element of the monoid acts by a map that preserves $0$, $1$, addition and multiplication.

Let $M$ be a monoid and $R$ a semiring. An action of $M$ on $R$ by semiring endomorphisms is a map $M \times R \to R$, $(m, r) \mapsto m \cdot r$, such that $1 \cdot r = r$ and $(m_1 m_2) \cdot r = m_1 \cdot (m_2 \cdot r)$, and such that for each $m \in M$ we have $m \cdot 0 = 0$, $m \cdot 1 = 1$, $m \cdot (r + s) = m \cdot r + m \cdot s$ and $m \cdot (rs) = (m \cdot r)(m \cdot s)$ for all $r, s \in R$.

When $R$ is a commutative ring, the ring $R$ with such an action is what difference algebra calls an *$M$-ring*, writing $\sigma^m(r)$ for $m \cdot r$. For the additive monoid $(\mathbb{N}, +)$, viewed multiplicatively, an action is determined by the single ring endomorphism $\sigma = \sigma^1$, and a commutative ring with a ring endomorphism is a *difference ring*.

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; read in arXiv:1909.03239v2, Definition 2.1 (difference rings) and Definition 2.6 ($M$-rings, a commutative ring with an action of a monoid $M$ by endomorphisms) of Section 2.
