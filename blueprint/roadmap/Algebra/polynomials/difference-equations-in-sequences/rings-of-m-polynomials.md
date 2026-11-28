# Rings of M-polynomials

The $M$-polynomials over a ring with an action of a monoid $M$ are the polynomials in all shifts of finitely many unknowns; they form the free $M$-algebra on those unknowns.

Let $M$ be a monoid and $A$ a commutative ring with an action of $M$ by [ring endomorphisms](monoid-actions-on-rings.md), written $m \mapsto \sigma^m$. For unknowns $\boldsymbol{X} = (X_1, \dots, X_n)$, the ring of *$M$-polynomials* $A[\sigma^m(\boldsymbol{X}) \mid m \in M]$ is the ordinary polynomial ring over $A$ in the indeterminates $\sigma^m(X_i)$, $m \in M$, $1 \le i \le n$, with the action of $M$ that extends the action on $A$ and satisfies $\sigma^{m_1}(\sigma^{m_2}(X_i)) = \sigma^{m_1 m_2}(X_i)$. It is the free $M$-algebra over $A$ on $X_1, \dots, X_n$. For $M = \mathbb{N}$ its elements are the *difference polynomials*, and an equation $f = 0$ with $f$ a difference polynomial is a *difference equation*.

## Depends on

- [Monoid action on a semiring by semiring endomorphisms](monoid-actions-on-rings.md)
- [Commutative ring with identity](../../rings-and-fields/commutative-ring-with-identity.md)

## Proof depends on

None.

## Expansion

Solutions of systems of $M$-polynomial equations are defined in [solutions of systems of M-polynomial equations](solutions-of-difference-equations.md).

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; read in arXiv:1909.03239v2, Definitions 2.3 and 2.10 of Section 2.
