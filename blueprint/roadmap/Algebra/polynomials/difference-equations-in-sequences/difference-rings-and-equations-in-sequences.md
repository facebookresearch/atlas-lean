# Difference rings and rings of sequences

A difference ring is a commutative ring with an endomorphism; more generally a monoid can act on a ring by endomorphisms. Sequences over a ring indexed by the monoid, with the shifts, form such a ring.

Let $M$ be a monoid. All rings are commutative with identity.

- A *difference ring* is a pair $(A, \sigma)$ of a commutative ring $A$ and a ring endomorphism $\sigma \colon A \to A$. More generally, an *$M$-ring* is a commutative ring $A$ with an action $m \mapsto \sigma^m$ of $M$ on $A$ by ring endomorphisms; a difference ring is an $\mathbb{N}$-ring for the additive monoid $(\mathbb{N}, +)$, where $\mathbb{N} = \{0, 1, 2, \dots\}$. A morphism of $M$-rings is a ring homomorphism that commutes with the actions.
- For a commutative ring $R$, the ring $R^M$ of *$M$-sequences* is the ring of all maps $M \to R$, with pointwise addition and multiplication, and with the action
  The shift by $m \in M$ is $\sigma^m\bigl((x_\ell)_{\ell \in M}\bigr) = (x_{\ell m})_{\ell \in M}$.

  For $M = \mathbb{N}$ or $M = \mathbb{Z}$ this is the ring of one-sided or two-sided sequences with the shift $\sigma((x_i)_i) = (x_{i+1})_i$. For $M = \mathbb{N}^2$ or $\mathbb{Z}^2$ it is the ring of sequences indexed by the grid, with the two shifts, and for the free monoid $\Sigma^\ast$ on a finite alphabet $\Sigma$ it is the ring of functions on words, with $\sigma^w((x_u)_u) = (x_{uw})_u$.

## Depends on

- [Commutative ring with identity](../../rings-and-fields/commutative-ring-with-identity.md)

## Proof depends on

None.

## Expansion

Systems of equations over these rings, and their solutions, are defined in [difference polynomials and their solutions](difference-polynomials-and-their-solutions.md).

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; definitions read in arXiv:1909.03239v2, Definitions 2.1 and 2.6 and Examples 2.2, 2.7, 2.8 and 2.9 of Section 2.
