# Rings of sequences indexed by a monoid

For a commutative ring $R$ and a monoid $M$, the ring of $M$-sequences is the ring of all maps from $M$ to $R$ under pointwise operations, on which $M$ acts by shifting the index.

Let $M$ be a monoid and $R$ a [commutative ring with identity](../../rings-and-fields/commutative-ring-with-identity.md). The ring $R^M$ of *$M$-sequences* is the ring of all maps $x \colon M \to R$, written $x = (x_\ell)_{\ell \in M}$, with pointwise addition and multiplication. The monoid $M$ acts on $R^M$ by [ring endomorphisms](monoid-actions-on-rings.md): the shift by $m \in M$ is $\sigma^m\bigl((x_\ell)_{\ell \in M}\bigr) = (x_{\ell m})_{\ell \in M}$, and $\sigma^{m_1} \sigma^{m_2} = \sigma^{m_1 m_2}$.

For $M = \mathbb{N}$ or $M = \mathbb{Z}$ this is the ring of one-sided or two-sided sequences with the shift $\sigma((x_i)_i) = (x_{i+1})_i$. For $M = \mathbb{N}^2$ or $\mathbb{Z}^2$ it is the ring of sequences indexed by the grid, with the two shifts, and for the free monoid $\Sigma^\ast$ on a finite alphabet $\Sigma$ it is the ring of functions on words, with $\sigma^w((x_u)_u) = (x_{uw})_u$.

## Depends on

- [Commutative ring with identity](../../rings-and-fields/commutative-ring-with-identity.md)
- [Monoid action on a semiring by semiring endomorphisms](monoid-actions-on-rings.md)

## Proof depends on

None.

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; definitions read in arXiv:1909.03239v2, Examples 2.2, 2.7, 2.8 and 2.9 of Section 2.
