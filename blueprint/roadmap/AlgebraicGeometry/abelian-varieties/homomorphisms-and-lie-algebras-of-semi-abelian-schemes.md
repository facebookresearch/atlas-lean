# Homomorphisms and Lie algebras of semi-abelian schemes

This node is still to be broken down. A semi-abelian scheme over a scheme $S$ is a smooth separated
commutative group scheme of finite type over $S$ whose fibres are connected and are extensions of an
abelian variety by a torus, such as the semi-abelian schemes of
[Mumford's construction](moduli-and-compactifications/mumford-construction-of-degenerating-abelian-varieties.md) and of the
[semistable reduction theorem](semistable-reduction-theorem.md). The targets are:

1. (Extension of homomorphisms.) Let $S$ be a noetherian normal scheme, $U \subset S$ a dense open
   subscheme and $G$, $H$ semi-abelian schemes over $S$. Every homomorphism $G|_U \to H|_U$ extends
   uniquely to a homomorphism $G \to H$.
2. (Seminegativity of the Lie algebra.) Let $k$ be a field of characteristic zero, $C$ a smooth
   projective geometrically connected curve over $k$ and $G$ a semi-abelian scheme over $C$. Every
   subbundle $W$ of the Lie algebra $\operatorname{Lie}(G/C)$, the vector bundle dual to
   $\omega_{G/C} = e^* \Omega^1_{G/C}$, has $\deg \det W \le 0$; equivalently, every quotient bundle
   of $\omega_{G/C}$ has nonnegative degree.

## Depends on

- [Abelian scheme](abelian-scheme.md)

## Proof depends on

- [Localization at a height-one prime is a DVR](../../RingTheory/valuation-rings/discrete-valuation-rings-at-height-one-primes/is-discrete-valuation-ring-of-height-eq.md),
  for the discrete valuation rings at the points of codimension one of $S$, localizations of a
  noetherian integrally closed domain on an integral affine open subscheme, over which the expansion
  of 1 first extends the homomorphism; the extension across codimension two needs the further inputs
  listed under Expansion

## Expansion

A good expansion has pages for: the extension of homomorphisms of semi-abelian schemes over normal
bases (Faltings–Chai, chapter I), which cannot simply extend the homomorphisms of the torus parts
and of the abelian quotients, since these need not exist over the whole base when the toric rank
varies (for the Tate curve over a discrete valuation ring the toric rank is $0$ on the generic fibre
and $1$ on the special fibre; Mumford's introduction separates the case of constant toric rank): the
expansion first extends over the local rings of $S$ at points of codimension one, which are discrete
valuation rings, and then over $S$ by normality, or follows a source that proves the theorem for
varying toric rank, such as Robert, Proposition 3.1.21, after Faltings, Lemma 2.1, which extends a
homomorphism from a dense open subscheme of a normal locally noetherian base through Néron models
locally of finite type, the closure of the graph and Zariski's main theorem; and, for 2, the
semipositivity of the Hodge bundle of a semi-abelian scheme over a curve in characteristic zero,
through the variation of Hodge structure of the abelian part and the degeneration at the points
where $G$ is not abelian. No source stating 2 in this generality has been identified, and this plan
is not a proof of it.

## Sources

- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Ergebnisse der Mathematik (3) 22,
  Springer, 1990: chapter I.
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>:
  Proposition 3.1.21 and its proof (extension of homomorphisms of semi-abelian schemes from a dense
  open subscheme of a normal locally noetherian base).
- D. Mumford, "An analytic construction of degenerating abelian varieties over complete rings",
  Compositio Math. 24 (1972), 239–272, <http://www.numdam.org/item?id=CM_1972__24_3_239_0>:
  introduction (semi-abelian group schemes).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1 as `GlobalTheory.Published.SemiAbelianHomExtension` and 2 as
  `GlobalTheory.Published.SemiAbelianLieSeminegative`.
