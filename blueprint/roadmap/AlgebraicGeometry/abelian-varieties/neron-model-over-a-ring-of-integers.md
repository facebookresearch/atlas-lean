# Néron model of an abelian variety over the ring of integers of a number field

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, and let $A$ be an
[abelian variety](abelian-scheme.md) of dimension $g$ over $L$. A **Néron model** of $A$ over
$\mathcal{O}_L$ is a [finite-type Néron model](../not-yet-classified/neron-models/finite-type-neron-model.md) of $A$ over
$\mathcal{O}_L$ and its fraction field $L$, that is, a smooth separated scheme $\mathcal{A}$ of finite
type over $\mathcal{O}_L$ with generic fibre identified with $A$ that represents the functor

$$S \longmapsto \operatorname{Hom}_L(S \times_{\operatorname{Spec} \mathcal{O}_L} \operatorname{Spec} L,\ A)$$

on smooth $\mathcal{O}_L$-schemes $S$: every morphism from the generic fibre of a smooth
$\mathcal{O}_L$-scheme $S$ to $A$ extends uniquely to an $\mathcal{O}_L$-morphism $S \to \mathcal{A}$,
with a commutative [group structure](../not-yet-classified/neron-models/group-structure.md) for which the identification of its
generic fibre with $A$ is a homomorphism.
This is the definition of the [Néron model over a discrete valuation ring](neron-model.md), with
$\mathcal{O}_L$ in place of the discrete valuation ring; by the Yoneda lemma a Néron model is unique
up to unique isomorphism.

**Theorem.** Let $A$ be an abelian variety of dimension $g$ over $L$.

1. $A$ has a Néron model $\mathcal{A}$ over $\mathcal{O}_L$.
2. For every maximal ideal $\mathfrak{p}$ of $\mathcal{O}_L$, the base change
   $\mathcal{A} \times_{\mathcal{O}_L} \operatorname{Spec} \mathcal{O}_{L,\mathfrak{p}}$ is the Néron
   model of $A$ over the discrete valuation ring $\mathcal{O}_{L,\mathfrak{p}}$.
3. There is a nonzero $f \in \mathcal{O}_L$ such that
   $\mathcal{A} \times_{\mathcal{O}_L} \operatorname{Spec} \mathcal{O}_L[1/f]$ is an abelian scheme; so
   $A$ has good reduction at every maximal ideal of $\mathcal{O}_L$ not containing $f$.
4. With $\varepsilon$ the zero section of $\mathcal{A}$, the $\mathcal{O}_L$-module
   $\omega_{\mathcal{A}} = \varepsilon^* \Omega^g_{\mathcal{A}/\mathcal{O}_L}$ is invertible, and
   $\omega_{\mathcal{A}} \otimes_{\mathcal{O}_L} L$ is the line $H^0(A, \Omega^g_{A/L})$ of invariant
   $g$-forms on $A$; so, for every embedding $\sigma : L \to \mathbb{C}$,
   $\omega_{\mathcal{A}} \otimes_\sigma \mathbb{C}$ is the space of holomorphic $g$-forms on
   $A_\sigma(\mathbb{C})$, where $A_\sigma$ is the base change of $A$ along $\sigma$.

## Depends on

- [Néron model of an abelian variety](neron-model.md), for the Néron model over a discrete valuation
  ring and good reduction
- [Abelian scheme](abelian-scheme.md), for abelian varieties and abelian schemes
- [Finite-type Néron model](../not-yet-classified/neron-models/finite-type-neron-model.md), over
  $\mathcal{O}_L$ and its fraction field $L$, for the Néron model $\mathcal{A}$
- [Group structure on a Néron model](../not-yet-classified/neron-models/group-structure.md), for the
  group law of $\mathcal{A}$ and its zero section $\varepsilon$

## Proof depends on

- [Néron model of an abelian variety](neron-model.md), for the existence of the Néron models over
  the local rings $\mathcal{O}_{L,\mathfrak{p}}$
- [Abelian varieties are projective](abelian-varieties-are-projective.md), for a projective
  embedding of $A$, which spreads out with the group law over some $\mathcal{O}_L[1/f]$
- [Representing objects are unique up to isomorphism](../../CategoryTheory/categories-and-functors/uniqueness-of-representing-objects.md),
  for the uniqueness of the Néron model

## Expansion

This node is still to be broken down. A good expansion states and links:

- spreading out: an abelian scheme over $\mathcal{O}_L[1/f]$, for some nonzero $f$, with generic fibre
  $A$, obtained by extending a projective embedding of $A$ and its group law and using that smoothness
  and properness spread out;
- that an abelian scheme over a discrete valuation ring is the Néron model of its generic fibre
  (Conrad, Example 5.3, which cites Bosch, Lütkebohmert and Raynaud), and the analogue over
  $\mathcal{O}_L[1/f]$;
- the gluing of that abelian scheme with the Néron models over the local rings at the finitely many
  maximal ideals that contain $f$, and the local criterion: a smooth separated group scheme of finite
  type over $\mathcal{O}_L$ whose base change to every $\mathcal{O}_{L,\mathfrak{p}}$ is a Néron model
  is a Néron model over $\mathcal{O}_L$;
- the existence, over $\mathcal{O}_L$, of the finite-type Néron model with its group structure: the
  group law, inverse and unit of $A$ extend to $\mathcal{A}$ by the mapping property, applied to the
  smooth $\mathcal{O}_L$-schemes $\mathcal{A} \times_{\mathcal{O}_L} \mathcal{A}$, $\mathcal{A}$ and
  $\operatorname{Spec} \mathcal{O}_L$, and the group axioms and commutativity hold because they hold
  on generic fibres and extensions are unique;
- for item 4, the identification of $\varepsilon^* \Omega^g$ of a smooth group scheme of relative
  dimension $g$ with the top exterior power of the dual of its Lie algebra, and of the latter, over a
  field, with the invariant $g$-forms (Deligne, §1.2).

## Sources

- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: §1.2, p. 26, the line
  $\omega(A) = \bigwedge^g ((\operatorname{Lie} A)^\vee)$, its $\mathcal{O}$-form
  $\bigwedge^g ((\operatorname{Lie} A_{\mathcal{O}})^\vee)$ given by the Néron model $A_{\mathcal{O}}$
  of $A$ over the ring of integers $\mathcal{O}$ of $k$ (item (a)), and the space of holomorphic
  $g$-forms on $\iota A$ for a complex embedding $\iota$ (item (b)); p. 27, "Généralisation", the
  invertible sheaf $\omega(G)$ of a flat group scheme $G$ of relative dimension $g$, which is
  $\bigwedge^g ((\operatorname{Lie} G)^\vee)$ when $G$ is smooth.
- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 255, the Néron model $\mathcal{E}/R$ of an
  elliptic curve $E/K$ over the ring of integers $R$ of $K$, in the definition of $h(E/K)$.
- B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>: §5, p. 13, Definition 5.1 (Néron model
  over a discrete valuation ring), Theorem 5.2 (Néron's existence theorem) and Example 5.3 (an
  abelian scheme over a discrete valuation ring is the Néron model of its generic fibre).
- S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, Ergebnisse der Mathematik (3) 21,
  Springer, 1990, for Néron models over Dedekind bases; not read for this page.
