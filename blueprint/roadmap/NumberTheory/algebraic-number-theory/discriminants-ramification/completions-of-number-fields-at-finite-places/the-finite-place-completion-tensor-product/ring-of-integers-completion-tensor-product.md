# Base change of the ring of integers to a finite completion

Let $L/K$ be an extension of number fields, with rings of integers $\mathcal{O}_K \subseteq \mathcal{O}_L$, let $v$ be a
finite place of $K$, with completion $K_v$ and valuation ring $\mathcal{O}_v \subset K_v$, and for each finite place
$w$ of $L$ [over $v$](../places-of-a-number-field-extension-lying-over-a/places-over.md) let $\mathcal{O}_w$ be the valuation ring
of the completion $L_w$, an $\mathcal{O}_v$-algebra by the
[restriction of the completion map](../valuation-formula-for-maps-between-finite-place/adic-completion-integers-map.md)
$\mathcal{O}_v \to \mathcal{O}_w$, which is [compatible](../adic-completion-integers-map-algebra-map.md) with $\mathcal{O}_K \to \mathcal{O}_L$.
Then the map

$$\mathcal{O}_v \otimes_{\mathcal{O}_K} \mathcal{O}_L \to \prod_{w \mid v} \mathcal{O}_w, \qquad x \otimes y \mapsto (x y)_w,$$

is an isomorphism of $\mathcal{O}_v$-algebras, and $\mathcal{O}_v$ and the $\mathcal{O}_w$ are complete discrete valuation rings.

This node is still to be broken down. Its map is the restriction of the isomorphism of the
[base change to a finite completion](completion-tensor-product-alg-equiv.md), but the field isomorphism alone does not
identify the integral orders: the proper subring $\{(a, b) \in \mathbb{Z}_p^2 : a \equiv b \pmod p\}$ of $\mathbb{Z}_p^2$ has the same
ring of fractions $\mathbb{Q}_p^2$. A good expansion proves it in three steps, with $\mathfrak{p}$ the prime ideal of $v$ and
$\mathfrak{P}_w$ that of $w$:

- $\mathcal{O}_v \otimes_{\mathcal{O}_K} \mathcal{O}_L$ is the $\mathfrak{p}$-adic completion $\varprojlim_N \mathcal{O}_L / \mathfrak{p}^N \mathcal{O}_L$ of the
  finitely generated module $\mathcal{O}_L$ over the Noetherian ring $\mathcal{O}_K$ (in Mathlib,
  `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` gives this for the module), and $\mathcal{O}_v$ is the
  $\mathfrak{p}$-adic completion of $\mathcal{O}_K$;
- by [unique factorisation](../../../../../RingTheory/dedekind-domains/ideal-unique-factorization.md),
  $\mathfrak{p} \mathcal{O}_L = \prod_{w \mid v} \mathfrak{P}_w^{e_w}$, where the exponents $e_w \ge 1$ are the ramification indices; the
  ideals $\mathfrak{P}_w^{N e_w}$ are pairwise comaximal, so their intersection is their product $\mathfrak{p}^N \mathcal{O}_L$, and the
  [Chinese remainder theorem](../../../../../RingTheory/ideals-and-constructions/chinese-remainder-theorem-for-polynomial-quotien/quotient-inf-alg-equiv-pi-quotient.md)
  gives $\mathcal{O}_L / \mathfrak{p}^N \mathcal{O}_L \cong \prod_{w \mid v} \mathcal{O}_L / \mathfrak{P}_w^{N e_w}$, compatibly in $N$;
- the powers $\mathfrak{P}_w^{N e_w}$ are cofinal among the powers of $\mathfrak{P}_w$, as $e_w \ge 1$, so the limit of
  $\mathcal{O}_L / \mathfrak{P}_w^{N e_w}$ is the $\mathfrak{P}_w$-adic completion of $\mathcal{O}_L$, which is $\mathcal{O}_w$; the composite
  isomorphism is $x \otimes y \mapsto (x y)_w$.

## Depends on

- [Finite places lying over a finite place](../places-of-a-number-field-extension-lying-over-a/places-over.md), for the places $w \mid v$
- [Restriction of the completion map to the rings of integers](../valuation-formula-for-maps-between-finite-place/adic-completion-integers-map.md), for the maps $\mathcal{O}_v \to \mathcal{O}_w$
- [The completed integer map is compatible with the rings of integers](../adic-completion-integers-map-algebra-map.md), for the map on $\mathcal{O}_v \otimes_{\mathcal{O}_K} \mathcal{O}_L$

## Proof depends on

- [Base change to a finite completion as a product of completions](completion-tensor-product-alg-equiv.md), the isomorphism that this one restricts
- [Unique factorisation of ideals in a Dedekind domain](../../../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), for the factorisation of $\mathfrak{p} \mathcal{O}_L$
- [Chinese remainder theorem as an algebra isomorphism](../../../../../RingTheory/ideals-and-constructions/chinese-remainder-theorem-for-polynomial-quotien/quotient-inf-alg-equiv-pi-quotient.md), for $\mathcal{O}_L / \mathfrak{p}^N \mathcal{O}_L$

## Sources

- A. V. Sutherland, *Number Theory I*, MIT 18.785 lecture notes (Fall 2021), Lecture 11,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes11.pdf>, p. 10: Corollary 11.26
  ($B \otimes_A \hat{A}_{\mathfrak{p}} \cong \prod_{\mathfrak{q} \mid \mathfrak{p}} \hat{B}_{\mathfrak{q}}$ as $\hat{A}_{\mathfrak{p}}$-algebras, for a Dedekind domain
  $A$ and the integral closure $B$ of $A$ in a finite separable extension of its fraction field) and Remark 11.27 (the
  completion $\hat{A}_{\mathfrak{p}}$ is a complete discrete valuation ring, the valuation ring of $K_{\mathfrak{p}}$).
- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>, Chapter 8, Proposition 8.2 (p. 136): the field version,
  $L \otimes_K \hat{K} \cong \prod_{i=1}^{g} L_i$, with the map $a \otimes b \mapsto (a b)_i$ of its proof.
- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>, Section 2.4,
  item 4 (p. 20): the notation $M_{\mathfrak{p}} := M \otimes_{\mathfrak{o}} \mathfrak{o}_{\mathfrak{p}}$ for the completion of an $\mathfrak{o}$-lattice, used by
  the local pages.
