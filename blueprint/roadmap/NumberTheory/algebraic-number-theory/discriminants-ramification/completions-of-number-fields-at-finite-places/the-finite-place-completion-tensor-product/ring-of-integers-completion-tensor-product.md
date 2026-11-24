# Base change of the ring of integers to a finite completion

Let $L/K$ be an extension of number fields, with rings of integers $\mathcal{O}_K \subseteq \mathcal{O}_L$, let $v$ be a
finite place of $K$, with completion $K_v$ and valuation ring $\mathcal{O}_v \subset K_v$, and for each finite place
$w$ of $L$ over $v$ let $\mathcal{O}_w$ be the valuation ring of the completion $L_w$. Then the map

$$\mathcal{O}_v \otimes_{\mathcal{O}_K} \mathcal{O}_L \to \prod_{w \mid v} \mathcal{O}_w, \qquad x \otimes y \mapsto (x y)_w,$$

is an isomorphism of $\mathcal{O}_v$-algebras, and $\mathcal{O}_v$ and the $\mathcal{O}_w$ are discrete valuation rings.

This node is still to be broken down. It is the integral form of the
[base change to a finite completion](completion-tensor-product-alg-equiv.md), whose isomorphism it restricts. A good
expansion proves it in three steps: $\mathcal{O}_v \otimes_{\mathcal{O}_K} \mathcal{O}_L$ is the $\mathfrak{p}$-adic completion
$\varprojlim_N \mathcal{O}_L / \mathfrak{p}^N \mathcal{O}_L$ of the finitely generated $\mathcal{O}_K$-module $\mathcal{O}_L$, where
$\mathfrak{p}$ is the prime ideal of $v$; the factorisation $\mathfrak{p} \mathcal{O}_L = \prod_{w \mid v} \mathfrak{P}_w^{e_w}$ and the
[Chinese remainder theorem](../../../../../RingTheory/ideals-and-constructions/chinese-remainder-theorem-for-polynomial-quotien/quotient-inf-alg-equiv-pi-quotient.md)
give $\mathcal{O}_L / \mathfrak{p}^N \mathcal{O}_L \cong \prod_{w \mid v} \mathcal{O}_L / \mathfrak{P}_w^{N e_w}$; and the
$\mathfrak{P}_w$-adic completion of $\mathcal{O}_L$ is $\mathcal{O}_w$, compatibly with the isomorphism of completions.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Base change to a finite completion as a product of completions](completion-tensor-product-alg-equiv.md), the isomorphism that this one restricts
- [Chinese remainder theorem as an algebra isomorphism](../../../../../RingTheory/ideals-and-constructions/chinese-remainder-theorem-for-polynomial-quotien/quotient-inf-alg-equiv-pi-quotient.md), for $\mathcal{O}_L / \mathfrak{p}^N \mathcal{O}_L$

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>, Section 2.4,
  item 4 (p. 20): for an $\mathfrak{o}$-module $M$, "$M_{\mathfrak{p}} := M \otimes_{\mathfrak{o}} \mathfrak{o}_{\mathfrak{p}}$ is the
  completion of $M$ at $\mathfrak{p}$".
- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>, Chapter 8, Proposition 8.2 (p. 136): $L \otimes_K \hat{K} \cong \prod_{i=1}^{g} L_i$,
  the product of the completions of $L$ at the extensions of the absolute value of $K$.
