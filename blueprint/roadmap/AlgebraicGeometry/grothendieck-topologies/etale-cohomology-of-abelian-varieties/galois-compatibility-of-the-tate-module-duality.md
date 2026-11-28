# Galois compatibility of the duality between ℓ-adic H¹ and the Tate module

This node is still to be broken down: the statement is precise, but its proof is not.

Let $A$ be an [abelian variety](../../abelian-varieties/abelian-scheme.md) over a field $k$, $K$ a separable closure of
$k$, $\ell$ a prime different from the characteristic of $k$, $A_K = A \times_k \operatorname{Spec} K$,
and let

$$\varphi \colon H^1(A_{K, \mathrm{et}}, \mathbb{Z}_\ell) \xrightarrow{\ \sim\ } \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell)$$

be the isomorphism of
[The ℓ-adic first cohomology of an abelian variety is the dual of its Tate module](l-adic-first-cohomology-and-the-tate-module.md)
for $A_K$, with $T_\ell A = \varprojlim_m A_{\ell^m}(K)$. An automorphism $\sigma$ of $K$ over $k$ acts
on each $H^1(A_{K, \mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$, hence on their limit, by inverse image
along the automorphism $\mathrm{id}_A \times \operatorname{Spec} \sigma$ of the scheme $A_K$, and on
$A(K)$, hence on $T_\ell A$, by $P \mapsto P \circ \operatorname{Spec} \sigma$, which applies $\sigma$ to
coordinates. Then $\varphi(\sigma x)(\sigma t) = \varphi(x)(t)$ for every $\sigma$, every
$x \in H^1(A_{K, \mathrm{et}}, \mathbb{Z}_\ell)$ and every $t \in T_\ell A$.

This is the degree-one case of Milne's Remark 12.5, which states that the isomorphism
$\bigwedge^* \operatorname{Hom}(T_\ell A, \mathbb{Z}_\ell) \to H^*(A_{k^{\mathrm{sep}}}, \mathbb{Z}_\ell)$
is compatible with the natural actions of $\operatorname{Gal}(k^{\mathrm{sep}}/k)$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the naturality of the classification of finite étale coverings and of the identification of $H^1$
  with homomorphisms from $\pi_1$ under an isomorphism of schemes that need not respect the structure
  morphism to $\operatorname{Spec} K$, here $\alpha = \mathrm{id}_A \times \operatorname{Spec} \sigma$,
  including the change of geometric base point;
- that $\alpha$ commutes with multiplication by $\ell^m$ on $A_K$ and conjugates the translation by
  a point $a \in A_{\ell^m}(K)$ into the translation by the image of $a$ under the action of
  $\sigma^{-1}$, so that inverse image along $\alpha$ carries the torsor attached to a homomorphism
  $f \colon A_{\ell^m}(K) \to \mathbb{Z}/\ell^m\mathbb{Z}$ to the torsor attached to $f$ composed with
  that action;
- the passage to the limit over $m$.

## Depends on

- [The ℓ-adic first cohomology of an abelian variety is the dual of its Tate module](l-adic-first-cohomology-and-the-tate-module.md),
  for the isomorphism $\varphi$
- [Galois Scheme Operator](../../not-yet-classified/geometric-adic-galois-operators/galois-scheme-operator.md),
  for the automorphism $\mathrm{id}_A \times \operatorname{Spec} \sigma$ of $A_K$
- [Map](../../../Algebra/not-yet-classified/tate-module/map.md), for the map of Tate modules induced
  by the action of $\sigma$ on $A(K)$

## Proof depends on

- [The étale fundamental group and first étale cohomology with finite coefficients](../etale-fundamental-group-and-first-cohomology.md),
  for the classification of finite étale coverings and the identification of $H^1$ with
  homomorphisms from $\pi_1$ (its items 1 and 2), whose naturality the expansion states
- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for the
  coverings given by multiplication by $\ell^m$, with their translations, and the classes
  $f \circ \rho_{\ell^m}$ (its items 1, 2 and 4)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 12.5, p. 56.
