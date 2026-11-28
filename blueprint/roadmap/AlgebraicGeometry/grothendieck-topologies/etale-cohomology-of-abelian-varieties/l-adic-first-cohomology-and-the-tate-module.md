# The ℓ-adic first cohomology of an abelian variety is the dual of its Tate module

Let $A$ be an [abelian variety](../../abelian-varieties/abelian-scheme.md) over a separably closed field $k$ and $\ell$ a
prime different from the characteristic of $k$. Write
$H^1(A_{\mathrm{et}}, \mathbb{Z}_\ell) = \varprojlim_m H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$,
with the maps induced by the reductions $\mathbb{Z}/\ell^{m+1}\mathbb{Z} \to \mathbb{Z}/\ell^m\mathbb{Z}$,
and $T_\ell A = \varprojlim_m A_{\ell^m}(k)$, with multiplication by $\ell$ as transition maps. There
is a canonical isomorphism of $\mathbb{Z}_\ell$-modules

$$H^1(A_{\mathrm{et}}, \mathbb{Z}_\ell) \xrightarrow{\ \sim\ } \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell),$$

the inverse of the map
$\iota \colon \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell) \to H^1(A_{\mathrm{et}}, \mathbb{Z}_\ell)$
induced by the epimorphism $\rho \colon \pi_1(A, 0) \to T_\ell A$ of
[Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md) (its item
3): $\iota(\psi)$ is the family, over $m$, of the classes of the homomorphisms
$(\psi \circ \rho) \bmod \ell^m \colon \pi_1(A, 0) \to \mathbb{Z}/\ell^m\mathbb{Z}$, through the
identification of $H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$ with
$\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/\ell^m\mathbb{Z})$. The map $\iota$ is
injective because $\rho$ is surjective; the theorem is that it is bijective.

This is Milne's Theorem 12.1 (a), which is stated for a separably closed field, with $\iota$ the
injection of the paragraph after it; his Remark 12.5 also says that Theorem 12.1 holds when $k$ is
only separably closed, with a reference to his *Étale Cohomology*, II 3.17.

Multiplication by $\ell$ maps $A_{\ell^{m+1}}(k)$ onto $A_{\ell^m}(k)$, as $\ell_A$ is finite, étale
and surjective and $k$ is separably closed; so the projection $T_\ell A \to A_{\ell^m}(k)$ is
surjective with kernel $\ell^m T_\ell A$, and $\psi \mapsto (\psi_m)_m$, with $\psi_m$ the map
$A_{\ell^m}(k) \to \mathbb{Z}/\ell^m\mathbb{Z}$ induced by $\psi$ modulo $\ell^m$, identifies
$\operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell)$ with
$\varprojlim_m \operatorname{Hom}(A_{\ell^m}(k), \mathbb{Z}/\ell^m\mathbb{Z})$, with the transition maps of
[First étale cohomology of an abelian variety with finite coefficients](first-etale-cohomology-with-finite-coefficients.md).
As $(\psi \circ \rho) \bmod \ell^m = \psi_m \circ \rho_{\ell^m}$, the map $\iota$ is the limit of the
injective maps $\iota_m \colon f \mapsto f \circ \rho_{\ell^m}$ of that page, which are compatible with
the transition maps. Each $\iota_m$ is bijective. With $g$ the dimension of $A$, its source has
$\ell^{2gm}$ elements, as $A_{\ell^m}(k)$ has $\ell^{2gm}$ elements and a finite abelian group killed by
$\ell^m$ has as many homomorphisms to $\mathbb{Z}/\ell^m\mathbb{Z}$ as elements. Its target is
$\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/\ell^m\mathbb{Z})$, which is in bijection with
$\operatorname{Pic}(A)_{\ell^m}$, as $A$ is complete, connected and nonsingular, and
$\operatorname{Pic}(A)_{\ell^m}$ has $\ell^{2gm}$ elements. An injective map between finite sets with the
same number of elements is bijective, and a limit of bijections is a bijection. Milne's proof of
Theorem 12.1 obtains the rank $2g$ of the first cohomology instead from his Lemma 12.2 on graded
algebras with a coproduct, the Künneth formula and the vanishing of cohomology above degree $2g$; the
count through the Picard group follows his Lemma III.9.2.

## Depends on

- [Abelian scheme](../../abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [The étale fundamental group and first étale cohomology with finite coefficients](../etale-fundamental-group-and-first-cohomology.md),
  for the étale cohomology groups $H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$ and their
  identification with $\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/\ell^m\mathbb{Z})$
- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for the
  epimorphism $\rho \colon \pi_1(A, 0) \to T_\ell A$

## Proof depends on

- [First étale cohomology of an abelian variety with finite coefficients](first-etale-cohomology-with-finite-coefficients.md),
  for the compatibility of the maps $\iota_m$ with the transition maps
- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for the
  injectivity of the maps $\iota_m$ (its item 4)
- [Cyclic étale coverings and torsion line bundles](../cyclic-etale-coverings-and-torsion-line-bundles.md),
  for the bijection between $\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/\ell^m\mathbb{Z})$
  and $\operatorname{Pic}(A)_{\ell^m}$ (its item 1)
- [Torsion in the Picard group of an abelian variety](torsion-in-the-picard-group.md), for the
  $\ell^{2gm}$ elements of $\operatorname{Pic}(A)_{\ell^m}$
- [Isogenies of abelian schemes](../../abelian-varieties/isogenies-of-abelian-schemes.md), for $\ell_A$ finite, étale and
  surjective (its item 2) and the $\ell^{2gm}$ points of $A_{\ell^m}(k)$ (its item 3)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 7.3, p. 34; Theorem 12.1 (a) and the paragraph after it, p. 55, and
  its proof, p. 56; Remark 12.5, p. 56; Chapter III, Lemma 9.2, p. 114.
- J. S. Milne, *Lectures on Étale Cohomology*, course notes, version 2.21 (2013), <https://www.jmilne.org/math/CourseNotes/LEC.pdf>: §19, "Sheaves of $\mathbb{Z}_\ell$-modules", the convention
  $H^r(X, \mathbb{Z}_\ell) = \varprojlim H^r(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z})$, pp. 123–124.
- J. S. Milne, *Étale Cohomology*, Princeton University Press, 1980: II 3.17, as cited by Milne,
  *Abelian Varieties*, p. 56 (not read).
