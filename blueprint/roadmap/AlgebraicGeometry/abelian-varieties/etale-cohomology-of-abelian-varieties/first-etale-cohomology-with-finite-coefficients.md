# First étale cohomology of an abelian variety with finite coefficients

Let $A$ be an [abelian variety](../abelian-scheme.md) of dimension $g$ over a separably closed field
$k$, and let $n \ge 1$ be an integer not divisible by the characteristic of $k$.

1. The injective map
   $\operatorname{Hom}(A_n(k), \mathbb{Z}/n\mathbb{Z}) \to H^1(A_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z})$,
   $f \mapsto f \circ \rho_n$, of
   [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md) (its item
   4) is bijective; both groups have $n^{2g}$ elements.
2. Let $\ell$ be a prime different from the characteristic of $k$ and $m \ge 1$. Under the
   bijections of 1 for $n = \ell^{m+1}$ and $n = \ell^m$, the map
   $H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^{m+1}\mathbb{Z}) \to H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$
   induced by the reduction $\mathbb{Z}/\ell^{m+1}\mathbb{Z} \to \mathbb{Z}/\ell^m\mathbb{Z}$
   corresponds to the map
   $\operatorname{Hom}(A_{\ell^{m+1}}(k), \mathbb{Z}/\ell^{m+1}\mathbb{Z}) \to \operatorname{Hom}(A_{\ell^m}(k), \mathbb{Z}/\ell^m\mathbb{Z})$
   that sends $f$ to the unique $f'$ with $f'(\ell a) = f(a) \bmod \ell^m$ for all
   $a \in A_{\ell^{m+1}}(k)$.

For 1, a finite abelian group killed by $n$ has as many homomorphisms to $\mathbb{Z}/n\mathbb{Z}$ as
elements, so the source has $n^{2g}$ elements. The target is
$\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/n\mathbb{Z})$, which is in bijection with
$\operatorname{Pic}(A)_n$, as $A$ is complete, connected and nonsingular, and
$\operatorname{Pic}(A)_n$ has $n^{2g}$ elements. An injective map between finite sets with the same
number of elements is bijective. For 2, $f \bmod \ell^m$ vanishes on the kernel $A_\ell(k)$ of
multiplication by $\ell$ from $A_{\ell^{m+1}}(k)$ onto $A_{\ell^m}(k)$, since $f(A_\ell(k))$ lies in
$\ell^m \mathbb{Z}/\ell^{m+1}\mathbb{Z}$, so $f'$ exists; and $\rho_{\ell^m} = \ell \rho_{\ell^{m+1}}$
gives $(f \bmod \ell^m) \circ \rho_{\ell^{m+1}} = f' \circ \rho_{\ell^m}$, while the identification of
$H^1$ with homomorphisms from $\pi_1(A, 0)$ is natural in the coefficients.

Milne's proof of Theorem 12.1 obtains the rank $2g$ of the first cohomology instead from his
Lemma 12.2 on graded algebras with a coproduct, the Künneth formula and the vanishing of cohomology
above degree $2g$; the count through the Picard group follows his Lemma III.9.2.

## Depends on

- [Abelian scheme](../abelian-scheme.md), for abelian varieties over a field
- [The étale fundamental group and first étale cohomology with finite coefficients](../../grothendieck-topologies/etale-fundamental-group-and-first-cohomology.md),
  for $H^1(A_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z})$
- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for the
  map of 1 and the homomorphisms $\rho_n$

## Proof depends on

- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for the
  injectivity of the map (its item 4) and $\rho_{\ell^m} = \ell \rho_{\ell^{m+1}}$ (its item 2)
- [The étale fundamental group and first étale cohomology with finite coefficients](../../grothendieck-topologies/etale-fundamental-group-and-first-cohomology.md),
  for $H^1 = \operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), -)$, natural in the coefficients (its item
  2)
- [Cyclic étale coverings and torsion line bundles](../../grothendieck-topologies/cyclic-etale-coverings-and-torsion-line-bundles.md),
  for the bijection between $\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/n\mathbb{Z})$ and
  $\operatorname{Pic}(A)_n$ (its item 1)
- [Torsion in the Picard group of an abelian variety](torsion-in-the-picard-group.md), for the
  $n^{2g}$ elements of $\operatorname{Pic}(A)_n$
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for the $n^{2g}$ points of
  $A_n(k)$ (its item 3)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 7.3, p. 34; Theorem 12.1, the paragraph after it, p. 55, and its proof,
  p. 56; Chapter III, Lemma 9.2, p. 114, and the proof of Corollary 9.6, p. 115.
