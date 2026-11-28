# First étale cohomology of an abelian variety with finite coefficients

Let $A$ be an [abelian variety](../../abelian-varieties/abelian-scheme.md) of dimension $g$ over a separably closed field
$k$, and let $\ell$ be a prime different from the characteristic of $k$. For $m \ge 1$ let
$\iota_m \colon \operatorname{Hom}(A_{\ell^m}(k), \mathbb{Z}/\ell^m\mathbb{Z}) \to H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$,
$f \mapsto f \circ \rho_{\ell^m}$, be the injective map of
[Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md) (its item
4, for $n = \ell^m$). The maps $\iota_m$ are compatible with the reductions: for $m \ge 1$, the map
$H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^{m+1}\mathbb{Z}) \to H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$
induced by the reduction $\mathbb{Z}/\ell^{m+1}\mathbb{Z} \to \mathbb{Z}/\ell^m\mathbb{Z}$ sends
$\iota_{m+1}(f)$ to $\iota_m(f')$, where $f'$ is the unique homomorphism
$A_{\ell^m}(k) \to \mathbb{Z}/\ell^m\mathbb{Z}$ with $f'(\ell a) = f(a) \bmod \ell^m$ for all
$a \in A_{\ell^{m+1}}(k)$.

Multiplication by $\ell$ maps $A_{\ell^{m+1}}(k)$ onto $A_{\ell^m}(k)$, with kernel $A_\ell(k)$, as these
three groups have $\ell^{2g(m+1)}$, $\ell^{2gm}$ and $\ell^{2g}$ elements; and $f \bmod \ell^m$ vanishes
on $A_\ell(k)$, since $f(A_\ell(k))$ lies in $\ell^m \mathbb{Z}/\ell^{m+1}\mathbb{Z}$, so $f'$ exists and
is unique. Then $\rho_{\ell^m} = \ell \rho_{\ell^{m+1}}$ gives
$(f \bmod \ell^m) \circ \rho_{\ell^{m+1}} = f' \circ \rho_{\ell^m}$, while the identification of $H^1$
with homomorphisms from $\pi_1(A, 0)$ is natural in the coefficients.

## Depends on

- [Abelian scheme](../../abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [The étale fundamental group and first étale cohomology with finite coefficients](../etale-fundamental-group-and-first-cohomology.md),
  for $H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$
- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for the
  maps $\iota_m$ and the homomorphisms $\rho_{\ell^m}$

## Proof depends on

- [Multiplication by n as a Galois covering](multiplication-by-n-as-a-galois-covering.md), for
  $\rho_{\ell^m} = \ell \rho_{\ell^{m+1}}$ (its item 2)
- [The étale fundamental group and first étale cohomology with finite coefficients](../etale-fundamental-group-and-first-cohomology.md),
  for $H^1 = \operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), -)$, natural in the coefficients (its item
  2)
- [Isogenies of abelian schemes](../../abelian-varieties/isogenies-of-abelian-schemes.md), for the $\ell^{2gm}$ points of
  $A_{\ell^m}(k)$ (its item 3)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 7.3, p. 34; the paragraph after Theorem 12.1, p. 55, which passes to
  the inverse limit over the coverings given by multiplication by $\ell^n$ and so obtains an
  injection $\operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell) \to H^1(A, \mathbb{Z}_\ell)$;
  Chapter III, the proof of Corollary 9.6, p. 115, which identifies
  $H^1(V_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$ with
  $\operatorname{Hom}(\pi_1(V, P), \mathbb{Z}/\ell^m\mathbb{Z})$ and passes to the limit over $m$.
