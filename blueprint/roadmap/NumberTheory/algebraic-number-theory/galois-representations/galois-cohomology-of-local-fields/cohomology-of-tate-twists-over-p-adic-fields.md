# Galois cohomology of Tate twists over a p-adic field

Let $k$ be a finite extension of $\mathbb{Q}_p$ of degree $d$, let $\ell$ be a prime and, for a nonzero integer
$r$, let

$$w_\ell^r = \max\{\ell^n : \text{the exponent of } \operatorname{Gal}(k(\mu_{\ell^n})/k) \text{ divides } r\},$$

so that $w_\ell^1 = \# \mu_{\ell^\infty}(k)$ and $w_\ell^r = w_\ell^{-r}$. Then, for every $i \in \mathbb{Z}$ and the discrete Tate twists
$\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$:

1. $H^0(k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(i)) \cong \mathbb{Q}_\ell/\mathbb{Z}_\ell$ for $i = 0$ and
   $\mathbb{Z}/w_\ell^i\mathbb{Z}$ for $i \ne 0$;
2. $H^1(k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(i))$ is isomorphic to
   $\mathbb{Z}/w_\ell^1\mathbb{Z} \oplus (\mathbb{Q}_\ell/\mathbb{Z}_\ell)^{d+1}$ if $i = 0$, to
   $(\mathbb{Q}_\ell/\mathbb{Z}_\ell)^{d+1}$ if $i = 1$, and to
   $\mathbb{Z}/w_\ell^{1-i}\mathbb{Z} \oplus (\mathbb{Q}_\ell/\mathbb{Z}_\ell)^d$ if $i \ne 0, 1$, when $\ell = p$;
   and to $\mathbb{Z}/w_\ell^1\mathbb{Z} \oplus \mathbb{Q}_\ell/\mathbb{Z}_\ell$ if $i = 0$, to
   $\mathbb{Q}_\ell/\mathbb{Z}_\ell$ if $i = 1$, and to $\mathbb{Z}/w_\ell^{1-i}\mathbb{Z}$ if $i \ne 0, 1$, when
   $\ell \ne p$;
3. $H^2(k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(i)) \cong \mathbb{Q}_\ell/\mathbb{Z}_\ell$ for $i = 1$, and $0$ for
   $i \ne 1$.

For the continuous cohomology of the compact twists $\mathbb{Z}_\ell(i)$, local duality gives
$H^j_{\mathrm{cts}}(G_k, \mathbb{Z}_\ell(i)) \cong H^{2-j}(k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(1-i))^\vee$, the
Pontryagin dual. In particular $H^2_{\mathrm{cts}}(G_k, \mathbb{Z}_\ell(i)) \cong
H^0(k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(1-i))^\vee$, which is finite of order $w_\ell^{1-i}$ for $i \ne 1$.

## Depends on

- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$ and $\mathbb{Z}_\ell(i)$
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for continuous cochain cohomology with compact coefficients

## Proof depends on

- [Local Tate duality](local-tate-duality.md), for $H^2$ and the duality between the twists
- [Local Euler characteristic formula](local-euler-characteristic-formula.md), for the Euler characteristics of $\mathbb{Z}/\ell\mathbb{Z}(j)$, which give the coranks of $H^1$
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for $\operatorname{cd}_\ell(G_k) = 2$
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^1(k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(1)) \cong k^\times \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell$
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for continuous cohomology as an inverse limit over finite levels and its ranks

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: the definition of $w_\ell^i$
  before (7.3.10); (7.3.10) Proposition (i)–(iii) and the Remark after it
  ($H^j_{\mathrm{cts}}(G_k, \mathbb{Z}_\ell(i)) \cong H^{2-j}(G_k, \mathbb{Q}_\ell/\mathbb{Z}_\ell(1-i))^\vee$),
  with its proof using (7.2.6) and (7.3.8), pp. 399–401.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the equality of the $\mathbb{Z}_\ell$-lengths of $H^2(\mathbb{Z}_\ell(e+1))$ and
  $H^0(\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e))$ at the places above $\ell$ as
  `Formalism.GaloisCohomology.TateLocalDualityH2Hypothesis`.
