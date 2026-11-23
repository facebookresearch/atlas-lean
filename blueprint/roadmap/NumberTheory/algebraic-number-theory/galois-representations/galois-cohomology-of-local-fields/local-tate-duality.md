# Local Tate duality

Let $k$ be a finite extension of $\mathbb{Q}_p$ with absolute Galois group $G_k$, let $A$ be a finite
discrete $G_k$-module and let $A' = \operatorname{Hom}(A, \mu)$ be its dual, where $\mu$ is the group of
roots of unity of $\bar k$ and $G_k$ acts on $A'$ by $(\sigma f)(a) = \sigma(f(\sigma^{-1} a))$. For
$0 \le i \le 2$, the cup product followed by the canonical isomorphism
$H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$,

$$H^i(k, A') \times H^{2-i}(k, A) \xrightarrow{\ \cup\ } H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z},$$

is a perfect pairing of finite groups: it induces isomorphisms
$H^i(k, A') \to H^{2-i}(k, A)^* = \operatorname{Hom}(H^{2-i}(k, A), \mathbb{Q}/\mathbb{Z})$.

If $\ell^r A = 0$, then $A' = \operatorname{Hom}(A, \mu_{\ell^r})$, which is isomorphic to the Tate twist
$\operatorname{Hom}_{\mathbb{Z}/\ell^r}(A, \mathbb{Z}/\ell^r\mathbb{Z})(1)$, and the pairing takes values in
$H^2(k, \mu_{\ell^r}) \cong \mathbb{Z}/\ell^r\mathbb{Z} \subset \mathbb{Q}/\mathbb{Z}$.

## Depends on

- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$ and $H^2(k, \mu_{\ell^r}) \cong \mathbb{Z}/\ell^r\mathbb{Z}$
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for the finiteness of the groups
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cup products
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the twist $(1)$

## Proof depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the abstract duality theorem of a profinite group of strict cohomological dimension $2$ with dualizing module, and for duality relative to a class formation
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for $\operatorname{scd}(G_k) = 2$
- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for the surjections $K^\times/K^{\times \ell} \to G_K^{\mathrm{ab}}/\ell$ over the finite extensions $K/k$, which give the vanishing of the dualizing modules $D_0$ and $D_1$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the class formation $(G_k, \bar k^\times)$ given by the invariant maps (its item 2)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.2.6) Theorem (Tate
  duality: "Let $k$ be a $p$-adic local field. Let $A$ be a finite $G_k$-module and set
  $A' = \operatorname{Hom}(A, \mu)$ … induces for $0 \le i \le 2$ an isomorphism of finite abelian groups
  $H^i(k, A') \to H^{2-i}(k, A)^*$") and its proof, a special case of the duality theorem (3.4.6) using
  (7.2.3) and (7.2.5), pp. 380–381; (7.2.9) and (7.2.10) for modules finitely generated as abelian groups.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Corollary 2.3, deduced from Theorem 1.8 (duality relative to a class formation) and
  Theorem 2.1.
- H. Darmon, F. Diamond, R. Taylor, "Fermat's Last Theorem", in *Current Developments in Mathematics*,
  1995, <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: Theorem 2.17 (a)–(c)
  (a summary of local duality, for the completions of $\mathbb{Q}$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states this duality for finite $\mathbb{Z}/\ell^r\mathbb{Z}$-modules as
  `Formalism.GaloisCohomology.LocalTateDualityK` (finite extensions of $\mathbb{Q}_\ell$) and
  `ReciprocityTheory.Gal.LocalTateDuality` (decomposition groups of number fields).
