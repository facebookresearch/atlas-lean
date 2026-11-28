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
- [Cup products for profinite groups](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cup-products.md), for cup products
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the twist $(1)$

## Proof depends on

- [Dualizing module of a p-adic field](dualizing-module-of-a-p-adic-field.md), for the identification of the dualizing module of $G_k$ with $\mu$, under which the duality takes values in $H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$
- [Dualizing modules and the abstract duality theorems](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/dualizing-modules-and-duality-theorems.md), for the duality theorem (3.4.6): for a profinite group $G$ with $\operatorname{cd}_P G = n < \infty$ such that $D_i(\mathbb{Z}/p\mathbb{Z}) = 0$ for $p \in P$ and $i < n$, cup product and the trace give $H^i(G, \operatorname{Hom}(A, D_P)) \cong H^{n-i}(G, A)^*$ for every finite $P$-torsion module $A$; with Remark 1 after (3.4.3), which allows any isomorphism $H^n(G, D_P) \cong \mathbb{Q}_P/\mathbb{Z}_P$ in place of the trace
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for $\operatorname{cd}_\ell(G_k) = 2$ for every prime $\ell$
- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for the surjections $K^\times/K^{\times \ell} \to G_K^{\mathrm{ab}}/\ell$ over the finite extensions $K/k$, which give $D_1(\mathbb{Z}/\ell\mathbb{Z}) = \varinjlim_K H^1(K, \mathbb{Z}/\ell\mathbb{Z})^* = 0$; and $D_0(\mathbb{Z}/\ell\mathbb{Z}) = 0$ because every finite extension has finite extensions of degree divisible by $\ell$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.2.6) Theorem (Tate
  duality: "Let $k$ be a $p$-adic local field. Let $A$ be a finite $G_k$-module and set
  $A' = \operatorname{Hom}(A, \mu)$ … induces for $0 \le i \le 2$ an isomorphism of finite abelian groups
  $H^i(k, A') \to H^{2-i}(k, A)^*$") and its proof, a special case of the duality theorem (3.4.6) once the
  dualizing module is identified with $\mu$ by (7.2.4), after checking $D_0(\mathbb{Z}/p\mathbb{Z}) = 0$ and, by the local
  reciprocity law (7.2.3), $D_1(\mathbb{Z}/p\mathbb{Z}) = 0$, pp. 380–381; (7.2.9) and (7.2.10) for modules finitely
  generated as abelian groups.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Corollary 2.3 (the statement).
- H. Darmon, F. Diamond, R. Taylor, "Fermat's Last Theorem", in *Current Developments in Mathematics*,
  1995, <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: Theorem 2.17 (a)–(c)
  (a summary of local duality, for the completions of $\mathbb{Q}$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states this duality for finite $\mathbb{Z}/\ell^r\mathbb{Z}$-modules as
  `Formalism.GaloisCohomology.LocalTateDualityK` (finite extensions of $\mathbb{Q}_\ell$) and
  `ReciprocityTheory.Gal.LocalTateDuality` (decomposition groups of number fields).
