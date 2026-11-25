# Local Euler characteristic formula

Let $k$ be a finite extension of $\mathbb{Q}_p$ with ring of integers $\mathcal{O}_k$ and residue field of
$q$ elements, and let $\lVert x \rVert_k = q^{-v_k(x)}$ be its normalized absolute value. For every finite
discrete $G_k$-module $A$, of order $a$,

$$\chi(k, A) = \frac{\# H^0(k, A) \cdot \# H^2(k, A)}{\# H^1(k, A)} = \lVert a \rVert_k
= (\mathcal{O}_k : a\mathcal{O}_k)^{-1}.$$

Equivalently, if $A$ is $\ell$-primary, then $\# H^1(k, A) = \# H^0(k, A) \cdot \# H^2(k, A)$ when
$\ell \ne p$, and $\# H^1(k, A) = \# H^0(k, A) \cdot \# H^2(k, A) \cdot (\# A)^{[k : \mathbb{Q}_p]}$ when
$\ell = p$. The groups are finite by the finiteness theorem below.

## Depends on

- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for the finiteness of $H^i(k, A)$

## Proof depends on

- [Local Tate duality](local-tate-duality.md), which identifies $h(K, \mathbb{Z}/\ell\mathbb{Z})^*$ with $h(K, \mu_\ell)$ in Serre's theorem
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for the Kummer description of $H^i(K, \mu_\ell)$ over finite Galois extensions $K/k$
- [Induction from cyclic subgroups in Grothendieck groups of modular representations](../../../../GroupTheory/characters-of-finite-groups/induction-from-cyclic-subgroups.md), which reduces the formula to cyclic Galois groups of order prime to $\ell$
- [The p-adic exponential on a neighbourhood of zero](../../../p-adic-numbers/p-adic-exponential.md), for the logarithm identifying a group of higher principal units with an ideal of $\mathcal{O}_K$
- [Normal basis theorem](../../../../FieldTheory/galois-theory/normal-basis-theorem.md), for an element $\theta$ generating a normal basis of $K$ over $k$, which may be taken in $\mathcal{O}_K$: then $M = \bigoplus_{\sigma \in G} \mathcal{O}_k \sigma\theta$ is a $\mathbb{Z}_p[G]$-submodule of finite index in $\mathcal{O}_K$, isomorphic to $\mathcal{O}_k[G]$, with $M/pM \cong \mathbb{F}_p[G]^{[k : \mathbb{Q}_p]}$, which computes the term coming from $\mathcal{O}_K$ (NSW, proof of (7.3.2); Milne, proof of Lemma I.2.11, where it appears as $K \cong \mathbb{Q}_p[G]^{[k : \mathbb{Q}_p]}$); no integral normal basis of $\mathcal{O}_K$ is used
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the Hochschild–Serre spectral sequence and the vanishing of the cohomology of a finite group of order prime to $\ell$ on $\ell$-primary modules

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VII, §3, the
  definition of $\chi(k, A)$ before (7.3.1); (7.3.1) Theorem (Tate: $\chi(k, A) = \lVert a \rVert_k$ for $A$
  of order $a$ prime to $\operatorname{char}(k)$) with the footnote normalizing $\lVert x \rVert_k = q^{-v(x)}$;
  its proof through (7.3.2) Theorem (Serre), (7.3.3) and (7.3.4) Lemmas, using the normal basis theorem and
  the logarithm on higher principal units, pp. 391–396.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 2.8 ($\chi(G, M) = (R : mR)^{-1}$) with Lemmas 2.9–2.12.
- H. Darmon, F. Diamond, R. Taylor, "Fermat's Last Theorem", 1995,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: Theorem 2.17 (d).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the formula for finite $\mathbb{Z}/\ell^r\mathbb{Z}$-modules as
  `Formalism.GaloisCohomology.LocalEulerCharK` and `ReciprocityTheory.Gal.LocalEulerChar`.
