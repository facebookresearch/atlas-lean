# Wiles's formula for Selmer groups

Let $F$ be a number field and $A$ a finite discrete $G_F$-module, with dual $A' = \operatorname{Hom}(A, \mu)$.
For each place $v$ of $F$ let $G_v \subseteq G_F$ be a decomposition group and $I_v \subseteq G_v$ its
inertia group ($I_v = G_v$ for archimedean $v$). A **collection of local conditions** for $A$ is a family
$\mathcal{L} = (L_v)_v$ of subgroups $L_v \subseteq H^1(G_v, A)$ such that
$L_v = H^1(G_v/I_v, A^{I_v}) = \ker(H^1(G_v, A) \to H^1(I_v, A))$ for almost all $v$. Its dual collection
$\mathcal{L}^D$ for $A'$ consists of the orthogonal complements $L_v^D$ of $L_v$ under the local duality
pairings $H^1(G_v, A) \times H^1(G_v, A') \to \mathbb{Q}/\mathbb{Z}$. The **Selmer groups** are

$$H^1_{\mathcal{L}}(F, A) = \ker\Bigl(H^1(G_F, A) \to \prod_v H^1(G_v, A)/L_v\Bigr), \qquad
H^1_{\mathcal{L}^D}(F, A') = \ker\Bigl(H^1(G_F, A') \to \prod_v H^1(G_v, A')/L_v^D\Bigr).$$

They are finite, and

$$\frac{\# H^1_{\mathcal{L}}(F, A)}{\# H^1_{\mathcal{L}^D}(F, A')}
= \frac{\# H^0(F, A)}{\# H^0(F, A')} \prod_v \frac{\# L_v}{\# H^0(F_v, A)},$$

where the product runs over all places of $F$, almost all of its factors are $1$, and $H^0(F_v, A) = A^{G_v}$
is the group of invariants also at the archimedean places (not the Tate group $\hat H^0$).

If $S$ is a finite set of places containing the archimedean places, the places above the primes dividing
$\# A$, the places where $A$ is ramified and those where $L_v$ is not the unramified subgroup, then
$H^1_{\mathcal{L}}(F, A)$ is the kernel of $H^1(G_S, A) \to \prod_{v \in S} H^1(F_v, A)/L_v$, and similarly for
$\mathcal{L}^D$.

## Depends on

- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the orthogonal complements at the non-archimedean places
- [Tate duality for the real numbers](../galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for the orthogonal complements at the archimedean places
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the unramified subgroups, which are exact annihilators of each other at the places prime to $\# A$, so that $\mathcal{L}^D$ is again a collection of local conditions
- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for the description through $G_S$

## Proof depends on

- [Poitou–Tate exact sequence](poitou-tate-exact-sequence.md)
- [Global Euler characteristic formula](global-euler-characteristic-formula.md)
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for $\# H^1(G_v/I_v, A^{I_v}) = \# H^0(F_v, A)$ at the finite places $v$ (at a complex place it fails: $H^1 = 0$ while $H^0 = A$)
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (8.7.8) Definition
  (collections of local conditions, $\mathcal{L}^D$ and the global groups) and the description through $G_S$
  that follows it, (8.7.9) Theorem (due to A. Wiles) and its proof, pp. 511–513, with the ordinary groups
  $H^0(k_\mathfrak{p}, A)$ in the formula.
- H. Darmon, F. Diamond, R. Taylor, "Fermat's Last Theorem", 1995,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: Theorem 2.18 (over $\mathbb{Q}$,
  with its proof from the Poitou–Tate sequence and the global Euler characteristic) and Theorem 2.19 (any
  number field), pp. 60–62.
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: Definitions 2.2–2.4 and
  Proposition 2.7 (the analogue for $p$-adic representations, attributed to Greenberg and Wiles).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the formula for $\mathbb{Z}/\ell^r\mathbb{Z}$-modules, $\ell \ne 2$, with local conditions at the places of a
  finite set $S$ containing the places above $\ell$, as `ReciprocityTheory.Gal.GreenbergWiles`.
