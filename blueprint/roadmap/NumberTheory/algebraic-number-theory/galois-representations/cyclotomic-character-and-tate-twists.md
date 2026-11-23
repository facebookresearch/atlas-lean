# Cyclotomic character and Tate twists

Let $k$ be a field with separable closure $\bar k$ and absolute Galois group
$G_k = \operatorname{Gal}(\bar k/k)$, and let $\mu \subset \bar k^\times$ be the group of roots of unity.
The **cyclotomic character** is the continuous homomorphism

$$\chi_{\mathrm{cycl}} \colon G_k \to \prod_{\ell \ne \operatorname{char} k} \mathbb{Z}_\ell^\times$$

determined by $\sigma(\zeta) = \zeta^{\chi_{\mathrm{cycl}}(\sigma)}$ for all $\zeta \in \mu$ and
$\sigma \in G_k$, where for $\zeta^n = 1$ and $\alpha \in \prod_\ell \mathbb{Z}_\ell^\times$ one sets
$\zeta^\alpha = \zeta^a$ for any $a \in \mathbb{Z}$ with $a \equiv \alpha \bmod n$. Its component
$\chi_\ell \colon G_k \to \mathbb{Z}_\ell^\times$ for a prime $\ell \ne \operatorname{char} k$ is the
**$\ell$-adic cyclotomic character**; it describes the action of $G_k$ on the $\ell$-power roots of unity.

For a finite discrete $G_k$-module $A$ of order prime to $\operatorname{char} k$ and $i \in \mathbb{Z}$,
the **$i$-th Tate twist** $A(i)$ is the abelian group $A$ with the action
$\sigma \cdot a = \chi_{\mathrm{cycl}}(\sigma)^i \, \sigma(a)$. The same definition applies to direct limits
of such modules, with their discrete topology, and to inverse limits of them, with the limit topology. Then
$A(0) = A$ and $A(i + j) = A(i)(j)$; for $(n, \operatorname{char} k) = 1$ and $i \ge 1$,
$\mathbb{Z}/n\mathbb{Z}(i) \cong \mu_n^{\otimes i}$ and
$\mathbb{Z}/n\mathbb{Z}(-i) \cong \operatorname{Hom}(\mu_n^{\otimes i}, \mathbb{Z}/n\mathbb{Z})$; and for a
prime $\ell \ne \operatorname{char} k$,

$$\mathbb{Z}_\ell(i) = \varprojlim_m \mathbb{Z}/\ell^m\mathbb{Z}(i), \qquad
\mathbb{Q}_\ell/\mathbb{Z}_\ell(i) = \varinjlim_m \mathbb{Z}/\ell^m\mathbb{Z}(i),$$

the second a discrete $G_k$-module isomorphic to $\mathbb{Q}_\ell/\mathbb{Z}_\ell$ on which $G_k$ acts
through $\chi_\ell^i$. For a finite-dimensional $\mathbb{Q}_\ell$-vector space $V$ with a continuous linear
action of $G_k$, $V(i) = V \otimes_{\mathbb{Z}_\ell} \mathbb{Z}_\ell(i)$, and $V^*(1)$ denotes the
twist of the dual representation $V^* = \operatorname{Hom}_{\mathbb{Q}_\ell}(V, \mathbb{Q}_\ell)$; in
particular $\mathbb{Q}_\ell(1) = \mathbb{Z}_\ell(1) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$ is the
$\ell$-adic cyclotomic character.

For a number field $F$ and a set $S$ of places of $F$ containing the archimedean places and the places
above $\ell$, the maximal extension $F_S$ of $F$ unramified outside $S$ contains all $\ell$-power roots of
unity, so $\chi_\ell$ factors through $\operatorname{Gal}(F_S/F)$ and the twists $\mathbb{Z}_\ell(i)$ and
$\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$ are modules over that group.

## Proof depends on

- [Cyclotomic fields are unramified at primes not dividing $m$](../cyclotomic-fields/ramification-and-inertia-in-cyclotomic-fields/is-unramified-in-of-not-dvd.md), applied to $\mathbb{Q}(\mu_{\ell^n})$, so that $F(\mu_{\ell^n}) = F \cdot \mathbb{Q}(\mu_{\ell^n})$ is unramified outside the places above $\ell$ and the archimedean places

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren der
  mathematischen Wissenschaften 323, Springer, 2008; electronic edition, version 2.3 (May 2020),
  <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VII, §3, (7.3.6) Definition (the
  cyclotomic character and the Tate twist $A(i)$, with its extension to direct and projective limits) and
  the remarks after it on p. 398 ($A(i + j) = A(i)(j)$, $\mathbb{Z}/n\mathbb{Z}(\pm i)$, $\mathbb{Z}_\ell(i)$ and
  $\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$); (8.3.4) Proposition ($\mu_n \subseteq k_S$ for $n \in \mathbb{N}(S)$).
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school lectures, Honolulu, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>:
  §2.1.3 and Examples 2.1 ($\mathbb{Q}_p(1)$ and the twisted dual $V^*(1)$ of a $p$-adic representation).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the twists $\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)$ and $\mathbb{Z}_\ell(e + 1)$ of
  $\operatorname{Gal}(F_S/F)$-modules as `Formalism.GaloisCohomology.qzTw` and `zlTw`.
