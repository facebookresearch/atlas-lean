# Cyclotomic character and Tate twists

Let $k$ be a field with separable closure $\bar k$ and absolute Galois group
$G_k = \operatorname{Gal}(\bar k/k)$, and let $\mu \subset \bar k^\times$ be the group of roots of unity.
The **cyclotomic character** is the continuous homomorphism

$$\chi_{\mathrm{cycl}} \colon G_k \to \prod_{\ell \ne \operatorname{char} k} \mathbb{Z}_\ell^\times$$

determined by $\sigma(\zeta) = \zeta^{\chi_{\mathrm{cycl}}(\sigma)}$ for all $\zeta \in \mu$ and
$\sigma \in G_k$, where for $\zeta^n = 1$ with $n$ prime to $\operatorname{char} k$ (for instance $n$ the order of $\zeta$, which is
prime to $\operatorname{char} k$) and $\alpha \in \prod_{\ell \ne \operatorname{char} k} \mathbb{Z}_\ell^\times$ one sets
$\zeta^\alpha = \zeta^a$ for any $a \in \mathbb{Z}$ with $a \equiv \alpha \bmod n$. Its component
$\chi_\ell \colon G_k \to \mathbb{Z}_\ell^\times$ for a prime $\ell \ne \operatorname{char} k$ is the
**$\ell$-adic cyclotomic character**; it describes the action of $G_k$ on the $\ell$-power roots of unity.

For a finite discrete $G_k$-module $A$ of order prime to $\operatorname{char} k$ and $i \in \mathbb{Z}$,
the **$i$-th Tate twist** $A(i)$ is the abelian group $A$ with the action
$\sigma \cdot a = \chi_{\mathrm{cycl}}(\sigma)^i \, \sigma(a)$. The same definition applies to direct limits
of such modules, with their discrete topology, and to inverse limits of them, with the limit topology. Then
$A(0) = A$ and $A(i + j) = A(i)(j)$, and for a prime $\ell \ne \operatorname{char} k$

$$\mathbb{Z}_\ell(i) = \varprojlim_m \mathbb{Z}/\ell^m\mathbb{Z}(i), \qquad
\mathbb{Q}_\ell/\mathbb{Z}_\ell(i) = \varinjlim_m \mathbb{Z}/\ell^m\mathbb{Z}(i):$$

these are $\mathbb{Z}_\ell$ and $\mathbb{Q}_\ell/\mathbb{Z}_\ell$ with $G_k$ acting through $\chi_\ell^i$ (the
scalar-character model). The geometric twist is different as a module, though isomorphic: the **Tate module of
$\mathbb{G}_m$** is $T_\ell(\mu) = \varprojlim_m \mu_{\ell^m}$, the limit over the $\ell$-th power maps, and
$\mu_{\ell^\infty} = \varinjlim_m \mu_{\ell^m}$. A choice of a compatible system $(\zeta_{\ell^m})_m$ of primitive
$\ell^m$-th roots of unity, $\zeta_{\ell^{m+1}}^\ell = \zeta_{\ell^m}$, gives isomorphisms
$\mathbb{Z}/\ell^m\mathbb{Z}(1) \cong \mu_{\ell^m}$, $1 \mapsto \zeta_{\ell^m}$, compatible in $m$, hence
$\mathbb{Z}_\ell(1) \cong T_\ell(\mu)$ and $\mathbb{Q}_\ell/\mathbb{Z}_\ell(1) \cong \mu_{\ell^\infty}$; another choice changes
them by a unit of $\mathbb{Z}_\ell$. Likewise $\mathbb{Z}/n\mathbb{Z}(i) \cong \mu_n^{\otimes i}$ for
$(n, \operatorname{char} k) = 1$ and $i \ge 1$ after choosing a primitive $n$-th root of unity. Statements that call
an isomorphism canonical, such as $H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$ for a $p$-adic field $k$, refer to the
geometric modules $\mu_n$, $\mu_{\ell^\infty}$ and $T_\ell(\mu)$.

For a finite-dimensional $\mathbb{Q}_\ell$-vector space $V$ with a continuous linear action of $G_k$,
$V(i) = V \otimes_{\mathbb{Z}_\ell} \mathbb{Z}_\ell(i)$, and $V^*(1)$ denotes the twist of the dual representation
$V^* = \operatorname{Hom}_{\mathbb{Q}_\ell}(V, \mathbb{Q}_\ell)$. The rational Tate module
$V_\ell(\mu) = T_\ell(\mu) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$ of $\mathbb{G}_m$ is a one-dimensional representation
on which $G_k$ acts through $\chi_\ell$; it is isomorphic to $\mathbb{Q}_\ell(1) = \mathbb{Z}_\ell(1) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$
through the choice above.

For a number field $F$ and a set $S$ of places of $F$ containing the archimedean places and the places
above $\ell$, the maximal extension $F_S$ of $F$ unramified outside $S$ contains all $\ell$-power roots of
unity, so $\chi_\ell$ factors through $\operatorname{Gal}(F_S/F)$ and the twists $\mathbb{Z}_\ell(i)$ and
$\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$ are modules over that group.

## Depends on

- [The ring of p-adic integers](../../p-adic-numbers/p-adic-integers.md), for $\mathbb{Z}_\ell$ and its units, the values of the cyclotomic character

## Proof depends on

- [Cyclotomic fields are unramified at primes not dividing $m$](../cyclotomic-fields/ramification-and-inertia-in-cyclotomic-fields/is-unramified-in-of-not-dvd.md), applied to $\mathbb{Q}(\mu_{\ell^n})$, so that $F(\mu_{\ell^n}) = F \cdot \mathbb{Q}(\mu_{\ell^n})$ is unramified outside the places above $\ell$ and the archimedean places

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren der
  mathematischen Wissenschaften 323, Springer, 2008; electronic edition, version 2.3 (May 2020),
  <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VII, §3, (7.3.6) Definition (the
  cyclotomic character and the Tate twist $A(i)$, with its extension to direct and projective limits) and
  the remarks after it on p. 398 ($A(i + j) = A(i)(j)$, $\mathbb{Z}/n\mathbb{Z}(i) \cong \mu_n^{\otimes i}$, $\mathbb{Z}_\ell(i)$ and
  $\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$); (8.3.4) Proposition ($\mu_n \subseteq k_S$ for $n \in \mathbb{N}(S)$).
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school lectures, Honolulu, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>:
  §2.1.2 ($T_p(A) = \varprojlim A[p^n](\bar K)$ and Examples 2.1: for $A = \mathbb{G}_m$, $V = \mathbb{Q}_p(1)$) and
  §2.1.3 (the twisted dual $V^*(1)$ of a $p$-adic representation).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the twists $\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)$ and $\mathbb{Z}_\ell(e + 1)$ of
  $\operatorname{Gal}(F_S/F)$-modules as `Formalism.GaloisCohomology.qzTw` and `zlTw`.
