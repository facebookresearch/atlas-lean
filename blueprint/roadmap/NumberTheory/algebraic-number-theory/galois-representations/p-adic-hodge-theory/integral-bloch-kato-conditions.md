# Integral Bloch–Kato conditions and their duality

Let $K$ be a finite extension of $\mathbb{Q}_p$, $\ell$ a prime, $T$ a free $\mathbb{Z}_\ell$-module of finite rank with a
continuous action of $G_K$, and $V = T \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$; if $\ell = p$, assume $V$ is de Rham. Let
$T^* = \operatorname{Hom}_{\mathbb{Z}_\ell}(T, \mathbb{Z}_\ell)$, so that $T^*(1)$ is a lattice in $V^*(1)$, and let
$A' = T^* \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell/\mathbb{Z}_\ell(1) = V^*(1)/T^*(1)$. For $* \in \{e, f, g\}$:

- the **integral Bloch–Kato subgroup** $H^1_*(K, T)$ is the inverse image of $H^1_*(K, V)$ under
  $\iota \colon H^1(K, T) \to H^1(K, V)$; it contains the torsion subgroup of $H^1(K, T)$;
- the **divisible Bloch–Kato subgroup** $H^1_*(K, A')$ is the image of $H^1_*(K, V^*(1))$ under the map induced by
  the projection $V^*(1) \to A'$, which is also the image of $H^1_*(K, T^*(1)) \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell$.

Here the rational groups are as follows. For $\ell = p$, $H^1_e(K, V) \subseteq H^1_f(K, V) \subseteq H^1_g(K, V)$ are
the Bloch–Kato subgroups of the $p$-adic representation $V$. For $\ell \ne p$ they are defined for the
$\ell$-adic representation $V$ by $H^1_e(K, V) = 0$, $H^1_g(K, V) = H^1(K, V)$ and
$H^1_f(K, V) = \ker(H^1(K, V) \to H^1(K^{\mathrm{nr}}, V))$. These descriptions concern $V$, not the lattice: for
$\ell \ne p$, $H^1_e(K, T)$ is the torsion subgroup of $H^1(K, T)$, which can be nonzero, and $H^1_g(K, T) = H^1(K, T)$.
For instance, for $K = \mathbb{Q}_7$, $\ell = 3$ and $T = \mathbb{Z}_3(1)$, the group $H^0(K, V/T)$ is isomorphic to
$\mu_{3^\infty}(\mathbb{Q}_7)$, which is nontrivial since $\mu_3 \subset \mathbb{Q}_7$, while $H^0(K, V) = 0$; the boundary map of
$0 \to T \to V \to V/T \to 0$ embeds it into the torsion of $H^1(K, T)$, so $H^1_e(K, T) \ne 0$. Then, under the perfect pairing

$$H^1(K, T) \times H^1(K, A') \xrightarrow{\ \cup\ } H^2(K, \mathbb{Q}_\ell/\mathbb{Z}_\ell(1)) \cong \mathbb{Q}_\ell/\mathbb{Z}_\ell,$$

$H^1_e(K, T)$ and $H^1_g(K, A')$ are the exact annihilators of each other, and so are $H^1_g(K, T)$ and
$H^1_e(K, A')$, and $H^1_f(K, T)$ and $H^1_f(K, A')$.

Flach uses a finite-level form of the $f$/$f$ case in one situation: for an elliptic curve $E$ over $\mathbb{Q}$, the
symmetric square $V = \mathrm{Sym}^2 H^1_{\mathrm{et}}(E_{\bar{\mathbb{Q}}}, \mathbb{Q}_p)$ with its natural lattice
$T = \mathrm{Sym}^2 H^1_{\mathrm{et}}(E_{\bar{\mathbb{Q}}}, \mathbb{Z}_p)$ and $A = V/T$, the twists $T(2)$ and $A(1)$, and the primes
$r$, where he identifies the Kummer dual of the twist $V(1)$ with $V(2)$. There, for $n \ge 1$, the inverse image of
the divisible condition under the inclusion $i(n) \colon A(1)[p^n] \hookrightarrow A(1)$ and the image of the lattice
condition under the projection $\mathrm{pr}(n) \colon T(2) \to T(2)/p^n$ are orthogonal complements under the local Tate
duality pairing of $H^1(\mathbb{Q}_r, A(1)[p^n])$ with $H^1(\mathbb{Q}_r, T(2)/p^n)$, which Flach derives as a formal
consequence of Bloch–Kato's Proposition 3.8. For an arbitrary $G_K$-stable lattice $T$, the theorem above pairs $T$
with the divisible quotient $A' = V^*(1)/T^*(1)$ of its **dual** lattice; finite-level forms for such lattices would
follow from it by the same functoriality along the inclusions of the $\ell^n$-torsion and the reductions modulo
$\ell^n$, not from Flach's case, and they are not stated on this page.

## Depends on

- [Bloch–Kato subgroups of local Galois cohomology](bloch-kato-subgroups.md), for $H^1_e$, $H^1_f$ and $H^1_g$ with $\mathbb{Q}_\ell$-coefficients
- [Galois cohomology of Tate twists over a p-adic field](../galois-cohomology-of-local-fields/cohomology-of-tate-twists-over-p-adic-fields.md), for $H^2(K, \mathbb{Q}_\ell/\mathbb{Z}_\ell(1)) \cong \mathbb{Q}_\ell/\mathbb{Z}_\ell$
- [Galois cohomology of ℓ-adic representations of a p-adic field](../galois-cohomology-of-local-fields/galois-cohomology-of-l-adic-representations.md), for continuous cohomology of $T$ and $V$
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $T^*(1)$ and $\mathbb{Q}_\ell/\mathbb{Z}_\ell(1)$

## Proof depends on

- [Bloch–Kato orthogonality](bloch-kato-orthogonality.md), for the statement with $\mathbb{Q}_\ell$-coefficients, from which the statement for $T$ follows
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the perfect pairing at finite levels, which gives the perfect pairing between $H^1(K, T) = \varprojlim_n H^1(K, T/\ell^n T)$ and $H^1(K, A') = \varinjlim_n H^1(K, A'[\ell^n])$
- [Galois cohomology of ℓ-adic representations of a p-adic field](../galois-cohomology-of-local-fields/galois-cohomology-of-l-adic-representations.md), for $H^1(K, T) = \varprojlim_n H^1(K, T/\ell^n T)$ and $H^1(K, V) = H^1(K, T) \otimes \mathbb{Q}_\ell$
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the case $\ell \ne p$

## Sources

- S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", in *The Grothendieck Festschrift*, vol. I,
  Progr. Math. 86, Birkhäuser, 1990, 333–400, <http://math.stanford.edu/~conrad/BSDseminar/refs/BKTamagawa.pdf>:
  §3, (3.7.1) (for $\ell \ne p$: $H^1_e = 0$, $H^1_g = H^1$, $H^1_f$ the unramified classes, for $\mathbb{Q}_\ell$-coefficients)
  and (3.7.2) (for $\ell = p$), (3.7.3) ($H^1_*(K, T) = \iota^{-1}(H^1_*(K, T \otimes \mathbb{Q}))$,
  containing the torsion), p. 354; (3.4) (the subgroups $H^1_*(K, T) \otimes \mathbb{Q}/\mathbb{Z}$ of $H^1(K, T \otimes \mathbb{Q}/\mathbb{Z})$),
  p. 352; Proposition 3.8 ("$H^1_e(K, T)$ and $H^1_g(K, T^*(1) \otimes \mathbb{Q}_\ell/\mathbb{Z}_\ell)$ are the exact annihilators of each
  other. The same statement holds with $e$ replaced by $g$ and $g$ by $e$ and also when $e$ and $g$ are both replaced
  by $f$"; "The assertion for $T$ follows easily from that for $V$"), pp. 354–359.
- M. Flach, "A finiteness theorem for the symmetric square of an elliptic curve", Invent. Math. 109 (1992),
  307–327, <https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0109/LOG_0022.pdf>: p. 308 (the natural
  Galois-invariant lattice $T = \mathrm{Sym}^2 H^1(E, \mathbb{Z}_p)$ and $A = V/T$), §1, pp. 309–311 (on p. 310 the Kummer dual
  $V(1)$ with its orthogonal lattice, and "the Kummer dual of $V(1)$ can be identified with $V(2)$"; the definitions of $H^1_f(\mathbb{Q}_r, V)$ and $H^1_f(\mathbb{Q}_r, T) = i_*^{-1}(H^1_f(\mathbb{Q}_r, V))$ as in Bloch–Kato, and in
  the proof of Proposition 1.1 the orthogonal complements $i(n)_*^{-1} \mathrm{pr}_* H^1_f(\mathbb{Q}_r, V(1))$ and
  $\mathrm{pr}(n)_* H^1_f(\mathbb{Q}_r, T(2))$ under Tate local duality, the $f$/$f$ case for the symmetric-square twists,
  "a formal consequence of" Bloch–Kato's Proposition 3.8).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the lattice and divisible-quotient statement for $f$ and dual lattices as the part `IntegralDuality` of
  `GlobalTheory.Published.BlochKatoLocal`.
