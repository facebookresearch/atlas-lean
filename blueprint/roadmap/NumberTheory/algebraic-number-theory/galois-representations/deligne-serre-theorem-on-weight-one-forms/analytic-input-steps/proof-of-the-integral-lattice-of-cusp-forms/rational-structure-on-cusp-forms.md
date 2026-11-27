# Cusp forms on Γ₁(N) with rational q-expansions span all cusp forms

Let $k \ge 1$ and $N \ge 1$, and let $S$ be the complex vector space of cusp forms of weight $k$ on $\Gamma_1(N)$, each
written by its $q$-expansion $f = \sum_{n \ge 1} a_n q^n$, $q = e^{2\pi i z}$. For a subfield $K$ of $\mathbb{C}$ let
$S(K)$ be the $K$-vector space of the $f \in S$ whose coefficients $a_n$ all lie in $K$. For $d \in (\mathbb{Z}/N\mathbb{Z})^*$
let $R_d$ be the operator $f \mapsto f|_k \gamma$ on $S$, where $(f|_k\gamma)(z) = (cz + d')^{-k} f\bigl(\frac{az + b}{cz + d'}\bigr)$
for any $\gamma = \left(\begin{smallmatrix} a & b \\ c & d' \end{smallmatrix}\right) \in \Gamma_0(N)$ with $d' \equiv d \pmod N$,
which depends only on $d$. Then:

1. the map $\mathbb{C} \otimes_{\mathbb{Q}} S(\mathbb{Q}) \to S$, $c \otimes f \mapsto c f$, is an isomorphism, that is, $S$ has a
   basis of forms with rational $q$-expansion coefficients;
2. for every subfield $K$ of $\mathbb{C}$, the map $K \otimes_{\mathbb{Q}} S(\mathbb{Q}) \to S(K)$, $c \otimes f \mapsto c f$, is an
   isomorphism;
3. $S(\mathbb{Q})$ is stable under the operators $R_d$.

This is (2.6.1) of Deligne–Serre with the criterion of their §2.6, read through the identification of their §2.4. For a
field $K$ of characteristic $0$ they write $S_K$ for the space of cusp forms of weight $k$ on $\Gamma_1(N)$ defined over $K$
in the sense of their §2.1: laws that attach to an elliptic curve $E$ over a $K$-algebra, with an embedding
$\alpha \colon \mu_N \to E$, a section of $\omega_E^{\otimes k}$. They show $S_K = K \otimes_{\mathbb{Q}} S_{\mathbb{Q}}$ (2.6.1), and,
for a subfield $K'$ of $K$, that $f \in S_K$ lies in $S_{K'}$ exactly when the coefficients of its expansion $f_\infty(q)$
lie in $K'$. For $K = \mathbb{C}$, §2.4 identifies $S_{\mathbb{C}}$ with $S$ and $f_\infty$ with the $q$-expansion
(formula (2.4.2)), so that $S_K$ is $S(K)$ for every subfield $K$ of $\mathbb{C}$: items 1 and 2 are (2.6.1) for $\mathbb{C}$
and for $K$. Item 3 holds because $(f|R_d)(E, \alpha) = f(E, d\alpha)$ (formula (2.2.1)) is defined over every field over
which $f$ is; Deligne and Serre use it at the start of the proof of their Proposition 2.7.

## Depends on

- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the space $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the operators $R_d$

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the geometric definition (§2.1) of a cusp form of weight $k$ on $\Gamma_1(N)$ defined over a ring in which $N$ is
  invertible, and its comparison (2.4.1)–(2.4.2) with the classical cusp forms over $\mathbb{C}$ (§2.4);
- the interpretation of $S_K$ as the space of sections of an invertible sheaf on the algebraic stack attached to
  $\Gamma_1(N)$ over $\mathbb{Q}$, which gives $S_K = K \otimes_{\mathbb{Q}} S_{\mathbb{Q}}$ ([7], VII, 3.2, as cited in §2.6);
- the descent argument of §2.6 for a subfield $K'$ of $K$: reduce to $K$ algebraically closed, and note that $f$ and
  $\sigma(f)$ have the same expansion for every $K'$-automorphism $\sigma$ of $K$, so that they coincide;
- the agreement of $f_\infty(q)$, the value of $f$ on the Tate curve, with the analytic $q$-expansion ([7], VII, §4, as
  cited in §2.5).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §2.1, p. 510 (forms defined over a ring); §2.2,
  formula (2.2.1), p. 510; §2.4, formulas (2.4.1)–(2.4.2), p. 511; §2.5, pp. 511–512; §2.6 and (2.6.1), p. 512; the proof of
  Proposition 2.7, p. 512.
- P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, in *Modular functions of one variable
  II*, Lecture Notes in Math. 349, Springer (1973), 143–316: VII, 3.2 and VII, §4, as cited in Deligne–Serre (1974),
  pp. 511–512; not read.
