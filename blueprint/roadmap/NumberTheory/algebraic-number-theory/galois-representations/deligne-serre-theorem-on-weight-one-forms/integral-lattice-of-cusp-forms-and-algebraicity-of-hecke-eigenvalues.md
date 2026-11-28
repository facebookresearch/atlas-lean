# Integral lattice of cusp forms on Γ₁(N) and algebraicity of their Hecke eigenvalues

Let $k \ge 1$ and $N \ge 1$, and let $S$ be the complex vector space of cusp forms of weight $k$ on $\Gamma_1(N)$, each
written by its $q$-expansion $f = \sum_{n \ge 1} a_n q^n$, $q = e^{2\pi i z}$. For $d \in (\mathbb{Z}/N\mathbb{Z})^*$ let
$R_d$ be the operator $f \mapsto f|_k \gamma$, $(f|_k\gamma)(z) = (cz + d')^{-k} f\bigl(\frac{az + b}{cz + d'}\bigr)$, for any
$\gamma = \left(\begin{smallmatrix} a & b \\ c & d' \end{smallmatrix}\right) \in \Gamma_0(N)$ with $d' \equiv d \pmod N$,
which depends only on $d$. For a prime $p \nmid N$ let $T_p$ be the Hecke operator, given on $q$-expansions by

$$f|T_p = \sum_{n \ge 1} a_{pn} q^n + p^{k-1} \sum_{n \ge 1} a_n(p)\, q^{pn}, \qquad f|R_p = \sum_{n \ge 1} a_n(p)\, q^n.$$

Let $L$ be the set of $f \in S$ such that $f|R_d$ has all its $q$-expansion coefficients in $\mathbb{Z}$ for every
$d \in (\mathbb{Z}/N\mathbb{Z})^*$. Then:

1. $L$ is a free $\mathbb{Z}$-module of finite rank, stable under the operators $T_p$ and $R_d$;
2. for every subfield $K$ of $\mathbb{C}$, the forms of $S$ whose $q$-expansion coefficients all lie in $K$ form the
   $K$-vector space $K \otimes_{\mathbb{Z}} L$; in particular $S = \mathbb{C} \otimes_{\mathbb{Z}} L$;
3. the eigenvalues of the operators $T_p$, $p \nmid N$, on $S$ are algebraic integers, and they all lie in one finite
   extension of $\mathbb{Q}$;
4. if $f \in S$ satisfies $f|T_p = a_p f$, then for every automorphism $\sigma$ of $\mathbb{C}$ the form $\sigma(f)$, whose
   $q$-expansion coefficients are the images under $\sigma$ of those of $f$ (a cusp form by 2), satisfies
   $\sigma(f)|T_p = \sigma(a_p)\,\sigma(f)$; if $f|R_d = \varepsilon(d) f$ for all $d$, for a character $\varepsilon$ of
   $(\mathbb{Z}/N\mathbb{Z})^*$, then $\sigma(f)|R_d = \sigma(\varepsilon(d))\,\sigma(f)$ for all $d$.

This is Proposition 2.7 of Deligne–Serre, stated there for the spaces $S_K$ of cusp forms defined over a field $K$ of
characteristic $0$ in the sense of their §2.1; for a subfield $K$ of $\mathbb{C}$, §2.6 identifies $S_K$ with the forms of
$S$ whose $q$-expansion coefficients lie in $K$, and §2.4 identifies $S_{\mathbb{C}}$, the operators $T_p$ and the $R_d$
with the classical ones above (formula (2.5.1) for $T_p$).

## Depends on

- [Cusp form](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/cusp-form.md), for the cusp forms of weight $k$ on $\Gamma_1(N)$ that make up $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/congruence-subgroup-gamma1.md), for the group of $S$
- [Congruence subgroup $\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/congruence-subgroup-gamma0.md), for the operators $R_d$
- [Free module](../../../../LinearAlgebra/bases-and-dimension/free-module.md), for the free $\mathbb{Z}$-module $L$
- [Eigenvalues of a linear map](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/eigenvalues.md), for the eigenvalues of the $T_p$ on $S$

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the bounded denominators of the $q$-expansions $(f|R_d)_\infty$ of a cusp form $f$ defined over $\mathbb{Q}$, which
  Deligne and Serre deduce from the Tate curve being defined over $\mathbb{Z}((q)) \otimes \mathbb{Q}$ (Remarque 2.8; their
  reference [7], VII, as cited there), or, for $k \ge 2$, from Shimura's theorem 3.5.2 ([24], as cited in Remarque 2.8)
  after multiplying a form of weight $1$ by $\Delta$;
- the base change $S_K = K \otimes_{\mathbb{Q}} S_{\mathbb{Q}}$ (2.6.1), from the interpretation of $S_K$ as the sections of an
  invertible sheaf on the algebraic stack of $\Gamma_1(N)$ ([7], VII, 3.2, as cited in §2.6), and the criterion of §2.6 for a
  form to be defined over a subfield;
- the stability of $L$ under the $T_p$, from formula (2.5.1), and the passage from (2.7.1) and (2.7.2) to (2.7.3) and
  (2.7.4): each $T_p$ acts on the finite free $\mathbb{Z}$-module $L$, so its eigenvalues are roots of a monic integer
  polynomial, which makes them algebraic integers one operator at a time; the one finite extension of $\mathbb{Q}$ of
  (2.7.3) comes from the $T_p$ commuting with one another (§2.3): they generate a finite-dimensional commutative
  $\mathbb{Q}$-algebra of endomorphisms of $\mathbb{Q} \otimes L$, which has finitely many residue fields, all number
  fields, and each eigenvalue of a $T_p$ is the image of $T_p$ under a homomorphism of that algebra to $\mathbb{C}$,
  which factors through one of them; and $\sigma$ commutes with operators defined on $L$.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Proposition 2.7, (2.7.1)–(2.7.4), and its proof, p. 512;
  §2.6 and (2.6.1), p. 512; formula (2.5.1), p. 511, and (2.5.2), p. 512; §§2.2–2.4, pp. 510–511, with §2.3, p. 511, for
  the commutation of the $T_p$ ("Les $T_p$ commutent entre eux, et commutent aux $R_d$"); §1.4, p. 508, for the
  operators $R_d$; Remarque 2.8, p. 512.
