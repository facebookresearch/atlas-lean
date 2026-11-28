# Galois conjugates of Hecke eigenforms on Γ₁(N)

Let $k \ge 1$ and $N \ge 1$, let $S$ be the space of cusp forms of weight $k$ on $\Gamma_1(N)$, with $q$-expansions
$f = \sum_{n \ge 1} a_n q^n$, let $R_d$, $d \in (\mathbb{Z}/N\mathbb{Z})^*$, be the operator $f \mapsto f|_k \gamma$ for any
$\gamma \in \Gamma_0(N)$ whose lower right entry is congruent to $d$ modulo $N$, and for a prime $p \nmid N$ let $T_p$ be the
Hecke operator on $S$, given on $q$-expansions by

$$f|T_p = \sum_{n \ge 1} a_{pn} q^n + p^{k-1} \sum_{n \ge 1} a_n(p)\, q^{pn}, \qquad f|R_p = \sum_{n \ge 1} a_n(p)\, q^n.$$

For $f \in S$ and an automorphism $\sigma$ of the field $\mathbb{C}$, the series $\sigma(f) = \sum_{n \ge 1} \sigma(a_n) q^n$ is the
$q$-expansion of an element of $S$. If $f|T_p = \lambda f$ for a prime $p \nmid N$, then
$\sigma(f)|T_p = \sigma(\lambda)\, \sigma(f)$. If $f|R_d = \varepsilon(d) f$ for all $d$, for a character $\varepsilon$ of
$(\mathbb{Z}/N\mathbb{Z})^*$, that is, if $f$ is of [type $(k, \varepsilon)$ on $\Gamma_0(N)$](../../modular-forms-of-type-k-epsilon.md), then
$\sigma(f)|R_d = \sigma(\varepsilon(d))\, \sigma(f)$ for all $d$, so that $\sigma(f)$ is of type $(k, \sigma \circ \varepsilon)$.

This is (2.7.4) of Deligne–Serre, which they deduce from (2.7.1)–(2.7.2). Let $\ell_1, \dots, \ell_r$ be a basis of the
[lattice $L$ of forms with integral expansions](integral-cusp-forms-form-a-lattice.md), so that $f = \sum_i c_i \ell_i$ with
$c_i \in \mathbb{C}$. The coefficients of $f$ are $a_n = \sum_i c_i a_n(\ell_i)$ with $a_n(\ell_i) \in \mathbb{Z}$, so $\sigma(f)$ is
the expansion of $\sum_i \sigma(c_i) \ell_i \in S$. The map $f \mapsto \sigma(f)$ is thus $\sigma$-semilinear and fixes $L$
pointwise, and the $\mathbb{C}$-linear operators $T_p$ and $R_d$ [map $L$ into $L$](hecke-operators-preserve-the-integral-lattice.md),
so they commute with it: $\sigma(f)|T_p = \sigma(f|T_p) = \sigma(\lambda f) = \sigma(\lambda)\, \sigma(f)$, and likewise for $R_d$.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](../../modular-forms-of-type-k-epsilon.md), for forms of type $(k, \varepsilon)$
- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the space $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the operators $R_d$

## Proof depends on

- [Cusp forms on Γ₁(N) with integral q-expansions form a lattice](integral-cusp-forms-form-a-lattice.md), for $S = \mathbb{C} \otimes_{\mathbb{Z}} L$
- [The Hecke operators on cusp forms on Γ₁(N) commute and preserve the integral lattice](hecke-operators-preserve-the-integral-lattice.md), for $T_p(L) \subset L$ and $R_d(L) \subset L$

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Proposition 2.7, (2.7.4), and its proof, p. 512.
