# The Hecke eigenvalues on cusp forms on Γ₁(N) are algebraic integers of one number field

Let $k \ge 1$ and $N \ge 1$, let $S$ be the space of cusp forms of weight $k$ on $\Gamma_1(N)$, with $q$-expansions
$f = \sum_{n \ge 1} a_n q^n$, and for a prime $p \nmid N$ let $T_p$ be the Hecke operator on $S$, given on $q$-expansions by

$$f|T_p = \sum_{n \ge 1} a_{pn} q^n + p^{k-1} \sum_{n \ge 1} a_n(p)\, q^{pn}, \qquad f|R_p = \sum_{n \ge 1} a_n(p)\, q^n,$$

where $R_p$ is the operator $f \mapsto f|_k \gamma$ for any $\gamma \in \Gamma_0(N)$ whose lower right entry is congruent to
$p$ modulo $N$. Then every eigenvalue of every $T_p$, $p \nmid N$, on $S$ is an algebraic integer, and some finite extension
$F$ of $\mathbb{Q}$ in $\mathbb{C}$ contains all of them.

This is (2.7.3) of Deligne–Serre, which they deduce from (2.7.1)–(2.7.2). Let $L$ be the
[lattice of forms with integral expansions](integral-cusp-forms-form-a-lattice.md), free of rank $r$ with
$S = \mathbb{C} \otimes_{\mathbb{Z}} L$. Each $T_p$ [maps $L$ into itself](hecke-operators-preserve-the-integral-lattice.md), so in a
basis of $L$ it is given by a matrix with integer entries, and its characteristic polynomial on $S$ is monic with
integer coefficients: its roots, the eigenvalues of $T_p$, are algebraic integers. The $T_p$ commute with one another (§2.3), so they
generate a commutative subring $\mathbf{T}$ of $\operatorname{End}_{\mathbb{Z}}(L)$, finitely generated as a $\mathbb{Z}$-module since
$\operatorname{End}_{\mathbb{Z}}(L) \cong \mathbb{Z}^{r^2}$. An eigenvalue $\lambda$ of $T_p$ has an eigenspace stable under
$\mathbf{T}$, in which the commuting operators of $\mathbf{T}$ have a common eigenvector; its eigenvalues define a ring
homomorphism $\chi \colon \mathbf{T} \to \mathbb{C}$ with $\chi(T_p) = \lambda$. Eigenvectors for distinct such $\chi$ are
linearly independent, so at most $r$ of them occur, and each $\chi(\mathbf{T})$ is a finitely generated $\mathbb{Z}$-module, so
$\mathbb{Q}(\chi(\mathbf{T}))$ is a number field. Their compositum is an $F$ as above.

## Depends on

- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the space $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the operators $R_p$
- [Eigenvalues of a linear map](../../../../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/eigenvalues.md), for the eigenvalues of the $T_p$ on $S$

## Proof depends on

- [Cusp forms on Γ₁(N) with integral q-expansions form a lattice](integral-cusp-forms-form-a-lattice.md), for $S = \mathbb{C} \otimes_{\mathbb{Z}} L$ with $L$ free of finite rank
- [The Hecke operators on cusp forms on Γ₁(N) commute and preserve the integral lattice](hecke-operators-preserve-the-integral-lattice.md), for $T_p(L) \subset L$ and the commutation of the $T_p$

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Proposition 2.7, (2.7.3), and its proof ("Les assertions
  (2.7.3) et (2.7.4) en résultent"), p. 512; §2.3, p. 511, for the commutation of the $\mathrm{T}_p$.
