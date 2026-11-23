/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Unified Catalan-type polynomials

The trinomial series and Kampé de Fériet polynomials follow M. A. Pathan and T. Usman,
*Unified Catalan-Type Polynomials with Matrix Formulations and Applications*. A recurrence among
the coefficients of the Catalan-type generating function gives a linear relation among the rows of
its Hankel matrix.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Negative real power of a trinomial as a power series.** For real numbers $\lambda$, $c$,
$\alpha$, $\beta$ and a natural number $m$, this is the formal power series in $t$ with real
coefficients
$$c^{-\lambda} \sum_{n \ge 0} \binom{-\lambda}{n} u^n, \qquad u = \frac{-\alpha t + \beta t^m}{c},$$
that is, the real power $c^{-\lambda}$ times the binomial series
$(1 + t)^{-\lambda} = \sum_{n \ge 0} \binom{-\lambda}{n} t^n$ with $u$ substituted for $t$ (for
$c = 0$ the division is read as $0$, so $u = 0$). The substitution is meaningful when $u$ has
zero constant term, which holds for $m \ge 1$; for $c > 0$ and $m \ge 1$ the series is the
expansion of $(c - \alpha t + \beta t^m)^{-\lambda}$ in powers of $t$.

For $c > 0$ and $m \ge 1$ this is the denominator factor of every generating function in Pathan
and Usman's paper; Section 2 takes $c = 1$, $\alpha = m$ and $\beta = x$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equations (6), (12)
and (15). -/
noncomputable def trinomialNegPowSeries (lam c α β : ℝ) (m : ℕ) : PowerSeries ℝ :=
  C (c ^ (-lam)) *
    (binomialSeries ℝ (-lam)).subst (C (-α / c) * X + C (β / c) * X ^ m : PowerSeries ℝ)

/-- **Constant term of the trinomial series.** For all real numbers $\lambda, c, \alpha, \beta$
and every natural number $m \ne 0$, the negative real power of the trinomial
$c - \alpha t + \beta t^m$ with exponent $\lambda$ as a power series in $t$, that is, the real
power $c^{-\lambda}$ times the binomial series $(1 + u)^{-\lambda}$ with
$u = (-\alpha t + \beta t^m)/c$ substituted (where $u = 0$ when $c = 0$), has constant term
$c^{-\lambda}$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (6). -/
theorem constantCoeff_trinomialNegPowSeries (lam c α β : ℝ) {m : ℕ} (hm : m ≠ 0) :
    constantCoeff (trinomialNegPowSeries lam c α β m) = c ^ (-lam) := by
  set u : PowerSeries ℝ := C (-α / c) * X + C (β / c) * X ^ m with hu_def
  have hu0 : constantCoeff u = 0 := by simp [u, hm]
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hone : subst u (1 : PowerSeries ℝ) = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  set b := binomialSeries ℝ (-lam) with hb_def
  have hb0 : constantCoeff (b - 1) = 0 := by simp [b]
  have hsub0 : constantCoeff ((b - 1).subst u) = 0 :=
    constantCoeff_subst_eq_zero hu0 (b - 1) hb0
  have hb : b = 1 + (b - 1) := by ring
  unfold trinomialNegPowSeries
  rw [← hu_def, ← hb_def, map_mul, hb, subst_add hu, map_add, hone, hsub0]
  simp

/-- **The trinomial series at exponent one.** For all real numbers $\alpha, \beta$ and every
natural number $m \ne 0$, the formal expansion of $(1 - \alpha t + \beta t^m)^{-\lambda}$ in
powers of $t$ at $\lambda = -1$ is the polynomial $1 - \alpha t + \beta t^m$ itself.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (6). -/
theorem trinomialNegPowSeries_neg_one (α β : ℝ) {m : ℕ} (hm : m ≠ 0) :
    trinomialNegPowSeries (-1) 1 α β m = 1 - C α * X + C β * X ^ m := by
  set u : PowerSeries ℝ := C (-α / 1) * X + C (β / 1) * X ^ m with hu_def
  have hu0 : constantCoeff u = 0 := by simp [u, hm]
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hone : subst u (1 : PowerSeries ℝ) = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  have h1 : (-(-1 : ℝ)) = ((1 : ℕ) : ℝ) := by norm_num
  unfold trinomialNegPowSeries
  rw [← hu_def, h1, binomialSeries_nat, pow_one, subst_add hu, subst_X hu, hone]
  simp [u, map_neg]
  ring

/-- **Kampé de Fériet polynomials.** For natural numbers $m, n$ and elements $x, y$ of a
commutative $\mathbb{R}$-algebra, the Kampé de Fériet (two-variable Hermite) polynomial is

$$H^m_n(x, y) = \sum_{r=0}^{q} \frac{n!}{r!\,(n - m r)!}\, y^r x^{n - m r},$$

where $q = \lfloor n / m \rfloor$, read as $q = 0$ when $m = 0$. The paper writes $H_n(x, y)$
for $H^2_n(x, y)$; taking values in an algebra lets $H_k(x + 2yt, y)$ be formed as a formal
power series in $t$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
noncomputable def kampeDeFerietHermite {A : Type*} [CommRing A] [Algebra ℝ A] (m n : ℕ)
    (x y : A) : A :=
  ∑ r ∈ Finset.range (n / m + 1),
    ((n.factorial : ℝ) / ((r.factorial : ℝ) * ((n - m * r).factorial : ℝ))) •
      (y ^ r * x ^ (n - m * r))

/-- **The zeroth Kampé de Fériet polynomial.** For every natural number $m$ and all elements
$x, y$ of a commutative $\mathbb{R}$-algebra, $H^m_0(x, y) = 1$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
theorem kampeDeFerietHermite_zero {A : Type*} [CommRing A] [Algebra ℝ A] (m : ℕ) (x y : A) :
    kampeDeFerietHermite m 0 x y = 1 := by
  simp [kampeDeFerietHermite]

/-- **The second Kampé de Fériet polynomial.** For all real numbers $x$ and $y$,
$H^2_2(x, y) = x^2 + 2y$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
theorem kampeDeFerietHermite_two_two (x y : ℝ) :
    kampeDeFerietHermite 2 2 x y = x ^ 2 + 2 * y := by
  simp [kampeDeFerietHermite, Finset.sum_range_succ, Nat.factorial]

/-- **Hankel determinants of recurrent Catalan-type sequences vanish.** Let $m, N, r$ be natural
numbers with $r \le N$, let $\lambda, x$ be real numbers, let $A$ be a polynomial with integer
coefficients, and let $P_n$ be the coefficient of $t^n$ in
$(1 + A(x)\, t)(1 - m t + x t^m)^{-\lambda}$, where $(1 - m t + x t^m)^{-\lambda}$ denotes the
negative real power of the trinomial $1 - m t + x t^m$ with exponent $\lambda$ as a power series
in $t$ (for $m \ge 1$, its expansion in powers of $t$). Suppose real numbers $c_0, \dots, c_r$,
not all zero, satisfy $\sum_{k=0}^{r} c_k P_{n-k} = 0$ for every $n \ge r$. Then the
$(N + 1) \times (N + 1)$ Hankel matrix with $(i, j)$ entry $P_{i+j}$ for $0 \le i, j \le N$ has
determinant $0$.

In the paper's notation $P_n = P^{\lambda,A}_{n,m}(x)$, the recurrence is Equation (22) and the
Hankel matrix is $H_N^{(m,\lambda,A)}(x)$ of Equation (20). The paper's assumption $1 \le r$ is
dropped.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 8
(`integers-2026-A105-thm-8`). -/
theorem det_catalanTypeHankel_eq_zero (m N r : ℕ) (lam x : ℝ)
    (A : Polynomial ℤ) (cs : ℕ → ℝ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    r ≤ N → (∃ k ≤ r, cs k ≠ 0) →
      (∀ n, r ≤ n → ∑ k ∈ Finset.range (r + 1), cs k * P (n - k) = 0) →
      (Matrix.of fun i j : Fin (N + 1) ↦ P (i + j)).det = 0 := by
  intro P hr ⟨k, hk, hck⟩ hrec
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hrows
  -- The recurrence weights rows r, r - 1, ..., 0 in this order.
  let row (a : Fin (r + 1)) := a.rev.castLE (Nat.succ_le_succ hr)
  have hind := hrows.comp row ((Fin.castLE_injective _).comp Fin.rev_injective)
  apply hck
  apply Fintype.linearIndependent_iff.mp hind (fun a ↦ cs a) _ ⟨k, by omega⟩
  funext j
  have hj := hrec (r + j.val) (by omega)
  rw [← Fin.sum_univ_eq_sum_range] at hj
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Matrix.of_apply,
    row, Fin.val_castLE, Fin.val_rev, Nat.succ_sub_succ_eq_sub, smul_eq_mul, Pi.zero_apply]
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans hj
  rw [Nat.sub_add_comm (Nat.le_of_lt_succ a.isLt)]

end

end MetaMathlibExt
