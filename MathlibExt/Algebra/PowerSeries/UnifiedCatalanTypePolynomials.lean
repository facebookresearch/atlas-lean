/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.NumberTheory.HankelTransform

/-!
# Unified Catalan-type polynomials

The trinomial series and Kampé de Fériet polynomials follow M. A. Pathan and T. Usman,
*Unified Catalan-Type Polynomials with Matrix Formulations and Applications*. The coefficients of
the trinomial series times the Nieto–Hermite series, which keeps the coefficients of
`e^(2yt - t²)` at the indices `jn + k`, are convolution sums over those indices. A recurrence
among the coefficients of the Catalan-type generating function gives a linear relation among the
rows of its Hankel matrix.
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

/-- **Nieto–Hermite Catalan-type polynomials as convolutions.** Let $j, k, m, r$ be natural
numbers with $k \le r$ and let $\lambda, x, y$ be real numbers. Let $E(t) = e^{2yt - t^2}$ be the
exponential series, so that its coefficient of $t^n$ is $H_n(y) / n!$ with $H_n$ the Hermite
polynomials, and let $F(t)$ be the power series whose coefficient of $t^n$ is $H_n(y) / n!$ when
$n \ge k$ and $j \mid n - k$, and $0$ otherwise (for $j \ge 1$ this is the series
$F(j, k, y, t) = \sum_n H_{jn+k}(y) t^{jn+k} / (jn + k)!$ of Equation (1)). Write
$(1 - m t + x t^m)^{-\lambda}$ and $(1 - m x t + t^m)^{-\lambda}$ for the negative real powers
of the trinomials $1 - m t + x t^m$ and $1 - m x t + t^m$ with exponent $\lambda$ as power
series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), let
$P^\lambda_{s,m}(x)$ and $h^\lambda_{s,m}(x)$ be their coefficients of $t^s$, and let
$q = \lfloor (r - k) / j \rfloor$, read as $q = 0$ when $j = 0$. Then the coefficient of
$t^r$ in $F(t) (1 - m t + x t^m)^{-\lambda}$ is
$\sum_{n=0}^{q} H_{jn+k}(y) P^\lambda_{r-jn-k,m}(x) / (jn + k)!$, and the coefficient of $t^r$
in $F(t) (1 - m x t + t^m)^{-\lambda}$ is the same sum with $h^\lambda_{r-jn-k,m}(x)$ in place
of $P^\lambda_{r-jn-k,m}(x)$.

These are the paper's $F^{j.k;\lambda}_{r,m}(x, y)$ and $f^{j.k;\lambda}_{r,m}(x, y)$
(Equations (10) and (11)). The paper takes $j, m \ge 1$; for $r < k$ its sum is empty.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 3
(`integers-2026-A105-thm-3`). -/
theorem coeff_nietoHermiteSeries_mul_trinomialNegPowSeries (j k m r : ℕ)
    (lam x y : ℝ) (hkr : k ≤ r) :
    let E : PowerSeries ℝ :=
      ((exp ℝ).subst (C (2 * y) * X - X ^ 2 : PowerSeries ℝ) : PowerSeries ℝ)
    let F : PowerSeries ℝ := PowerSeries.mk fun n ↦ if k ≤ n ∧ j ∣ n - k then coeff n E else 0
    coeff r (F * trinomialNegPowSeries lam 1 m x m) =
        ∑ n ∈ Finset.range ((r - k) / j + 1),
          coeff (j * n + k) E * coeff (r - j * n - k) (trinomialNegPowSeries lam 1 m x m) ∧
      coeff r (F * trinomialNegPowSeries lam 1 (m * x) 1 m) =
        ∑ n ∈ Finset.range ((r - k) / j + 1),
          coeff (j * n + k) E *
            coeff (r - j * n - k) (trinomialNegPowSeries lam 1 (m * x) 1 m) := by
  intro E F
  -- For every series `G`, only the indices `a = j * n + k ≤ r` contribute to the coefficient
  -- of `t ^ r` in `F * G`, and `n ↦ j * n + k` maps the `n ≤ (r - k) / j` bijectively onto them.
  have key (G : PowerSeries ℝ) : coeff r (F * G) =
      ∑ n ∈ Finset.range ((r - k) / j + 1), coeff (j * n + k) E * coeff (r - j * n - k) G := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [F, coeff_mk, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun n ↦ j * n + k) (fun a ↦ (a - k) / j) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range] at hn
      have hjn : j * n ≤ r - k :=
        (Nat.mul_le_mul_left j (Nat.lt_succ_iff.mp hn)).trans (Nat.mul_div_le (r - k) j)
      rw [Finset.mem_filter, Finset.mem_range, Nat.add_sub_cancel]
      exact ⟨by omega, by omega, dvd_mul_right j n⟩
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · intro n hn
      rw [Finset.mem_range] at hn
      rw [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [Nat.div_zero] at hn ⊢
        omega
      · exact Nat.mul_div_cancel_left n hj
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Nat.mul_div_cancel' ha.2.2]
      omega
    · intro n _
      rw [Nat.sub_sub]
  exact ⟨key _, key _⟩

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
  intro P
  exact hankelTransform.eq_zero_of_recurrence P cs

end

end MetaMathlibExt
