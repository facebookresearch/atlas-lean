/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.Complex.EntireOrder
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The Selberg class

The *Selberg class* `𝒮` is an axiomatic class of Dirichlet series `F(s) = ∑ a(n) n^{-s}` that
behave like `L`-functions of automorphic forms. A coefficient sequence `a` belongs to `𝒮` when

* `a 1 = 1`;
* (*analytic continuation*) `F` continues to a function holomorphic on `ℂ ∖ {1}` such that
  `(s - 1)^m F(s)` extends to an entire function of finite order for some `m`;
* (*functional equation*) there are `Q > 0`, `α_i > 0`, `r_i` with `Re r_i ≥ 0` and `|w| = 1`
  such that `Φ(s) = Q^s ∏ Γ(α_i s + r_i) F(s)` satisfies `Φ(s) = w Φ̄(1 - s)`;
* (*Euler product*) `log F(s) = ∑ b(n) n^{-s}` with `b` supported on prime powers and
  `b(n) = O(n^θ)` for some `θ < 1/2`;
* (*Ramanujan hypothesis*) `a(n) = O(n^ε)` for every `ε > 0`.

We record a member of `𝒮` by its coefficient sequence, an arithmetic function `a`, so that
`𝒮` is a subset of the ring of arithmetic functions, where products are products of
`L`-functions.

## Main definitions

* `ArithmeticFunction.IsLSeriesContinuation a F`: `F` agrees with `L(a, s)` on `Re s > 1` and
  is holomorphic on `ℂ ∖ {1}`.
* `ArithmeticFunction.IsEulerLog a b`: `b` is supported on prime powers and
  `L(a, s) = exp L(b, s)` on `Re s > 1`, with `L(b, s)` absolutely convergent there.
* `SelbergClass.FunctionalEquation F`: the data of a functional equation of `F`.
* `SelbergClass.FunctionalEquation.degree`: the degree `2 ∑ α_i` of a functional equation.
* `ArithmeticFunction.selbergClass`: the Selberg class `𝒮`.

## Main statements

* `ArithmeticFunction.IsLSeriesContinuation.eqOn_compl_one`: the continuation is unique off `1`.
* `ArithmeticFunction.IsEulerLog.unique`: the Euler logarithm of `a` with `a 1 = 1` is unique.
* `ArithmeticFunction.IsEulerLog.natCast_mul_apply_prime_pow`: the recursion
  `k a(pᵏ) = ∑_{i ≤ k} i b(pⁱ) a(pᵏ⁻ⁱ)` between `a` and its Euler logarithm `b`.
* `ArithmeticFunction.IsEulerLog.apply_prime`: `b(p) = a(p)` at primes.
* `SelbergClass.FunctionalEquation.eq_of_re_lt_one`: the functional equation holds on all of
  `Re s < 1`, `s ≠ 0`, solved for `F(s)`.
* `SelbergClass.meromorphicAt_one`: the function of a member of `𝒮` is meromorphic at `1`.
-/

open Complex Filter Topology

@[expose] public section

namespace ArithmeticFunction

/-- `F` is the *continuation* of the Dirichlet series of `a`: it equals `L(a, s) = ∑ a n n^{-s}`
on `Re s > 1` and is holomorphic on `ℂ ∖ {1}`. The value `F 1` is irrelevant. -/
def IsLSeriesContinuation (a : ArithmeticFunction ℂ) (F : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => a n) s) ∧ DifferentiableOn ℂ F {1}ᶜ

/-- `b` is an *Euler logarithm* of `a`: `b` is supported on prime powers and, for `Re s > 1`,
`∑ b n n^{-s}` converges absolutely with `∑ a n n^{-s} = exp (∑ b n n^{-s})`. -/
def IsEulerLog (a : ArithmeticFunction ℂ) (b : ℕ → ℂ) : Prop :=
  (∀ n, b n ≠ 0 → IsPrimePow n) ∧
  ∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧ LSeries (fun n => a n) s = exp (LSeries b s)

end ArithmeticFunction

namespace SelbergClass

/-- A *functional equation* for `F` of Selberg type: `Q > 0`, `α i > 0`, `r i` with
`Re (r i) ≥ 0` and `‖w‖ = 1` such that `Φ(s) = Q^s ∏ Γ(α i s + r i) F(s)` satisfies
`Φ(s) = w · conj (Φ(1 - conj s))` on the open strip `0 < Re s < 1`. (By analytic continuation it
then holds wherever both sides are holomorphic, see `FunctionalEquation.eq_of_re_lt_one`.) -/
structure FunctionalEquation (F : ℂ → ℂ) where
  /-- The number of Gamma factors. -/
  d : ℕ
  /-- The conductor `Q`. -/
  Q : ℝ
  /-- The scalings `α i` of the Gamma factors. -/
  α : Fin d → ℝ
  /-- The shifts `r i` of the Gamma factors. -/
  r : Fin d → ℂ
  /-- The root number `w`. -/
  w : ℂ
  Q_pos : 0 < Q
  α_pos : ∀ i, 0 < α i
  r_re_nonneg : ∀ i, 0 ≤ (r i).re
  norm_w : ‖w‖ = 1
  eqn : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    (Q : ℂ) ^ s * (∏ i, Gamma (α i * s + r i)) * F s =
      w * starRingEnd ℂ ((Q : ℂ) ^ (1 - starRingEnd ℂ s) *
        (∏ i, Gamma (α i * (1 - starRingEnd ℂ s) + r i)) * F (1 - starRingEnd ℂ s))

/-- The *degree* of a functional equation: `2 ∑ i, α i`. -/
def FunctionalEquation.degree {F : ℂ → ℂ} (D : FunctionalEquation F) : ℝ := 2 * ∑ i, D.α i

/-- **The functional equation of a product.** Functional equations of `F₁` and `F₂` give one of
`F₁ F₂`: concatenate the Gamma factors and multiply the conductors and the root numbers. -/
noncomputable def FunctionalEquation.mul {F₁ F₂ : ℂ → ℂ} (D₁ : FunctionalEquation F₁)
    (D₂ : FunctionalEquation F₂) : FunctionalEquation (fun s => F₁ s * F₂ s) where
  d := D₁.d + D₂.d
  Q := D₁.Q * D₂.Q
  α := Fin.append D₁.α D₂.α
  r := Fin.append D₁.r D₂.r
  w := D₁.w * D₂.w
  Q_pos := mul_pos D₁.Q_pos D₂.Q_pos
  α_pos := Fin.addCases (by simpa using D₁.α_pos) (by simpa using D₂.α_pos)
  r_re_nonneg := Fin.addCases (by simpa using D₁.r_re_nonneg) (by simpa using D₂.r_re_nonneg)
  norm_w := by rw [norm_mul, D₁.norm_w, D₂.norm_w, one_mul]
  eqn s h0 h1 := by
    have hQ : ∀ z : ℂ, ((D₁.Q * D₂.Q : ℝ) : ℂ) ^ z = (D₁.Q : ℂ) ^ z * (D₂.Q : ℂ) ^ z :=
      fun z => by rw [ofReal_mul, mul_cpow_ofReal_nonneg D₁.Q_pos.le D₂.Q_pos.le]
    have hP : ∀ z : ℂ,
        ∏ i, Gamma ((Fin.append D₁.α D₂.α i : ℝ) * z + Fin.append D₁.r D₂.r i) =
          (∏ i, Gamma (D₁.α i * z + D₁.r i)) * ∏ i, Gamma (D₂.α i * z + D₂.r i) :=
      fun z => by simp [Fin.prod_univ_add]
    rw [hQ, hQ, hP, hP]
    calc _ = ((D₁.Q : ℂ) ^ s * (∏ i, Gamma (D₁.α i * s + D₁.r i)) * F₁ s) *
          ((D₂.Q : ℂ) ^ s * (∏ i, Gamma (D₂.α i * s + D₂.r i)) * F₂ s) := by ring
      _ = _ := by rw [D₁.eqn s h0 h1, D₂.eqn s h0 h1]; simp only [map_mul]; ring

/-- The degree of the functional equation of a product is the sum of the degrees. -/
theorem FunctionalEquation.degree_mul {F₁ F₂ : ℂ → ℂ} (D₁ : FunctionalEquation F₁)
    (D₂ : FunctionalEquation F₂) : (D₁.mul D₂).degree = D₁.degree + D₂.degree := by
  change 2 * ∑ i : Fin (D₁.d + D₂.d), Fin.append D₁.α D₂.α i = 2 * _ + 2 * _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

end SelbergClass

namespace ArithmeticFunction

open SelbergClass

/-- **The Selberg class** `𝒮`, as a set of coefficient sequences: `a 1 = 1`; the Dirichlet
series of `a` has a continuation `F` such that `(s - 1)^m F(s)` extends to an entire function of
finite order and `F` satisfies a functional equation; `a` has an Euler logarithm `b` with
`b n = O(n^θ)` for some `θ < 1/2`; and `a n = O(n^ε)` for every `ε > 0`. -/
def selbergClass : Set (ArithmeticFunction ℂ) :=
  {a | a 1 = 1 ∧
    (∃ F : ℂ → ℂ, IsLSeriesContinuation a F ∧
      (∃ (m : ℕ) (G : ℂ → ℂ) (β : ℝ), Differentiable ℂ G ∧ HasGrowthOrderLE G β ∧
        ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) ∧
      Nonempty (FunctionalEquation F)) ∧
    (∃ (b : ℕ → ℂ) (θ : ℝ), θ < 1 / 2 ∧ IsEulerLog a b ∧ ∃ C, ∀ n, ‖b n‖ ≤ C * (n : ℝ) ^ θ) ∧
    (∀ ε > (0 : ℝ), ∃ C, ∀ n, ‖a n‖ ≤ C * (n : ℝ) ^ ε)}

/-- Two continuations of the same Dirichlet series agree off `1`. -/
theorem IsLSeriesContinuation.eqOn_compl_one {a : ArithmeticFunction ℂ} {F F' : ℂ → ℂ}
    (hF : IsLSeriesContinuation a F) (hF' : IsLSeriesContinuation a F') :
    ∀ s : ℂ, s ≠ 1 → F s = F' s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h3 : F =ᶠ[𝓝 (2 : ℂ)] F' := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    rw [hF.1 s hs, hF'.1 s hs]
  intro s hs
  exact (hF.2.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hF'.2.analyticOnNhd hU) hpc (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) h3 hs

end ArithmeticFunction

/-- A coefficient bound `a n = O(n ^ ε)` for every `ε > 0` makes the Dirichlet series absolutely
convergent on `Re s > 1`. -/
theorem LSeriesSummable.of_forall_norm_le_mul_rpow {a : ℕ → ℂ}
    (hram : ∀ ε > (0 : ℝ), ∃ C, ∀ n, ‖a n‖ ≤ C * (n : ℝ) ^ ε) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable a s := by
  obtain ⟨C, hC⟩ := hram ((s.re - 1) / 2) (by linarith)
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1 + (s.re - 1) / 2) (by linarith) ⟨C, ?_⟩
  intro n _
  have : 1 + (s.re - 1) / 2 - 1 = (s.re - 1) / 2 := by ring
  rw [this]; exact hC n

/-- `Re (α s + r) > 0` when `α > 0`, `Re s > 0` and `Re r ≥ 0`. -/
theorem Complex.re_ofReal_mul_add_pos {α : ℝ} {r s : ℂ} (hα : 0 < α) (hr : 0 ≤ r.re)
    (hs : 0 < s.re) : 0 < ((α : ℂ) * s + r).re := by
  simp only [add_re, re_ofReal_mul]
  have := mul_pos hα hs
  linarith

namespace ArithmeticFunction

/-- **Coefficients of an Euler logarithm.** If `L(a, s) = exp L(b, s)` on `Re s > 1`, then
differentiating gives `log n · a n = ((log · b) ⍟ a) n` for `n ≠ 0`. -/
theorem IsEulerLog.logMul_eq_convolution {a : ArithmeticFunction ℂ} {b : ℕ → ℂ}
    (hb : IsEulerLog a b) (haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s)
    {n : ℕ} (hn : n ≠ 0) :
    LSeries.logMul (fun n => a n) n =
      (LSeries.convolution (LSeries.logMul b) (fun n => a n)) n := by
  have hA : LSeries.abscissaOfAbsConv (fun n => a n) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      haS y (by simpa using hy)
  have hB : LSeries.abscissaOfAbsConv b ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hb.2 y (by simpa using hy)).1
  have hlt : ∀ {f : ℕ → ℂ}, LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) → ∀ s : ℂ, 1 < s.re →
      LSeries.abscissaOfAbsConv f < s.re := fun h s hs => lt_of_le_of_lt h (by exact_mod_cast hs)
  have hAl : LSeries.abscissaOfAbsConv (LSeries.logMul fun n => a n) ≤ (1 : ℝ) := by
    rw [LSeries.abscissaOfAbsConv_logMul]; exact hA
  have hBl : LSeries.abscissaOfAbsConv (LSeries.logMul b) ≤ (1 : ℝ) := by
    rw [LSeries.abscissaOfAbsConv_logMul]; exact hB
  have hC : LSeries.abscissaOfAbsConv
      (LSeries.convolution (LSeries.logMul b) (fun n => a n)) ≤ (1 : ℝ) :=
    (LSeries.abscissaOfAbsConv_convolution_le _ _).trans (max_le hBl hA)
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have key : ∀ s : ℂ, 1 < s.re → LSeries (LSeries.logMul fun n => a n) s =
      LSeries (LSeries.convolution (LSeries.logMul b) (fun n => a n)) s := by
    intro s hs
    have h1 := LSeries_hasDerivAt (hlt hA s hs)
    have h2 := (LSeries_hasDerivAt (hlt hB s hs)).cexp
    have heq : (fun z => exp (LSeries b z)) =ᶠ[𝓝 s] LSeries (fun n => a n) := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact ((hb.2 z hz).2).symm
    have h3 := (h2.congr_of_eventuallyEq heq.symm)
    have := h1.unique h3
    rw [LSeries_convolution (hlt hBl s hs) (hlt hA s hs), ← (hb.2 s hs).2] at *
    linear_combination -this
  refine LSeries.eq_of_LSeries_eventually_eq ?_ ?_ ?_ hn
  · exact lt_of_le_of_lt hAl (EReal.coe_lt_top 1)
  · exact lt_of_le_of_lt hC (EReal.coe_lt_top 1)
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    exact key x (by simpa using hx)

/-- **The Euler-logarithm recursion at prime powers.** If `L(a, s) = exp L(b, s)` on `Re s > 1`,
then `k a(pᵏ) = ∑_{i ≤ k} i b(pⁱ) a(pᵏ⁻ⁱ)` for every prime `p`. -/
theorem IsEulerLog.natCast_mul_apply_prime_pow {a : ArithmeticFunction ℂ} {b : ℕ → ℂ}
    (hb : IsEulerLog a b) (haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (k : ℂ) * a (p ^ k) = ∑ i ∈ Finset.range (k + 1), (i : ℂ) * b (p ^ i) * a (p ^ (k - i)) := by
  have h := hb.logMul_eq_convolution haS (pow_ne_zero k hp.ne_zero)
  rw [LSeries.convolution_def] at h
  simp only [LSeries.logMul] at h
  rw [Nat.sum_divisorsAntidiagonal (fun x y => Complex.log (x : ℂ) * b x * a y),
    Nat.sum_divisors_prime_pow hp] at h
  have hL : (Real.log p : ℂ) ≠ 0 := by
    have : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    exact_mod_cast this.ne'
  have hlog : ∀ i : ℕ, Complex.log (((p ^ i : ℕ) : ℕ) : ℂ) = (i : ℂ) * (Real.log p : ℂ) := by
    intro i
    rw [← Complex.natCast_log, Nat.cast_pow, Real.log_pow]
    push_cast; ring
  have hdiv : ∀ i ∈ Finset.range (k + 1), p ^ k / p ^ i = p ^ (k - i) := fun i hi =>
    Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos
  rw [Finset.sum_congr rfl (fun i hi => by rw [hdiv i hi, hlog i])] at h
  rw [hlog k] at h
  apply mul_right_cancel₀ hL
  rw [Finset.sum_mul, mul_right_comm, h]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- An Euler logarithm vanishes at `1`. -/
theorem IsEulerLog.apply_one {a : ArithmeticFunction ℂ} {b : ℕ → ℂ} (hb : IsEulerLog a b) :
    b 1 = 0 := by
  by_contra h; exact not_isPrimePow_one (hb.1 1 h)

/-- **Uniqueness of the Euler logarithm.** If `a 1 = 1` and `L(a, s)` converges absolutely on
`Re s > 1`, then `a` has at most one Euler logarithm. -/
theorem IsEulerLog.unique {a : ArithmeticFunction ℂ} (ha1 : a 1 = 1)
    (haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s)
    {b₁ b₂ : ℕ → ℂ} (h₁ : IsEulerLog a b₁) (h₂ : IsEulerLog a b₂) : b₁ = b₂ := by
  have hpk : ∀ p : ℕ, p.Prime → ∀ k : ℕ, b₁ (p ^ k) = b₂ (p ^ k) := by
    intro p hp k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [h₁.apply_one, h₂.apply_one]
    have e1 := h₁.natCast_mul_apply_prime_pow haS hp k
    have e2 := h₂.natCast_mul_apply_prime_pow haS hp k
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, ha1] at e1 e2
    have hs : ∑ i ∈ Finset.range k, (i : ℂ) * b₁ (p ^ i) * a (p ^ (k - i)) =
        ∑ i ∈ Finset.range k, (i : ℂ) * b₂ (p ^ i) * a (p ^ (k - i)) :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.mp hi)]
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    apply mul_left_cancel₀ hk0
    linear_combination e2 - e1 - hs
  funext n
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, -, rfl⟩ := (isPrimePow_nat_iff n).1 hn
    exact hpk p hp k
  · have e1 : b₁ n = 0 := by by_contra h; exact hn (h₁.1 n h)
    have e2 : b₂ n = 0 := by by_contra h; exact hn (h₂.1 n h)
    rw [e1, e2]

/-- At a prime, the Euler logarithm coefficient is the coefficient itself: `b p = a p`. -/
theorem IsEulerLog.apply_prime {a : ArithmeticFunction ℂ} {b : ℕ → ℂ} (hb : IsEulerLog a b)
    (ha1 : a 1 = 1) (haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s)
    {p : ℕ} (hp : p.Prime) : b p = a p := by
  have h := hb.logMul_eq_convolution haS hp.ne_zero
  rw [LSeries.convolution_def] at h
  simp only [LSeries.logMul] at h
  rw [Nat.sum_divisorsAntidiagonal (fun x y => Complex.log (x : ℂ) * b x * a y),
    hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos, ha1] at h
  have hL : Complex.log (p : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    have : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    exact_mod_cast this.ne'
  simp only [Nat.cast_one, Complex.log_one, zero_mul, zero_add, mul_one] at h
  exact (mul_left_cancel₀ hL h).symm

end ArithmeticFunction

namespace SelbergClass

open ArithmeticFunction

/-- The Dirichlet series of a member of `𝒮` converges absolutely on `Re s > 1`. -/
theorem LSeriesSummable_of_mem {a : ArithmeticFunction ℂ} (ha : a ∈ selbergClass) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => a n) s :=
  LSeriesSummable.of_forall_norm_le_mul_rpow ha.2.2.2 hs

/-- **The functional equation on the half-plane `Re s < 1`.** For a functional equation of `F`
(with `F` holomorphic off `1`), analytic continuation extends the functional equation from the
strip `0 < Re s < 1` to every `s ≠ 0` with `Re s < 1`, solved for `F(s)`. -/
theorem FunctionalEquation.eq_of_re_lt_one {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (D : FunctionalEquation F) :
    ∀ s : ℂ, s.re < 1 → s ≠ 0 → F s = (D.Q : ℂ) ^ (-s) * (∏ i, (Gamma (D.α i * s + D.r i))⁻¹) *
      (D.w * starRingEnd ℂ ((D.Q : ℂ) ^ (1 - starRingEnd ℂ s) *
        (∏ i, Gamma (D.α i * (1 - starRingEnd ℂ s) + D.r i)) *
          F (1 - starRingEnd ℂ s))) := by
  have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
  set Φ : ℂ → ℂ := fun u => (D.Q : ℂ) ^ u * (∏ i, Gamma (D.α i * u + D.r i)) * F u
    with hΦ
  have hΦd : ∀ u : ℂ, 0 < u.re → u ≠ 1 → DifferentiableAt ℂ Φ u := by
    intro u hu hu1
    have hF : DifferentiableAt ℂ F u :=
      hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hu1)
    have hG : DifferentiableAt ℂ (fun u => ∏ i, Gamma (D.α i * u + D.r i)) u := by
      apply DifferentiableAt.fun_finsetProd
      intro i _
      apply DifferentiableAt.comp
      · apply differentiableAt_Gamma
        intro m hm
        have := congrArg re hm
        have h3 := re_ofReal_mul_add_pos (D.α_pos i) (D.r_re_nonneg i) hu
        simp only [neg_re, natCast_re] at this
        have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      · exact (differentiableAt_id.const_mul _).add_const _
    exact ((differentiableAt_id.const_cpow (Or.inl hQ0)).mul hG).mul hF
  set R : ℂ → ℂ := fun s => (D.Q : ℂ) ^ (-s) * (∏ i, (Gamma (D.α i * s + D.r i))⁻¹) *
      (D.w * starRingEnd ℂ (Φ (starRingEnd ℂ (1 - s)))) with hR
  have hRd : ∀ s : ℂ, s.re < 1 → s ≠ 0 → DifferentiableAt ℂ R s := by
    intro s hs hs0
    have h1 : DifferentiableAt ℂ (starRingEnd ℂ ∘ Φ ∘ starRingEnd ℂ) (1 - s) := by
      have hne : starRingEnd ℂ (1 - s) ≠ 1 := by
        intro h
        apply hs0
        have : 1 - s = 1 := by
          have := congrArg (starRingEnd ℂ) h
          simpa using this
        linear_combination -this
      have := (hΦd (starRingEnd ℂ (1 - s)) (by simp; linarith) hne).conj_conj
      simpa using this
    have h2 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s :=
      (differentiableAt_const 1).sub differentiableAt_id
    have h3 := (h1.comp s h2).const_mul D.w
    have h4 : DifferentiableAt ℂ (fun s : ℂ => (D.Q : ℂ) ^ (-s)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hQ0)
    have h5 : DifferentiableAt ℂ (fun s : ℂ => ∏ i, (Gamma (D.α i * s + D.r i))⁻¹) s := by
      apply DifferentiableAt.fun_finsetProd
      intro i _
      exact (differentiable_one_div_Gamma _).comp s
        ((differentiableAt_id.const_mul _).add_const _)
    exact (h4.mul h5).mul h3
  set V : Set ℂ := ({s | s.re < 0} ∪ {s | s.re < 1 ∧ 0 < s.im}) ∪
    ({s | s.re < 1 ∧ s.im < 0} ∪ {s | 0 < s.re ∧ s.re < 1}) with hV
  have hVo : IsOpen V := by
    refine ((isOpen_lt continuous_re continuous_const).union ?_).union
      (((isOpen_lt continuous_re continuous_const).inter
        (isOpen_lt continuous_im continuous_const)).union
        ((isOpen_lt continuous_const continuous_re).inter
          (isOpen_lt continuous_re continuous_const)))
    exact (isOpen_lt continuous_re continuous_const).inter
      (isOpen_lt continuous_const continuous_im)
  have hVpc : IsPreconnected V := by
    have hA : IsPreconnected {s : ℂ | s.re < 0} := (convex_halfSpace_re_lt 0).isPreconnected
    have hB : IsPreconnected {s : ℂ | s.re < 1 ∧ 0 < s.im} :=
      ((convex_halfSpace_re_lt 1).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hC : IsPreconnected {s : ℂ | s.re < 1 ∧ s.im < 0} :=
      ((convex_halfSpace_re_lt 1).inter (convex_halfSpace_im_lt 0)).isPreconnected
    have hE : IsPreconnected {s : ℂ | 0 < s.re ∧ s.re < 1} :=
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
    have hAB := hA.union (-1 + I) (by simp) (by simp) hB
    have hCE := hC.union (1 / 2 - I) (by simp; norm_num) (by simp; norm_num) hE
    exact hAB.union (1 / 2 + I) (Or.inr (by simp; norm_num)) (Or.inr (by simp; norm_num)) hCE
  have hmem : ∀ s : ℂ, s.re < 1 → s ≠ 0 → s ∈ V := by
    intro s hs hs0
    rcases lt_trichotomy s.im 0 with h | h | h
    · exact Or.inr (Or.inl ⟨hs, h⟩)
    · rcases lt_trichotomy s.re 0 with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact absurd (Complex.ext h' h) hs0
      · exact Or.inr (Or.inr ⟨h', hs⟩)
    · exact Or.inl (Or.inr ⟨hs, h⟩)
  have hVre : ∀ s ∈ V, s.re < 1 ∧ s ≠ 0 := by
    intro s hs
    rcases hs with (h | h) | (h | h)
    · refine ⟨by simp at h; linarith, fun h0 => by rw [h0] at h; simp at h⟩
    · refine ⟨h.1, fun h0 => by rw [h0] at h; simp at h⟩
    · refine ⟨h.1, fun h0 => by rw [h0] at h; simp at h⟩
    · refine ⟨h.2, fun h0 => by rw [h0] at h; simp at h⟩
  have hFa : AnalyticOnNhd ℂ F V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro s hs
    have h1 : s ≠ 1 := by
      intro h; have := (hVre s hs).1; rw [h] at this; simp at this
    exact (hFd.differentiableAt (isOpen_compl_singleton.mem_nhds h1)).differentiableWithinAt
  have hRa : AnalyticOnNhd ℂ R V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro s hs
    exact (hRd s (hVre s hs).1 (hVre s hs).2).differentiableWithinAt
  have hloc : F =ᶠ[𝓝 (1 / 2 : ℂ)] R := by
    have hstrip : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ 𝓝 (1 / 2 : ℂ) :=
      ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).mem_nhds (by norm_num)
    filter_upwards [hstrip] with s hs
    have he := D.eqn s hs.1 hs.2
    have hc : starRingEnd ℂ (1 - s) = 1 - starRingEnd ℂ s := by simp
    simp only [hR, hΦ, hc]
    rw [← he]
    have hG : ∀ i, Gamma (D.α i * s + D.r i) ≠ 0 := fun i =>
      Gamma_ne_zero_of_re_pos (re_ofReal_mul_add_pos (D.α_pos i) (D.r_re_nonneg i) hs.1)
    have hP : (∏ i, (Gamma (D.α i * s + D.r i))⁻¹) *
        ∏ i, Gamma (D.α i * s + D.r i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => inv_mul_cancel₀ (hG i))
    have hq : (D.Q : ℂ) ^ (-s) * (D.Q : ℂ) ^ s = 1 := by
      rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff_of_exponent_ne_zero
        (by intro h; rw [h] at hs; simp at hs) |>.mpr hQ0)]
    calc F s = ((D.Q : ℂ) ^ (-s) * (D.Q : ℂ) ^ s) * ((∏ i, (Gamma (D.α i * s + D.r i))⁻¹) *
          ∏ i, Gamma (D.α i * s + D.r i)) * F s := by rw [hq, hP]; ring
      _ = _ := by ring
  intro s hs hs0
  have := hFa.eqOn_of_preconnected_of_eventuallyEq hRa hVpc (hmem _ (by norm_num) (by norm_num))
    hloc (hmem s hs hs0)
  simpa only [hR, hΦ, map_sub, map_one] using this

/-- **Meromorphy at `s = 1`.** The continuation of a member of `𝒮` is meromorphic at `1`. -/
theorem meromorphicAt_one {a : ArithmeticFunction ℂ} (ha : a ∈ selbergClass) {F : ℂ → ℂ}
    (hF : IsLSeriesContinuation a F) : MeromorphicAt F 1 := by
  obtain ⟨-, ⟨F', hF', ⟨m, G, -, hG, -, hGF⟩, -⟩, -⟩ := ha
  have hev : (fun s => G s / (s - 1) ^ m) =ᶠ[𝓝[≠] 1] F := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (s - 1) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
    rw [hGF s hs, hF.eqOn_compl_one hF' s hs]
    field_simp
  refine MeromorphicAt.congr ?_ hev
  exact (hG.analyticAt 1).meromorphicAt.div
    (((MeromorphicAt.id 1).sub (MeromorphicAt.const 1 1)).pow m)

end SelbergClass
