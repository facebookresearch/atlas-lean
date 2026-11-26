/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.PrimeCounting.ModFourMeanValue

/-!
# Integers whose prime factors are all `≡ 3 (mod 4)`

This file proves the asymptotic formula of Gareth A. Jones and Alexander K. Zvonkin,
*A Number-Theoretic Problem Concerning Pseudo-Real Riemann Surfaces*, INTEGERS 25 (2025),
Article A75 (arXiv:2401.00270), for the number `g(x)` of integers `n ≤ x` all of whose prime
factors are `≡ 3 (mod 4)`:
`g(x) ~ √(e^γ / π) · (C / 2) · x / √(ln x)`
(`MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four`).

`g(x)` counts the `n ≤ x` all of whose prime factors are `≡ -1 (mod 4)` (including
`n = 1`). The constant `C = C(4, 1)` of Languasco and Zaccagnini is defined in the paper
by `∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q) = C / (ln x)^{1/2} + O((ln x)^{-3/2})`; it enters
here as the limit of `(ln x)^{1/2} ∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q)`.

## Proof

The paper derives the formula from Raikov's Tauberian theorem. This file uses only real-variable
arguments instead. Write `G(s) = ∑ g(n) n^{-s}` and `H(s) = ∑ h(n) n^{-s}` for `s > 1`, where `h`
is the indicator of the integers with no prime factor `≡ 3 (mod 4)`.

1. The mean-value theorem of `MathlibExt.NumberTheory.PrimeCounting.ModFourMeanValue`,
   applied to the indicator for the progression `3 mod 4`, gives
   `∑_{n ≤ x} g(n) / n ~ α √(ln x)` for some `α > 0`, and then `g(x) ~ (α / 2) x / √(ln x)`.
2. An Abelian argument turns the first asymptotic into `√ε · G(1 + ε) → α Γ(3/2) = α √π / 2`
   as `ε → 0⁺`.
3. The Euler products give `G(s) H(s) = ζ(s)`; with `(s - 1) ζ(s) → 1` this yields the limit of
   `√ε · H(1 + ε)`.
4. A log-log Abelian argument, through the integral formula
   `γ = -log ε - ε ∫_1^∞ log (log t) t^{-1-ε} dt`, compares `log H(1 + ε)` with the partial
   products in the hypothesis on `C`. This identifies `α = e^{γ/2} C / √π`.
-/

namespace MetaMathlibExt

namespace isEquivalent_card_primeFactors_three_mod_four

/-! ### A mean-value argument for the integers with all prime factors `≡ 3 (mod 4)` -/

section Elementary

open Asymptotics Filter Finset Nat Chebyshev ArithmeticFunction
open scoped Topology

/-- Indicator of positive integers all of whose prime factors are `≡ 3 mod 4`. -/
private noncomputable def tmG (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 = 3 then 1 else 0

private lemma tmG_zero : tmG 0 = 0 := by simp [tmG]

private lemma tmG_one : tmG 1 = 1 := by simp [tmG]

private lemma tmG_nonneg (n : ℕ) : 0 ≤ tmG n := by
  unfold tmG
  split_ifs <;> norm_num

private lemma tmG_le_one (n : ℕ) : tmG n ≤ 1 := by
  unfold tmG
  split_ifs <;> norm_num

/-- The indicator of positive integers all of whose prime factors satisfy `P` is completely
multiplicative. -/
private lemma tmPrimeFactorIndicator_mul (P : ℕ → Prop) [DecidablePred P] (m n : ℕ) :
    (if m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, P p then (1 : ℝ) else 0) =
      (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p then (1 : ℝ) else 0) *
        (if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p then (1 : ℝ) else 0) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Nat.primeFactors_mul hm hn]
  simp only [ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    Finset.forall_mem_union]
  split_ifs <;> simp_all

private lemma tmG_mul (m n : ℕ) : tmG (m * n) = tmG m * tmG n :=
  tmPrimeFactorIndicator_mul (fun p => p % 4 = 3) m n

/-- `tmG` on a prime is determined by the residue of the prime mod 4. -/
private lemma tmG_prime_eq {p : ℕ} (hp : p.Prime) :
    tmG p = if p % 4 = 3 then 1 else 0 := by
  simp [tmG, hp.ne_zero, hp.primeFactors]

/-- The residue `3` is a unit modulo `4`. -/
private lemma tm_isUnit_three : IsUnit (3 : ZMod 4) :=
  ⟨⟨3, 3, by decide, by decide⟩, rfl⟩

/-- The elementary mean-value argument for `tmG`: `∑_{n ≤ x} tmG n / n ~ α √(log x)` for some
`α > 0`, and then the count of `n ≤ x` with `tmG n = 1` is `~ (α / 2) x / √(log x)`. -/
private theorem partI : ∃ α : ℝ, 0 < α ∧
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ)) / √(Real.log x))
      atTop (𝓝 α) ∧
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n) * √(Real.log x) / x)
      atTop (𝓝 (α / 2)) := by
  let f : ℕ →*₀ ℝ :=
    { toFun := tmG, map_one' := tmG_one, map_mul' := tmG_mul,
      map_zero' := tmG_zero }
  apply exists_tendsto_sum_of_prime_mod_four f tmG_nonneg tmG_le_one 3 tm_isUnit_three
  intro p hp _
  change tmG p = _
  rw [tmG_prime_eq hp, ← ZMod.natCast_mod p 4]
  have hlt := Nat.mod_lt p (by decide : 0 < 4)
  interval_cases p % 4 <;> rfl

end Elementary

/-! ### An Abelian theorem for `√(log x)` growth -/

section Abelian

open Filter Topology

section AbelSqrtLogHelpers

open MeasureTheory

/-- `∫₀^∞ e^{-v} √v dv = Γ(3/2) = √π / 2`. -/
private theorem abelSqrtLog_integral_exp_neg_mul_sqrt :
    ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * √v = √Real.pi / 2 := by
  have h := Real.Gamma_eq_integral (s := 3 / 2) (by norm_num)
  have h32 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  rw [h32, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
    show (1 / 2 + 1 : ℝ) - 1 = 1 / 2 by norm_num] at h
  calc ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * √v
      = ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * v ^ (1 / 2 : ℝ) := by
        simp_rw [Real.sqrt_eq_rpow]
    _ = √Real.pi / 2 := by rw [← h]; ring

/-- `v ↦ e^{-v} √v` is integrable on `(0, ∞)`. -/
private theorem abelSqrtLog_integrableOn_exp_neg_mul_sqrt :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * √v) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := 3 / 2) (by norm_num)
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at h
  simpa only [Real.sqrt_eq_rpow] using h

/-- `v ↦ e^{-v}` is integrable on `(0, ∞)`. -/
private theorem abelSqrtLog_integrableOn_exp_neg :
    IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ioi 0) := by
  simpa using exp_neg_integrableOn_Ioi 0 one_pos

/-- Change of variables `t = exp (v / ε)` in `ε ∫_{(1, ∞)} t ^ (-ε - 1) S(t) dt`. -/
private theorem abelSqrtLog_mul_integral_rpow_eq (S : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi 1, t ^ (-ε - 1) * S t =
      ∫ v in Set.Ioi 0, Real.exp (-v) * S (Real.exp (v / ε)) := by
  have h1 := integral_comp_exp_Ioi (fun t : ℝ => t ^ (-ε - 1) * S t) 0
  rw [Real.exp_zero] at h1
  rw [← h1]
  have h2 := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-(ε * x)) * S (Real.exp x)) 0 (inv_pos.mpr hε)
  rw [mul_zero, inv_inv, smul_eq_mul] at h2
  have h3 : ∀ x : ℝ, Real.exp x • ((Real.exp x) ^ (-ε - 1) * S (Real.exp x)) =
      Real.exp (-(ε * x)) * S (Real.exp x) := by
    intro x
    rw [smul_eq_mul, ← mul_assoc, ← Real.exp_mul, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h3]
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

/-- A monotone `S` with `S x / √(log x) → α` satisfies `S x ≤ A √(log x) + B` for `x ≥ 1`. -/
private theorem abelSqrtLog_exists_bound {S : ℝ → ℝ} (hSm : Monotone S) {α : ℝ}
    (hA : Tendsto (fun x => S x / √(Real.log x)) atTop (𝓝 α)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → S x ≤ A * √(Real.log x) + B := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((hA.eventually (gt_mem_nhds (lt_add_one α))).and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨|α + 1|, |S T|, abs_nonneg _, abs_nonneg _, fun x hx => ?_⟩
  have hlog : 0 ≤ √(Real.log x) := Real.sqrt_nonneg _
  rcases le_or_gt T x with hTx | hxT
  · obtain ⟨h1, h2⟩ := hT x hTx
    have hpos : 0 < √(Real.log x) :=
      Real.sqrt_pos.mpr (Real.log_pos (by linarith))
    rw [div_lt_iff₀ hpos] at h1
    have : (α + 1) * √(Real.log x) ≤ |α + 1| * √(Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog
    linarith [abs_nonneg (S T)]
  · have h1 : S x ≤ S T := hSm hxT.le
    have h2 : 0 ≤ |α + 1| * √(Real.log x) := mul_nonneg (abs_nonneg _) hlog
    linarith [le_abs_self (S T)]

/-- The partial sums `t ↦ ∑_{0 < n ≤ t} c n` of a nonnegative sequence are monotone. -/
private theorem abelSqrtLog_partialSum_monotone {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) :
    Monotone (fun t : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n) := by
  intro s t hst
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hst)) fun i _ _ => hc i

/-- Dominated convergence: `∫₀^∞ e^{-v} √ε S(e^{v/ε}) dv → ∫₀^∞ e^{-v} α √v dv` as `ε → 0⁺`. -/
private theorem abelSqrtLog_tendsto_integral {S : ℝ → ℝ} (hS0 : ∀ x, 0 ≤ S x) (hSm : Monotone S)
    {α A B : ℝ} (hB : 0 ≤ B)
    (hA : Tendsto (fun x => S x / √(Real.log x)) atTop (𝓝 α))
    (hbound : ∀ x : ℝ, 1 ≤ x → S x ≤ A * √(Real.log x) + B) :
    Tendsto (fun ε : ℝ => ∫ v in Set.Ioi 0, Real.exp (-v) * (√ε * S (Real.exp (v / ε))))
      (𝓝[>] 0) (𝓝 (∫ v in Set.Ioi 0, Real.exp (-v) * (α * √v))) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => Real.exp (-v) * (A * √v + B)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hm : Measurable (fun v : ℝ => S (Real.exp (v / ε))) := by
      refine (hSm.comp fun a b hab => ?_).measurable
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hab hε.le)
    exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
      (measurable_const.mul hm)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε ⟨hε0, hε1⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v)
    have hx : 1 ≤ Real.exp (v / ε) := Real.one_le_exp (div_nonneg hv.le hε0.le)
    have h1 := hbound _ hx
    rw [Real.log_exp] at h1
    have h2 : √ε * √(v / ε) = √v := by
      rw [← Real.sqrt_mul hε0.le, mul_div_cancel₀ _ hε0.ne']
    have h3 : √ε ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hε1
    have h4 : 0 ≤ √ε := Real.sqrt_nonneg ε
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg h4 (hS0 _)))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    calc √ε * S (Real.exp (v / ε)) ≤ √ε * (A * √(v / ε) + B) :=
          mul_le_mul_of_nonneg_left h1 h4
      _ = A * (√ε * √(v / ε)) + √ε * B := by ring
      _ = A * √v + √ε * B := by rw [h2]
      _ ≤ A * √v + B := by nlinarith
  · have := (abelSqrtLog_integrableOn_exp_neg_mul_sqrt.const_mul A).add
      (abelSqrtLog_integrableOn_exp_neg.const_mul B)
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v)
    refine Tendsto.const_mul _ ?_
    have hlim : Tendsto (fun ε : ℝ => Real.exp (v / ε)) (𝓝[>] 0) atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      exact (tendsto_inv_nhdsGT_zero.const_mul_atTop hv).congr fun ε =>
        (div_eq_mul_inv v ε).symm
    have := (hA.comp hlim).mul_const (√v)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    simp only [Function.comp, Real.log_exp]
    rw [Real.sqrt_div hv.le]
    have : 0 < √v := Real.sqrt_pos.mpr hv
    have : 0 < √ε := Real.sqrt_pos.mpr hε
    field_simp

/-- Abel summation: if the partial sums are `O(t ^ (ε / 2))`, then
`∑ c n / n ^ ε = ε ∫_{(1, ∞)} t ^ (-ε - 1) S(t) dt`. -/
private theorem abelSqrtLog_hasSum_div_rpow {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, 1 ≤ t → ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n ≤ C * t ^ (ε / 2)) :
    HasSum (fun n : ℕ => c n / (n : ℝ) ^ ε)
      (ε * ∫ t in Set.Ioi 1, t ^ (-ε - 1) * ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n) := by
  set c' : ℕ → ℝ := fun n => if n = 0 then 0 else c n
  have hc'0 : c' 0 = 0 := by simp [c']
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, c' k = ∑ k ∈ Finset.Ioc 0 m, c k := by
    intro m
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons, hc'0, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [c', (Finset.mem_Ioc.mp hk).1.ne']
  have hS0 : ∀ t : ℝ, 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n := fun t =>
    Finset.sum_nonneg fun i _ => hc i
  have hderiv : deriv (fun t : ℝ => t ^ (-ε)) = fun t => -ε * t ^ (-ε - 1) :=
    Real.deriv_rpow_const' _
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun t : ℝ => t ^ (-ε)) t :=
    fun t ht => Real.differentiableAt_rpow_const_of_ne _
      (zero_lt_one.trans_le (Set.mem_Ici.mp ht)).ne'
  have hf_int : LocallyIntegrableOn (deriv fun t : ℝ => t ^ (-ε)) (Set.Ici 1) := by
    rw [hderiv]
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun x hx =>
      Or.inl (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne')
  have h_lim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Icc 0 n, c' k) atTop
      (𝓝 0) := by
    simp_rw [hsum]
    have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(ε / 2))) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < ε / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul C
      rwa [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.sum_nonneg fun i _ => hc i)) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    have h1 := hC n hn'
    rw [Nat.floor_natCast] at h1
    calc (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Ioc 0 n, c k
        ≤ (n : ℝ) ^ (-ε) * (C * (n : ℝ) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = C * ((n : ℝ) ^ (-ε) * (n : ℝ) ^ (ε / 2)) := by ring
      _ = C * (n : ℝ) ^ (-(ε / 2)) := by
        rw [← Real.rpow_add (by linarith)]
        congr 2
        ring
  have hg_dom : (fun t : ℝ => deriv (fun t : ℝ => t ^ (-ε)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c' k) =O[atTop] fun t : ℝ => t ^ (-ε / 2 - 1) := by
    simp_rw [hderiv, hsum]
    refine Asymptotics.IsBigO.of_bound (ε * C) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_mul, abs_mul, abs_neg, abs_of_pos hε, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_of_nonneg (hS0 t)]
    calc ε * t ^ (-ε - 1) * ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k
        ≤ ε * t ^ (-ε - 1) * (C * t ^ (ε / 2)) := by
          gcongr
          exact hC t ht
      _ = ε * C * (t ^ (-ε - 1) * t ^ (ε / 2)) := by ring
      _ = ε * C * t ^ (-ε / 2 - 1) := by
        rw [← Real.rpow_add ht0]
        congr 2
        ring
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-ε / 2 - 1)) atTop :=
    integrableAtFilter_rpow_atTop_iff.mpr (by linarith)
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c' hc'0 hf_diff hf_int h_lim
    hg_dom hg_int
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n => div_nonneg (hc n) (Real.rpow_nonneg (Nat.cast_nonneg n) ε)),
    ← tendsto_add_atTop_iff_nat 1]
  simp_rw [Nat.range_succ_eq_Icc_zero]
  have hval : (0 : ℝ) - ∫ t in Set.Ioi 1, deriv (fun t : ℝ => t ^ (-ε)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c' k =
      ε * ∫ t in Set.Ioi 1, t ^ (-ε - 1) * ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n := by
    simp_rw [hderiv, hsum, mul_assoc]
    rw [integral_const_mul]
    ring
  rw [hval] at key
  refine key.congr fun n => Finset.sum_congr rfl fun k _ => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hc'0, Real.zero_rpow hε.ne']
  · simp only [c', hk, ↓reduceIte]
    rw [Real.rpow_neg (Nat.cast_nonneg k), div_eq_inv_mul]

end AbelSqrtLogHelpers

/-- An Abelian theorem: if the partial sums of a nonnegative sequence `c` grow like
`α √(log x)`, then `√ε ∑ c n / n ^ ε → α Γ(3/2) = α √π / 2` as `ε → 0⁺`. -/
private theorem abel_sqrt_log {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {α : ℝ}
    (hA : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c n) / √(Real.log x))
      atTop (𝓝 α)) :
    Tendsto (fun ε : ℝ => √ε * ∑' n : ℕ, c n / (n : ℝ) ^ ε) (𝓝[>] 0)
      (𝓝 (α * (√Real.pi / 2))) := by
  have hSm := abelSqrtLog_partialSum_monotone hc
  have hS0 : ∀ t : ℝ, 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n := fun t =>
    Finset.sum_nonneg fun i _ => hc i
  obtain ⟨A, B, hA0, hB0, hbound⟩ := abelSqrtLog_exists_bound hSm hA
  have hlim := abelSqrtLog_tendsto_integral hS0 hSm hB0 hA hbound
  have hval : ∫ v in Set.Ioi 0, Real.exp (-v) * (α * √v) = α * (√Real.pi / 2) := by
    simp_rw [mul_left_comm (Real.exp _) α]
    rw [MeasureTheory.integral_const_mul, abelSqrtLog_integral_exp_neg_mul_sqrt]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hC : ∀ t : ℝ, 1 ≤ t → ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n ≤ (A / √ε + B) * t ^ (ε / 2) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    have h1 : √(Real.log t) ≤ t ^ (ε / 2) / √ε := by
      calc √(Real.log t) ≤ √(t ^ ε / ε) := Real.sqrt_le_sqrt (Real.log_le_rpow_div ht0 hε)
        _ = t ^ (ε / 2) / √ε := by
          rw [Real.sqrt_div (Real.rpow_nonneg ht0 _), Real.sqrt_eq_rpow (t ^ ε),
            ← Real.rpow_mul ht0, show ε * (1 / 2) = ε / 2 by ring]
    have h2 : 1 ≤ t ^ (ε / 2) := Real.one_le_rpow ht (by linarith)
    calc ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n ≤ A * √(Real.log t) + B := hbound t ht
      _ ≤ A * (t ^ (ε / 2) / √ε) + B * t ^ (ε / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hA0) (le_mul_of_one_le_right hB0 h2)
      _ = (A / √ε + B) * t ^ (ε / 2) := by ring
  have hsum := abelSqrtLog_hasSum_div_rpow hc hε hC
  have hcov := abelSqrtLog_mul_integral_rpow_eq
    (fun t => ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n) hε
  rw [hsum.tsum_eq, hcov, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  ring

end Abelian

/-! ### Euler products -/

section EulerProducts

open Filter Topology

/-- Indicator of positive integers with no prime factor `≡ 3 mod 4`. -/
private noncomputable def tmH (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 then 1 else 0

/-- Weights `-log (1 - 1/p)` on the primes `p` with `p % 4 ≠ 3`. -/
private noncomputable def tmW (n : ℕ) : ℝ :=
  if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - 1 / (n : ℝ)) else 0

/-! ### Complete multiplicativity of prime-factor indicators -/

/-- Indicator of the positive integers, written in the same shape as `tmG` and `tmH`. -/
private noncomputable def tmPosIndicator (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, True then 1 else 0

private lemma tmH_mul (m n : ℕ) : tmH (m * n) = tmH m * tmH n :=
  tmPrimeFactorIndicator_mul (fun p => p % 4 ≠ 3) m n

private lemma tmPosIndicator_mul (m n : ℕ) :
    tmPosIndicator (m * n) = tmPosIndicator m * tmPosIndicator n :=
  tmPrimeFactorIndicator_mul (fun _ => True) m n

private lemma tmH_zero : tmH 0 = 0 := by simp [tmH]

private lemma tmPosIndicator_zero : tmPosIndicator 0 = 0 := by simp [tmPosIndicator]

private lemma tmH_one : tmH 1 = 1 := by simp [tmH]

private lemma tmPosIndicator_one : tmPosIndicator 1 = 1 := by simp [tmPosIndicator]

private lemma tmH_prime {p : ℕ} (hp : p.Prime) :
    tmH p = if p % 4 ≠ 3 then 1 else 0 := by
  simp [tmH, hp.primeFactors, hp.ne_zero]

private lemma tmPosIndicator_of_ne_zero {n : ℕ} (hn : n ≠ 0) : tmPosIndicator n = 1 := by
  simp [tmPosIndicator, hn]

/-- The completely multiplicative function `n ↦ a n / n ^ s`. -/
private noncomputable def tmDirichletHom (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n, a (m * n) = a m * a n) (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := a n / (n : ℝ) ^ s
  map_zero' := by simp [h0]
  map_one' := by simp [h1]
  map_mul' m n := by
    simp only [Nat.cast_mul, hmul]
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_div_mul_comm]

private lemma tmDirichletHom_apply (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n, a (m * n) = a m * a n) (s : ℝ) (n : ℕ) :
    tmDirichletHom a h0 h1 hmul s n = a n / (n : ℝ) ^ s :=
  rfl

private lemma tmDirichletHom_summable_norm (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n, a (m * n) = a m * a n) (ha : ∀ n, |a n| ≤ 1) {s : ℝ} (hs : 1 < s) :
    Summable (fun n => ‖tmDirichletHom a h0 h1 hmul s n‖) := by
  refine (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_)
  rw [tmDirichletHom_apply, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  exact div_le_div_of_nonneg_right (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

private lemma tm_abs_ite_one_zero_le_one {P : Prop} [Decidable P] :
    |(if P then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-- The Euler products give `G(s) H(s) = ζ(s)` for real `s > 1`, where `G` and `H` are the
Dirichlet series of `tmG` and `tmH`. -/
private theorem tsum_tmG_mul_tsum_tmH {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, tmG n / (n : ℝ) ^ s) * (∑' n : ℕ, tmH n / (n : ℝ) ^ s) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  have hG := EulerProduct.eulerProduct_completely_multiplicative
    (tmDirichletHom_summable_norm tmG tmG_zero tmG_one tmG_mul
      (fun _ => tm_abs_ite_one_zero_le_one) hs)
  have hH := EulerProduct.eulerProduct_completely_multiplicative
    (tmDirichletHom_summable_norm tmH tmH_zero tmH_one tmH_mul
      (fun _ => tm_abs_ite_one_zero_le_one) hs)
  have hZ := EulerProduct.eulerProduct_completely_multiplicative
    (tmDirichletHom_summable_norm tmPosIndicator tmPosIndicator_zero tmPosIndicator_one
      tmPosIndicator_mul (fun _ => tm_abs_ite_one_zero_le_one) hs)
  simp only [tmDirichletHom_apply] at hG hH hZ
  have key : ∀ N : ℕ,
      (∏ p ∈ N.primesBelow, (1 - tmG p / (p : ℝ) ^ s)⁻¹) *
          (∏ p ∈ N.primesBelow, (1 - tmH p / (p : ℝ) ^ s)⁻¹) =
        ∏ p ∈ N.primesBelow, (1 - tmPosIndicator p / (p : ℝ) ^ s)⁻¹ := by
    intro N
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primesBelow hp
    rw [tmG_prime_eq hp', tmH_prime hp', tmPosIndicator_of_ne_zero hp'.ne_zero]
    by_cases h4 : p % 4 = 3 <;> simp [h4]
  rw [tendsto_nhds_unique ((hG.mul hH).congr key) hZ]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tmPosIndicator_zero, Real.zero_rpow (by linarith : s ≠ 0)]
  · rw [tmPosIndicator_of_ne_zero hn]

private lemma tmH_div_rpow_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ tmH n / (n : ℝ) ^ s :=
  div_nonneg (by unfold tmH; split_ifs <;> norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

/-- The terms `-log (1 - p ^ (-s))` over primes `p % 4 ≠ 3` are nonnegative. -/
private lemma tm_prime_neg_log_term_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ (if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-s)) else 0) := by
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h.1.one_lt.le
    have h2 : (n : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have h3 : 0 ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have := Real.log_nonpos (by linarith) (by linarith : 1 - (n : ℝ) ^ (-s) ≤ 1)
    linarith
  · exact le_rfl

/-- The logarithm of the Euler product of `H(s)`: a sum of `-log (1 - p ^ (-s))` over the primes
`p` with `p % 4 ≠ 3`. -/
private theorem hasSum_log_tsum_tmH {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-s)) else 0)
      (Real.log (∑' n : ℕ, tmH n / (n : ℝ) ^ s)) := by
  have hsumH := tmDirichletHom_summable_norm tmH tmH_zero tmH_one tmH_mul
    (fun _ => tm_abs_ite_one_zero_le_one) hs
  have hH := EulerProduct.eulerProduct_completely_multiplicative hsumH
  simp only [tmDirichletHom_apply] at hH hsumH
  have hpos : 0 < ∑' n : ℕ, tmH n / (n : ℝ) ^ s := by
    have h1 := (Summable.of_norm hsumH).le_tsum 1 (fun j _ => tmH_div_rpow_nonneg s j)
    simp only [tmH_one, Nat.cast_one, Real.one_rpow, div_one] at h1
    linarith
  have hlog := ((Real.continuousAt_log hpos.ne').tendsto).comp hH
  rw [hasSum_iff_tendsto_nat_of_nonneg (tm_prime_neg_log_term_nonneg (by linarith))]
  refine hlog.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [Real.log_prod (fun p hp => ?_)]
  · simp only [Nat.primesBelow, Finset.sum_filter, ite_and]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hp h4
    · rw [tmH_prime hp, ite_eq_left h4, Real.log_inv, Real.rpow_neg (Nat.cast_nonneg p),
        one_div]
    · rw [tmH_prime hp, ite_eq_right h4]
      simp
    · rfl
  · have hp' := Nat.prime_of_mem_primesBelow hp
    rw [tmH_prime hp']
    split_ifs with h4
    · have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
      have h2 : 1 < (p : ℝ) ^ s := Real.one_lt_rpow h1 (by linarith)
      have h3 : 1 / (p : ℝ) ^ s < 1 := by rw [div_lt_one (by linarith)]; exact h2
      exact inv_ne_zero (by linarith)
    · simp

/-! ### The limit `ε → 0⁺` -/

/-- For `0 ≤ t ≤ 1/2`, `0 ≤ -log (1 - t) - t ≤ 2 t ^ 2`. -/
private lemma tm_neg_log_one_sub_sub_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    0 ≤ -Real.log (1 - t) - t ∧ -Real.log (1 - t) - t ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  refine ⟨by linarith [Real.log_le_sub_one_of_pos hpos], ?_⟩
  have habs : |t| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg h0] at h
  have h2 : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg t]
  have h3 := neg_abs_le (t + Real.log (1 - t))
  linarith

/-- For `0 ≤ x ≤ 1/2` and `0 ≤ y ≤ 1`, `|-log (1 - x y) - y (-log (1 - x))| ≤ 2 x ^ 2`. -/
private lemma tm_abs_neg_log_mul_sub_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    |-Real.log (1 - x * y) - -Real.log (1 - x) * y| ≤ 2 * x ^ 2 := by
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ x := mul_le_of_le_one_right hx0 hy1
  obtain ⟨h1, h2⟩ := tm_neg_log_one_sub_sub_bounds hxy0 (by linarith)
  obtain ⟨h3, h4⟩ := tm_neg_log_one_sub_sub_bounds hx0 hx1
  have e : -Real.log (1 - x * y) - -Real.log (1 - x) * y =
      (-Real.log (1 - x * y) - x * y) - y * (-Real.log (1 - x) - x) := by ring
  rw [e]
  refine abs_sub_le_of_nonneg_of_le h1 ?_ (mul_nonneg hy0 h3) ?_
  · nlinarith
  · nlinarith

/-- As `ε → 0⁺`, `log H(1 + ε)` and the Dirichlet series `∑ tmW n / n ^ ε` differ by `o(1)`. -/
private theorem tendsto_tsum_log_sub_tsum_tmW :
    Tendsto (fun ε : ℝ =>
      (∑' n : ℕ, if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) else 0) -
        ∑' n : ℕ, tmW n / (n : ℝ) ^ ε)
      (𝓝[>] 0) (𝓝 0) := by
  set A : ℝ → ℕ → ℝ := fun ε n =>
    if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) else 0 with hA_def
  set B : ℝ → ℕ → ℝ := fun ε n => tmW n / (n : ℝ) ^ ε with hB_def
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ‖A ε n - B ε n‖ ≤ 2 / (n : ℝ) ^ 2 := by
    intro ε hε n
    by_cases h : n.Prime ∧ n % 4 ≠ 3
    · simp only [hA_def, hB_def, tmW]
      rw [ite_eq_left h, ite_eq_left h]
      have hn : (0 : ℝ) < n := by exact_mod_cast h.1.pos
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1.two_le
      have hy1 : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
      have hrpow : (n : ℝ) ^ (-(1 + ε)) = 1 / (n : ℝ) * (1 / (n : ℝ) ^ ε) := by
        rw [Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one]
        field_simp
      rw [hrpow, Real.norm_eq_abs, div_eq_mul_one_div (-Real.log (1 - 1 / (n : ℝ)))]
      have hx1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
      have hy : 1 / (n : ℝ) ^ ε ≤ 1 := by rw [div_le_one (by linarith)]; exact hy1
      calc _ ≤ 2 * (1 / (n : ℝ)) ^ 2 :=
            tm_abs_neg_log_mul_sub_le (by positivity) hx1 (by positivity) hy
        _ = 2 / (n : ℝ) ^ 2 := by ring
    · simp only [hA_def, hB_def, tmW]
      rw [ite_eq_right h, ite_eq_right h]
      simp only [zero_div, sub_zero, norm_zero]
      positivity
  have hsum_bound : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2).congr fun n => mul_one_div _ _
  have hA : ∀ ε : ℝ, 0 < ε → Summable (A ε) := fun ε hε =>
    (hasSum_log_tsum_tmH (by linarith : 1 < 1 + ε)).summable
  have hAB : ∀ ε : ℝ, 0 < ε → Summable (fun n => A ε n - B ε n) := fun ε hε =>
    hsum_bound.of_norm_bounded (hbound ε hε)
  have hB : ∀ ε : ℝ, 0 < ε → Summable (B ε) := fun ε hε => by
    simpa using (hA ε hε).sub (hAB ε hε)
  have hpt : ∀ n : ℕ, Tendsto (fun ε => A ε n - B ε n) (𝓝[>] 0) (𝓝 0) := by
    intro n
    by_cases h : n.Prime ∧ n % 4 ≠ 3
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h.1.ne_zero
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1.two_le
      have h1 : (1 : ℝ) - (n : ℝ) ^ (-(1 + 0 : ℝ)) ≠ 0 := by
        rw [add_zero, Real.rpow_neg_one]
        have : (n : ℝ)⁻¹ ≤ 1 / 2 := by
          rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hn2
        linarith
      have hc : ContinuousAt (fun ε : ℝ => -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) -
          -Real.log (1 - 1 / (n : ℝ)) / (n : ℝ) ^ ε) 0 := by
        fun_prop (disch := first | exact hn0 | exact h1 | simp)
      have h0 : -Real.log (1 - (n : ℝ) ^ (-(1 + 0 : ℝ))) -
          -Real.log (1 - 1 / (n : ℝ)) / (n : ℝ) ^ (0 : ℝ) = 0 := by
        simp [Real.rpow_neg_one]
      have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 0) (h0 ▸ hc.tendsto)
      refine this.congr fun ε => ?_
      simp only [hA_def, hB_def, tmW]
      rw [ite_eq_left h, ite_eq_left h]
    · have : ∀ ε, A ε n - B ε n = 0 := fun ε => by
        simp only [hA_def, hB_def, tmW]
        rw [ite_eq_right h, ite_eq_right h]
        simp
      simp only [this]
      exact tendsto_const_nhds
  have hlim : Tendsto (fun ε => ∑' n, (A ε n - B ε n)) (𝓝[>] 0) (𝓝 (∑' _ : ℕ, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence hsum_bound hpt
      (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
  rw [tsum_zero] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact (hA ε hε).tsum_sub (hB ε hε)

end EulerProducts

/-! ### A log-log Abelian theorem and the constant `C` -/

section LogLog

open Filter Topology

section Helpers

open MeasureTheory Asymptotics

private lemma abelLogLog_tmW_zero : tmW 0 = 0 := by
  simp [tmW, Nat.not_prime_zero]

private lemma abelLogLog_one_sub_one_div_prime_pos {n : ℕ} (hn : n.Prime) :
    0 < 1 - 1 / (n : ℝ) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

private lemma abelLogLog_tmW_nonneg (n : ℕ) : 0 ≤ tmW n := by
  unfold tmW
  split_ifs with h
  · have hpos := abelLogLog_one_sub_one_div_prime_pos h.1
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    exact neg_nonneg.mpr (Real.log_nonpos hpos.le (by linarith))
  · exact le_rfl

private lemma abelLogLog_tmW_le_two_div (n : ℕ) : tmW n ≤ 2 / n := by
  unfold tmW
  split_ifs with h
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1.two_le
    have hpos := abelLogLog_one_sub_one_div_prime_pos h.1
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hlog
    refine hlog.trans ?_
    have hn1 : (0 : ℝ) < n - 1 := by linarith
    have e : (1 - 1 / (n : ℝ))⁻¹ - 1 = 1 / (n - 1) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hn1 (by linarith)]
    linarith
  · positivity

private lemma abelLogLog_tmW_eq_ite_two_add_ite (n : ℕ) :
    tmW n = (if n = 2 then Real.log 2 else 0) +
    (if n.Prime ∧ n % 4 = 1 then -Real.log (1 - 1 / (n : ℝ)) else 0) := by
  unfold tmW
  by_cases h2 : n = 2
  · subst h2
    norm_num [Nat.prime_two]
    rw [one_div, Real.log_inv, neg_neg]
  · simp only [h2, ↓reduceIte, zero_add]
    by_cases hp : n.Prime
    · have hodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      have hiff : (n % 4 ≠ 3) ↔ (n % 4 = 1) := by omega
      simp only [hp, true_and, hiff]
    · simp [hp]

private lemma abelLogLog_sum_Icc_tmW_eq {x : ℕ} (hx : 2 ≤ x) :
    ∑ n ∈ Finset.Icc 0 x, tmW n = Real.log 2 +
      ∑ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1),
        -Real.log (1 - 1 / (q : ℝ)) := by
  simp_rw [abelLogLog_tmW_eq_ite_two_add_ite, Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [Finset.sum_filter, Nat.range_succ_eq_Icc_zero]
  simp only [Finset.mem_Icc, zero_le, hx, and_self, ↓reduceIte]

private lemma abelLogLog_sqrt_log_mul_prod_eq {x : ℕ} (hx : 2 ≤ x) :
    √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)) =
      2 * Real.exp (-(∑ n ∈ Finset.Icc 0 x, tmW n - 1 / 2 * Real.log (Real.log x))) := by
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hlog : 0 < Real.log x := Real.log_pos hx1
  set S := (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1)
  have hprod : ∏ q ∈ S, (1 - 1 / (q : ℝ)) = Real.exp (∑ q ∈ S, Real.log (1 - 1 / (q : ℝ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun q hq => (Real.exp_log ?_).symm
    exact abelLogLog_one_sub_one_div_prime_pos (Finset.mem_filter.mp hq).2.1
  rw [hprod, abelLogLog_sum_Icc_tmW_eq hx, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlog,
    ← Real.exp_add]
  have e : -(Real.log 2 + ∑ q ∈ S, -Real.log (1 - 1 / (q : ℝ)) - 1 / 2 * Real.log (Real.log x))
      = -Real.log 2 + (Real.log (Real.log x) * (1 / 2) + ∑ q ∈ S, Real.log (1 - 1 / (q : ℝ))) := by
    rw [Finset.sum_neg_distrib]
    ring
  rw [e, Real.exp_add (-Real.log 2), Real.exp_neg, Real.exp_log two_pos, ← mul_assoc,
    mul_inv_cancel₀ two_ne_zero, one_mul, Real.exp_add]

private lemma abelLogLog_log_sub_log_le_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  rw [← Real.log_div ha.ne' hb.ne']
  calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
    _ = (a - b) / b := by field_simp

private lemma abelLogLog_tendsto_log_log_sub_log_log_floor :
    Tendsto (fun t : ℝ => Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hup : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) * Real.log 2)⁻¹) atTop (𝓝 0) :=
    ((tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).atTop_mul_const
      hlog2).inv_tendsto_atTop
  have hbounds : ∀ t : ℝ, 2 ≤ t → 0 ≤ Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ∧
      Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ≤ ((⌊t⌋₊ : ℝ) * Real.log 2)⁻¹ := by
    intro t ht
    have hn2 : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast ht)
    have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have htn : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have hn0 : (0 : ℝ) < ⌊t⌋₊ := by linarith
    have hlogn : Real.log 2 ≤ Real.log ⌊t⌋₊ := Real.log_le_log two_pos hn2
    have hlognt : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hn0 hnt
    have hlogn0 : 0 < Real.log ⌊t⌋₊ := lt_of_lt_of_le hlog2 hlogn
    refine ⟨sub_nonneg.mpr (Real.log_le_log hlogn0 hlognt), ?_⟩
    calc Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊)
        ≤ (Real.log t - Real.log ⌊t⌋₊) / Real.log ⌊t⌋₊ :=
          abelLogLog_log_sub_log_le_div (by linarith) hlogn0
      _ ≤ ((t - ⌊t⌋₊) / ⌊t⌋₊) / Real.log ⌊t⌋₊ := by
          gcongr
          exact abelLogLog_log_sub_log_le_div (by linarith) hn0
      _ ≤ (1 / ⌊t⌋₊) / Real.log 2 := by
          gcongr
          linarith
      _ = ((⌊t⌋₊ : ℝ) * Real.log 2)⁻¹ := by
          rw [div_div, one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with t ht
    exact (hbounds t ht).1
  · filter_upwards [eventually_ge_atTop 2] with t ht
    exact (hbounds t ht).2

private lemma abelLogLog_tendsto_two_mul_exp_neg {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => 2 * Real.exp
      (-(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, tmW n - 1 / 2 * Real.log (Real.log t)))) atTop (𝓝 C) := by
  have h1 := hC.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 : Tendsto (fun t : ℝ => Real.exp
      (1 / 2 * (Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊)))) atTop (𝓝 1) := by
    have := (abelLogLog_tendsto_log_log_sub_log_log_floor.const_mul (1 / 2)).rexp
    simpa using this
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with t ht
  have hn : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  simp only [Function.comp_apply]
  rw [abelLogLog_sqrt_log_mul_prod_eq hn, mul_assoc, ← Real.exp_add]
  congr 2
  ring

private lemma abelLogLog_sum_Icc_tmW_nonneg (N : ℕ) : 0 ≤ ∑ k ∈ Finset.Icc 0 N, tmW k :=
  Finset.sum_nonneg fun k _ => abelLogLog_tmW_nonneg k

private lemma abelLogLog_sum_Icc_tmW_le_log {t : ℝ} (ht : 1 ≤ t) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k ≤ 2 * (1 + Real.log t) := by
  calc ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k ≤ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, 2 * ((k : ℝ))⁻¹ :=
        Finset.sum_le_sum fun k _ => (abelLogLog_tmW_le_two_div k).trans_eq (by rw [div_eq_mul_inv])
    _ = 2 * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((k : ℝ))⁻¹ := by
        rw [← Finset.mul_sum]
        congr 1
        refine (Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)).symm
        · simp only [Finset.mem_Icc] at hk ⊢
          omega
        · simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
          have : k = 0 := by omega
          simp [this]
    _ = 2 * (harmonic ⌊t⌋₊ : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ 2 * (1 + Real.log t) := by
        gcongr
        exact harmonic_floor_le_one_add_log t ht

private lemma abelLogLog_sum_Icc_tmW_le_rpow {t δ : ℝ} (ht : 1 ≤ t) (hδ : 0 < δ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k ≤ (2 + 2 / δ) * t ^ δ := by
  have h1 : 1 ≤ t ^ δ := Real.one_le_rpow ht hδ.le
  have h2 : Real.log t ≤ t ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ
  calc _ ≤ 2 * (1 + Real.log t) := abelLogLog_sum_Icc_tmW_le_log ht
    _ ≤ 2 * (t ^ δ + t ^ δ / δ) := by gcongr
    _ = (2 + 2 / δ) * t ^ δ := by ring

private lemma abelLogLog_isBigO_rpow_mul_sum_Icc_tmW {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) =O[atTop]
      (fun t : ℝ => t ^ (-1 - ε / 2)) := by
  refine IsBigO.of_bound (2 + 2 / (ε / 2)) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hW := abelLogLog_sum_Icc_tmW_nonneg ⌊t⌋₊
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (by positivity)]
  calc t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k
      ≤ t ^ (-1 - ε) * ((2 + 2 / (ε / 2)) * t ^ (ε / 2)) := by
        gcongr
        exact abelLogLog_sum_Icc_tmW_le_rpow ht (by positivity)
    _ = (2 + 2 / (ε / 2)) * t ^ (-1 - ε / 2) := by
        rw [mul_left_comm, ← Real.rpow_add ht0]
        congr 2
        ring

private lemma abelLogLog_tendsto_rpow_neg_mul_sum_Icc_tmW {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Icc 0 n, tmW k) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (2 + 2 / (ε / 2)) * (n : ℝ) ^ (-(ε / 2))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by positivity : 0 < ε / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul (2 + 2 / (ε / 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with n
    have := abelLogLog_sum_Icc_tmW_nonneg n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hW := abelLogLog_sum_Icc_tmW_le_rpow hn1 (by positivity : 0 < ε / 2)
    rw [Nat.floor_natCast] at hW
    calc (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Icc 0 n, tmW k
        ≤ (n : ℝ) ^ (-ε) * ((2 + 2 / (ε / 2)) * (n : ℝ) ^ (ε / 2)) := by gcongr
      _ = (2 + 2 / (ε / 2)) * (n : ℝ) ^ (-(ε / 2)) := by
        rw [mul_left_comm, ← Real.rpow_add (by linarith)]
        congr 2
        ring

private lemma abelLogLog_integrableAtFilter_rpow {a : ℝ} (ha : a < -1) :
    IntegrableAtFilter (fun t : ℝ => t ^ a) atTop :=
  ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt ha one_pos⟩

private lemma abelLogLog_integrableOn_rpow_mul_sum_Icc_tmW {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) (Set.Ioi 1) := by
  have hloc : LocallyIntegrableOn (fun t : ℝ => t ^ (-1 - ε)) (Set.Ici 1) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    exact continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le one_pos ht).ne'
  have := (locallyIntegrableOn_mul_sum_Icc tmW (m := 0) zero_le_one
    hloc).integrableOn_of_isBigO_atTop (abelLogLog_isBigO_rpow_mul_sum_Icc_tmW hε)
    (abelLogLog_integrableAtFilter_rpow (by linarith))
  exact this.mono_set Set.Ioi_subset_Ici_self

private lemma abelLogLog_hasSum_tmW_div_rpow {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => tmW n / (n : ℝ) ^ ε)
      (ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) := by
  have hderiv : ∀ t : ℝ, 0 < t → deriv (fun x : ℝ => x ^ (-ε)) t = -ε * t ^ (-1 - ε) := by
    intro t ht
    rw [(Real.hasDerivAt_rpow_const (Or.inl ht.ne')).deriv]
    congr 2
    ring
  have hdiff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => x ^ (-ε)) t :=
    fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (lt_of_lt_of_le one_pos ht).ne')).differentiableAt
  have hloc : LocallyIntegrableOn (deriv (fun x : ℝ => x ^ (-ε))) (Set.Ici 1) := by
    have hc : ContinuousOn (fun t : ℝ => -ε * t ^ (-1 - ε)) (Set.Ici 1) :=
      continuousOn_const.mul
        (continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le one_pos ht).ne')
    exact (hc.congr fun t ht => hderiv t (lt_of_lt_of_le one_pos ht)).locallyIntegrableOn
      measurableSet_Ici
  have hO : (fun t : ℝ => deriv (fun x : ℝ => x ^ (-ε)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k)
      =O[atTop] (fun t : ℝ => t ^ (-1 - ε / 2)) := by
    refine ((abelLogLog_isBigO_rpow_mul_sum_Icc_tmW hε).const_mul_left (-ε)).congr' ?_
      EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hderiv t ht, mul_assoc]
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := tmW) abelLogLog_tmW_zero hdiff hloc
    (abelLogLog_tendsto_rpow_neg_mul_sum_Icc_tmW hε) hO
    (abelLogLog_integrableAtFilter_rpow (by linarith))
  have hI : ∫ t in Set.Ioi 1, deriv (fun x : ℝ => x ^ (-ε)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k
      = -ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hderiv t (lt_trans one_pos ht), mul_assoc]
  rw [hI, zero_sub, neg_mul, neg_neg] at key
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n => div_nonneg (abelLogLog_tmW_nonneg n) (by positivity)), ← tendsto_add_atTop_iff_nat 1]
  refine key.congr fun n => ?_
  rw [Nat.range_succ_eq_Icc_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg k), div_eq_inv_mul]

private lemma abelLogLog_integrableOn_rpow_mul_log_log {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * Real.log (Real.log t)) (Set.Ioi 1) := by
  refine (Real.integrableOn_log_log_mul_rpow (s := 1 + ε) (by linarith)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  rw [show -(1 + ε) = -1 - ε by ring, mul_comm]

private lemma abelLogLog_mul_integral_rpow_mul_log_log {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * Real.log (Real.log t) =
      -Real.eulerMascheroniConstant - Real.log ε := by
  have h := Real.eulerMascheroniConstant_eq_neg_integral_log_log (s := 1 + ε) (by linarith)
  have e : ∫ t in Set.Ioi 1, Real.log (Real.log t) * t ^ (-(1 + ε)) =
      ∫ t in Set.Ioi 1, t ^ (-1 - ε) * Real.log (Real.log t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show -(1 + ε) = -1 - ε by ring, mul_comm]
  rw [e, add_sub_cancel_left] at h
  linarith

private lemma abelLogLog_integrableOn_rpow_mul_D {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - ε) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t))) (Set.Ioi 1) := by
  refine ((abelLogLog_integrableOn_rpow_mul_sum_Icc_tmW hε).sub
    ((abelLogLog_integrableOn_rpow_mul_log_log hε).const_mul (1 / 2))).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  ring

private lemma abelLogLog_mul_integral_rpow_mul_D {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t)) =
      1 / 2 * Real.log ε + ∑' n : ℕ, tmW n / (n : ℝ) ^ ε +
        Real.eulerMascheroniConstant / 2 := by
  have h1 := (abelLogLog_hasSum_tmW_div_rpow hε).tsum_eq
  have h2 := abelLogLog_mul_integral_rpow_mul_log_log hε
  have hsplit : ∫ t in Set.Ioi 1, t ^ (-1 - ε) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t)) =
      (∫ t in Set.Ioi 1, t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) -
        1 / 2 * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * Real.log (Real.log t) := by
    rw [← integral_const_mul, ← integral_sub (abelLogLog_integrableOn_rpow_mul_sum_Icc_tmW hε)
      ((abelLogLog_integrableOn_rpow_mul_log_log hε).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hsplit]
  linear_combination -h1 - (1 / 2 : ℝ) * h2

/-- One-sided Abelian bound: an eventual lower bound `m ≤ f t` passes to the limit `L` of the
means `ε ∫_{t > 1} t ^ (-1 - ε) f t` as `ε → 0+`. -/
private lemma abelLogLog_le_of_tendsto_mean {f : ℝ → ℝ} {m L : ℝ}
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * f t) (Set.Ioi 1))
    (hlim : Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * f t) (𝓝[>] 0) (𝓝 L))
    (hm : ∀ᶠ t in atTop, m ≤ f t) : m ≤ L := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hm
  set T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  set K := T * ∫ t in Set.Ioc 1 T, |t ^ (-1 - 1 : ℝ) * f t|
  have hbound : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      -(ε * K) + m * T ^ (-ε) ≤ ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * f t := by
    rintro ε ⟨hε0, hε1⟩
    have hI := hint ε hε0
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hI.mono_set Set.Ioc_subset_Ioi_self)
      (hI.mono_set (Set.Ioi_subset_Ioi hT1)), mul_add]
    have hA : -(ε * K) ≤ ε * ∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t := by
      have habs : |∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t| ≤ K := by
        calc |∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t|
            ≤ ∫ t in Set.Ioc 1 T, |t ^ (-1 - ε) * f t| := abs_integral_le_integral_abs
          _ ≤ ∫ t in Set.Ioc 1 T, T * |t ^ (-1 - 1 : ℝ) * f t| := by
              refine setIntegral_mono_on (hI.mono_set Set.Ioc_subset_Ioi_self).abs
                (((hint 1 one_pos).mono_set Set.Ioc_subset_Ioi_self).abs.const_mul T)
                measurableSet_Ioc fun t ht => ?_
              obtain ⟨ht1, htT⟩ := ht
              have ht0 : 0 < t := by linarith
              have e : t ^ (-1 - ε) = t ^ (1 - ε) * t ^ (-1 - 1 : ℝ) := by
                rw [← Real.rpow_add ht0]
                congr 1
                ring
              rw [e, mul_assoc, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              calc t ^ (1 - ε) ≤ t ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
                _ = t := Real.rpow_one t
                _ ≤ T := htT
          _ = K := integral_const_mul _ _
      have := neg_abs_le (∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t)
      nlinarith
    have hB : m * T ^ (-ε) ≤ ε * ∫ t in Set.Ioi T, t ^ (-1 - ε) * f t := by
      have h1 : ∫ t in Set.Ioi T, t ^ (-1 - ε) * m ≤ ∫ t in Set.Ioi T, t ^ (-1 - ε) * f t := by
        refine setIntegral_mono_on ((integrableOn_Ioi_rpow_of_lt (by linarith) hT0).mul_const m)
          (hI.mono_set (Set.Ioi_subset_Ioi hT1)) measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := lt_trans hT0 ht
        exact mul_le_mul_of_nonneg_left (hT₀ t (le_trans (le_max_left _ _) ht.le))
          (Real.rpow_pos_of_pos ht0 _).le
      have h2 : ∫ t in Set.Ioi T, t ^ (-1 - ε) * m = T ^ (-ε) / ε * m := by
        rw [integral_mul_const, integral_Ioi_rpow_of_lt (by linarith) hT0,
          show -1 - ε + 1 = -ε by ring, neg_div_neg_eq]
      calc m * T ^ (-ε) = ε * (T ^ (-ε) / ε * m) := by field_simp
        _ ≤ ε * ∫ t in Set.Ioi T, t ^ (-1 - ε) * f t := by
            rw [← h2]
            exact mul_le_mul_of_nonneg_left h1 hε0.le
    linarith
  have hlow : Tendsto (fun ε : ℝ => -(ε * K) + m * T ^ (-ε)) (𝓝[>] 0) (𝓝 m) := by
    have hc : Continuous (fun ε : ℝ => -(ε * K) + m * T ^ (-ε)) :=
      (continuous_id.mul continuous_const).neg.add
        (continuous_const.mul (continuous_const.rpow continuous_neg fun _ => Or.inl hT0.ne'))
    have := hc.tendsto 0
    simp only [zero_mul, neg_zero, Real.rpow_zero, mul_one, zero_add] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine le_of_tendsto_of_tendsto hlow hlim ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
  exact hbound ε hε

private lemma abelLogLog_tendsto_mean_le {f : ℝ → ℝ} {m L : ℝ}
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * f t) (Set.Ioi 1))
    (hlim : Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * f t) (𝓝[>] 0) (𝓝 L))
    (hm : ∀ᶠ t in atTop, f t ≤ m) : L ≤ m := by
  have := abelLogLog_le_of_tendsto_mean (f := fun t => -f t) (m := -m) (L := -L)
    (fun ε hε => by simpa only [mul_neg, Pi.neg_def] using (hint ε hε).neg)
    (by simpa only [mul_neg, integral_neg] using hlim.neg)
    (hm.mono fun t ht => neg_le_neg ht)
  linarith

end Helpers

/-- The log-log Abelian theorem pins down `C`: if `(1/2) log ε + ∑ tmW n / n ^ ε → log κ` as
`ε → 0⁺`, then `C = 2 e^{-γ/2} / κ`. -/
private theorem partIII {C κ : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (𝓝 C))
    (hκ : 0 < κ)
    (hL : Tendsto (fun ε : ℝ => 1 / 2 * Real.log ε + ∑' n : ℕ, tmW n / (n : ℝ) ^ ε)
      (𝓝[>] 0) (𝓝 (Real.log κ))) :
    C = 2 * Real.exp (-Real.eulerMascheroniConstant / 2) / κ := by
  set L := Real.log κ + Real.eulerMascheroniConstant / 2 with hLdef
  set D : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t)
  have hint : ∀ ε : ℝ, 0 < ε → MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * D t)
      (Set.Ioi 1) := fun ε hε => abelLogLog_integrableOn_rpow_mul_D hε
  have hlim : Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * D t) (𝓝[>] 0)
      (𝓝 L) := by
    refine (hL.add_const (Real.eulerMascheroniConstant / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (abelLogLog_mul_integral_rpow_mul_D hε).symm
  have hG : Tendsto (fun t => 2 * Real.exp (-D t)) atTop (𝓝 C) :=
    abelLogLog_tendsto_two_mul_exp_neg hC
  have key : C = 2 * Real.exp (-L) := by
    apply le_antisymm
    · refine not_lt.mp fun h => ?_
      obtain ⟨c, hc1, hc2⟩ := exists_between h
      have hcpos : 0 < c := lt_trans (by positivity) hc1
      have hev : ∀ᶠ t in atTop, D t ≤ -Real.log (c / 2) := by
        filter_upwards [hG.eventually (lt_mem_nhds hc2)] with t ht
        have h1 : c / 2 < Real.exp (-D t) := by linarith
        have h2 := (Real.log_lt_iff_lt_exp (by positivity)).mpr h1
        linarith
      have hLm := abelLogLog_tendsto_mean_le hint hlim hev
      have : c / 2 ≤ Real.exp (-L) := (Real.log_le_iff_le_exp (by positivity)).mp (by linarith)
      linarith
    · refine not_lt.mp fun h => ?_
      obtain ⟨c, hc1, hc2⟩ :=
        exists_between (max_lt h (by positivity : (0 : ℝ) < 2 * Real.exp (-L)))
      have hcpos : 0 < c := lt_of_le_of_lt (le_max_right _ _) hc1
      have hCc : C < c := lt_of_le_of_lt (le_max_left _ _) hc1
      have hev : ∀ᶠ t in atTop, -Real.log (c / 2) ≤ D t := by
        filter_upwards [hG.eventually (gt_mem_nhds hCc)] with t ht
        have h1 : Real.exp (-D t) < c / 2 := by linarith
        have h2 := (Real.lt_log_iff_exp_lt (by positivity)).mpr h1
        linarith
      have hLm := abelLogLog_le_of_tendsto_mean hint hlim hev
      have : Real.exp (-L) ≤ c / 2 := by
        rw [← Real.exp_log (by positivity : 0 < c / 2)]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
  rw [key, hLdef, neg_add, Real.exp_add, Real.exp_neg (Real.log κ), Real.exp_log hκ, neg_div]
  field_simp

end LogLog

/-! ### Assembly -/

section Assembly

open Filter Topology Asymptotics

/-- The Dirichlet series of `tmG` at a real `s > 1` is summable. -/
private lemma summable_tmG {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => tmG n / (n : ℝ) ^ s) := by
  refine (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact div_nonneg (tmG_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  · exact div_le_div_of_nonneg_right (tmG_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

/-- The Dirichlet series of `tmG` at a real `s > 1` is at least `1`. -/
private lemma one_le_tsum_tmG {s : ℝ} (hs : 1 < s) : 1 ≤ ∑' n : ℕ, tmG n / (n : ℝ) ^ s := by
  have h := (summable_tmG hs).le_tsum 1 (fun n _ =>
    div_nonneg (tmG_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
  simpa [tmG_one] using h

/-- `ε ζ(1 + ε) → 1` as `ε → 0⁺`. -/
private lemma tendsto_mul_zeta_one_add :
    Tendsto (fun ε : ℝ => ε * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝[>] 1) := by
    have hc : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_id (x := 𝓝 (0 : ℝ)))
      simpa using this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε ⊢
    linarith
  have h := tendsto_sub_mul_tsum_nat_rpow.comp hmap
  refine h.congr fun ε => ?_
  change (1 + ε - 1) * _ = _
  rw [add_sub_cancel_left]

/-- The rescaled Dirichlet series of `tmG`. -/
private lemma tendsto_sqrt_mul_tsum_tmG {α : ℝ}
    (hA : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ)) / √(Real.log x))
      atTop (𝓝 α)) :
    Tendsto (fun ε : ℝ => √ε * ∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) (𝓝[>] 0)
      (𝓝 (α * (√Real.pi / 2))) := by
  have h := abel_sqrt_log (c := fun n => tmG n / (n : ℝ))
    (fun n => div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n)) hA
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Set.mem_Ioi] at hε
  have hterm : ∀ n : ℕ, tmG n / (n : ℝ) / (n : ℝ) ^ ε = tmG n / (n : ℝ) ^ (1 + ε) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, div_zero, zero_div, Real.zero_rpow (by linarith), div_zero]
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [Real.rpow_add hnpos, Real.rpow_one, div_div]
  change √ε * ∑' n : ℕ, tmG n / (n : ℝ) / (n : ℝ) ^ ε = _
  rw [tsum_congr hterm]

/-- The asymptotic formula, assembled from the four parts above; the public theorem
`MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four` restates it. -/
private theorem main {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    IsEquivalent atTop
      (fun x : ℕ => (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ))
      (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x /
        √(Real.log x)) := by
  obtain ⟨α, hα, hA, hN⟩ := partI
  have hG := tendsto_sqrt_mul_tsum_tmG hA
  have hpi : 0 < √Real.pi / 2 := by positivity
  have hαpi : 0 < α * (√Real.pi / 2) := mul_pos hα hpi
  set κ := 1 / (α * (√Real.pi / 2)) with hκdef
  have hκ : 0 < κ := by positivity
  -- `√ε · F_h(1 + ε) → κ`.
  have hH : Tendsto (fun ε : ℝ => √ε * ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε)) (𝓝[>] 0)
      (𝓝 κ) := by
    have hq := tendsto_mul_zeta_one_add.div hG hαpi.ne'
    rw [hκdef]
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have hs : 1 < 1 + ε := by linarith
    have hF := tsum_tmG_mul_tsum_tmH hs
    have hG1 := one_le_tsum_tmG hs
    have hsq : 0 < √ε := Real.sqrt_pos.mpr hε
    simp only [Pi.div_apply]
    rw [← hF]
    have hG0 : (∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) ≠ 0 := by linarith
    rw [div_eq_iff (mul_ne_zero hsq.ne' hG0)]
    calc ε * ((∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) * ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε))
        = (√ε * √ε) * ((∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) *
            ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε)) := by rw [Real.mul_self_sqrt hε.le]
      _ = _ := by ring
  -- Logarithms.
  have hlog : Tendsto (fun ε : ℝ => 1 / 2 * Real.log ε +
      ∑' n : ℕ, (if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) else 0))
      (𝓝[>] 0) (𝓝 (Real.log κ)) := by
    have h1 := hH.log hκ.ne'
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have hs : 1 < 1 + ε := by linarith
    have hpos : 0 < ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε) := by
      have hF := tsum_tmG_mul_tsum_tmH hs
      have hG1 := one_le_tsum_tmG hs
      have hz : 1 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε) := by
        have h := (Real.summable_one_div_nat_rpow.mpr hs).le_tsum 1 (fun n _ => by positivity)
        simpa using h
      by_contra hneg
      have hneg' : ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε) ≤ 0 := not_lt.mp hneg
      nlinarith
    rw [Real.log_mul (Real.sqrt_pos.mpr hε).ne' hpos.ne', (hasSum_log_tsum_tmH hs).tsum_eq,
      Real.log_sqrt hε.le]
    ring
  have hL : Tendsto (fun ε : ℝ => 1 / 2 * Real.log ε + ∑' n : ℕ, tmW n / (n : ℝ) ^ ε)
      (𝓝[>] 0) (𝓝 (Real.log κ)) := by
    have h := hlog.sub tendsto_tsum_log_sub_tsum_tmW
    rw [sub_zero] at h
    refine h.congr fun ε => ?_
    ring
  have hCeq := partIII hC hκ hL
  -- The constant.
  have hK : √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 = α / 2 := by
    have hsqrt : √(Real.exp Real.eulerMascheroniConstant / Real.pi) =
        Real.exp (Real.eulerMascheroniConstant / 2) / √Real.pi := by
      rw [Real.sqrt_div' _ Real.pi_pos.le, ← Real.exp_half]
    have hpi0 : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have he : Real.exp (-Real.eulerMascheroniConstant / 2) =
        (Real.exp (Real.eulerMascheroniConstant / 2))⁻¹ := by
      rw [neg_div, Real.exp_neg]
    have hE0 : Real.exp (Real.eulerMascheroniConstant / 2) ≠ 0 := (Real.exp_pos _).ne'
    rw [hCeq, hκdef, hsqrt, he]
    field_simp
  -- The count as a sum of `tmG`.
  have hcard : ∀ x : ℕ,
      ((((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℕ) : ℝ) =
        ∑ n ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊, tmG n := by
    intro x
    rw [Nat.floor_natCast, Finset.card_filter, Nat.cast_sum,
      show Finset.Icc 1 x = Finset.Ioc 0 x from rfl]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    unfold tmG
    by_cases h : ∀ q ∈ n.primeFactors, q % 4 = 3
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), ite_eq_left_iff.mpr
        (fun h' => absurd ⟨hn0, h⟩ h'), Nat.cast_one]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), ite_eq_right_iff.mpr
        (fun h' => absurd h'.2 h), Nat.cast_zero]
  have hNnat : Tendsto (fun x : ℕ => (∑ n ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊, tmG n) *
      √(Real.log x) / x) atTop (𝓝 (α / 2)) := hN.comp tendsto_natCast_atTop_atTop
  have hα2 : α / 2 ≠ 0 := by positivity
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun x : ℕ => ((∑ n ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊, tmG n) *
      √(Real.log x) / x) / (α / 2)) atTop (𝓝 1) := by
    simpa [div_self hα2] using hNnat.div_const (α / 2)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : 0 < √(Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx1)
  simp only [Pi.div_apply]
  rw [hcard x, ← hK]
  have hK0 : √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 ≠ 0 := by rw [hK]; exact hα2
  field_simp

end Assembly

end isEquivalent_card_primeFactors_three_mod_four

@[expose] public section

open Filter Asymptotics

/-- **Counting integers whose prime factors are all $\equiv 3 \pmod 4$.** Let $C$ be a real
number such that $\sqrt{\ln x} \prod_{q \le x} (1 - 1/q) \to C$ as the natural number $x$ tends
to infinity, where $q$ runs over the primes with $q \equiv 1 \pmod 4$. Let $g(x)$ be the number
of integers $n$ with $1 \le n \le x$ all of whose prime factors are $\equiv 3 \pmod 4$ (so
$n = 1$ is counted). Then
$$g(x) \sim \sqrt{e^\gamma / \pi} \cdot \frac{C}{2} \cdot \frac{x}{\sqrt{\ln x}}$$
as the natural number $x$ tends to infinity, where $\gamma$ is the Euler–Mascheroni constant.

In the source $C = C(4, 1)$ is the constant of Languasco and Zaccagnini; for $C = 1.29230\ldots$
the constant in front of $x / \sqrt{\ln x}$ is $0.48651\ldots$.

Source: Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann
Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 2 (`integers-2025-A75-thm-2`). -/
public theorem isEquivalent_card_primeFactors_three_mod_four {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    IsEquivalent atTop
      (fun x : ℕ => (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ))
      (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x /
        √(Real.log x)) :=
  _root_.MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four.main hC

end

end MetaMathlibExt
