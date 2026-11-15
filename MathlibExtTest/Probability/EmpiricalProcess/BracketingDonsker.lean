/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.EmpiricalProcess.BracketingDonsker
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for Donsker conditions under uniform bracketing entropy

* Boundary values of the bracketing number and entropy, computed from the definitions: no cover
  of negative width exists for a nonempty class, every bracket is ordered (so not even the
  empty class has a bracket of negative width), the empty class needs `0` brackets, and a class
  of copies of one function needs one bracket at every width `ε ≥ 0`.
* The empirical process vanishes at `n = 0` and at constant functions.
* Non-vacuity of the entropy hypothesis: the infinite class `{θ • g : θ ∈ [0, 1]}` with `|g| ≤ 1`
  has `⌈1/ε⌉₊ + 1` brackets of width `ε`, so its entropy is at most `√2 ε^{-1/2}` on `(0, 1]` and
  its entropy integral is finite. This is computed from the definitions, not through the
  theorems under test.
* The main theorem applied to that class with an i.i.d. Gaussian sample on `ℕ → ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open MathlibExt.Probability.EmpiricalProcess.BracketingDonsker

namespace BracketingDonskerTest

/-! ### Boundary values of the definitions -/

/-- No bracket has negative width, so a nonempty class has no cover of width `ε < 0`. -/
example {S ι : Type*} [MeasurableSpace S] [Nonempty S] [Nonempty ι] (F : ι → S → ℝ) {ε : ℝ}
    (hε : ε < 0) : uniformBracketingNumber F ε = ⊤ ∧ uniformBracketingEntropy F ε = ⊤ := by
  have h : ∀ n, ¬ IsUniformBracketCover F ε n := by
    rintro n ⟨l, u, -, -, -, hw, hc⟩
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨x⟩ := ‹Nonempty S›
    obtain ⟨j, hj⟩ := hc i
    linarith [hw j x, (hj x).1, (hj x).2]
  exact ⟨uniformBracketingNumber_eq_top_iff.2 h, uniformBracketingEntropy_eq_top_iff.2 h⟩

/-- The empty class is covered by zero brackets at every width. -/
example {S : Type*} [MeasurableSpace S] (F : Empty → S → ℝ) (ε : ℝ) :
    uniformBracketingNumber F ε = 0 ∧ uniformBracketingEntropy F ε = 0 := by
  have h : IsUniformBracketCover F ε 0 :=
    ⟨Fin.elim0, Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0,
      fun i ↦ i.elim⟩
  refine ⟨nonpos_iff_eq_zero.1 ?_, nonpos_iff_eq_zero.1 ?_⟩
  · simpa using uniformBracketingNumber_le h
  · simpa using uniformBracketingEntropy_le h

/-- Infinitely many copies of one measurable function need one bracket at every `ε ≥ 0`, so the
entropy vanishes there. -/
example {S : Type*} [MeasurableSpace S] {g : S → ℝ} (hg : Measurable g) {ε : ℝ} (hε : 0 ≤ ε) :
    uniformBracketingNumber (fun _ : ℕ ↦ g) ε ≤ 1 ∧
      uniformBracketingEntropy (fun _ : ℕ ↦ g) ε = 0 := by
  have h : IsUniformBracketCover (fun _ : ℕ ↦ g) ε 1 :=
    ⟨fun _ ↦ g, fun _ ↦ g, fun _ ↦ hg, fun _ ↦ hg, fun _ _ ↦ le_rfl, fun _ _ ↦ by simpa using hε,
      fun _ ↦ ⟨0, fun _ ↦ ⟨le_rfl, le_rfl⟩⟩⟩
  refine ⟨?_, nonpos_iff_eq_zero.1 ?_⟩
  · simpa using uniformBracketingNumber_le h
  · simpa using uniformBracketingEntropy_le h

/-- Every bracket is ordered, so a cover of negative width has no brackets at all, even for the
empty class (the unordered pair `l = 1`, `u = 0` is not a bracket). -/
example {S : Type*} [MeasurableSpace S] [Nonempty S] (F : Empty → S → ℝ) :
    ¬ IsUniformBracketCover F (-1) 1 := by
  rintro ⟨l, u, -, -, hlu, hw, -⟩
  obtain ⟨x⟩ := ‹Nonempty S›
  linarith [hlu 0 x, hw 0 x]

/-! ### The empirical process at boundary inputs -/

example {S Ω : Type*} [MeasurableSpace S] (μ : Measure S) (X : ℕ → Ω → S) (f : S → ℝ) (ω : Ω) :
    empiricalProcess μ X 0 f ω = 0 := by
  simp [empiricalProcess]

example {S Ω : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → S) (c : ℝ) (n : ℕ) (ω : Ω) :
    empiricalProcess μ X n (fun _ ↦ c) ω = 0 := by
  simp [empiricalProcess]

/-! ### Non-vacuity: a scaled class with finite entropy integral -/

/-- `{θ • g : θ ∈ [0, 1]}` with `|g| ≤ 1` has `⌈1/ε⌉₊ + 1` brackets of width `ε`, centred at
`(j + 1/2) ε g` with `j = ⌊θ / ε⌋₊`. -/
theorem isUniformBracketCover_scale {S : Type*} [MeasurableSpace S] {g : S → ℝ}
    (hg : Measurable g) (hg1 : ∀ x, |g x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    IsUniformBracketCover (fun θ : Set.Icc (0 : ℝ) 1 ↦ fun x ↦ (θ : ℝ) * g x) ε
      (⌈1 / ε⌉₊ + 1) := by
  refine ⟨fun j x ↦ ((j : ℝ) + 1 / 2) * ε * g x - ε / 2,
    fun j x ↦ ((j : ℝ) + 1 / 2) * ε * g x + ε / 2,
    fun j ↦ ((hg.const_mul _).sub_const _), fun j ↦ ((hg.const_mul _).add_const _),
    fun j x ↦ by linarith, fun j x ↦ le_of_eq (by ring), fun θ ↦ ?_⟩
  have hθ0 : 0 ≤ (θ : ℝ) / ε := div_nonneg θ.2.1 hε.le
  have hj : ⌊(θ : ℝ) / ε⌋₊ < ⌈1 / ε⌉₊ + 1 :=
    Nat.lt_succ_of_le ((Nat.floor_le_floor (div_le_div_of_nonneg_right θ.2.2 hε.le)).trans
      (Nat.floor_le_ceil _))
  refine ⟨⟨⌊(θ : ℝ) / ε⌋₊, hj⟩, fun x ↦ ?_⟩
  have h1 : (⌊(θ : ℝ) / ε⌋₊ : ℝ) * ε ≤ θ := (le_div_iff₀ hε).1 (Nat.floor_le hθ0)
  have h2 : (θ : ℝ) < ((⌊(θ : ℝ) / ε⌋₊ : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).1 (Nat.lt_floor_add_one _)
  have hd : |(θ : ℝ) - ((⌊(θ : ℝ) / ε⌋₊ : ℝ) + 1 / 2) * ε| ≤ ε / 2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hx : |(θ : ℝ) * g x - ((⌊(θ : ℝ) / ε⌋₊ : ℝ) + 1 / 2) * ε * g x| ≤ ε / 2 := by
    rw [← sub_mul, abs_mul]
    calc _ ≤ ε / 2 * 1 := mul_le_mul hd (hg1 x) (abs_nonneg _) (by positivity)
      _ = ε / 2 := mul_one _
  constructor <;> linarith [(abs_le.1 hx).1, (abs_le.1 hx).2]

/-- The entropy of the scaled class is at most `√2 ε^{-1/2}` on `(0, 1]`. -/
theorem uniformBracketingEntropy_scale_le {S : Type*} [MeasurableSpace S] {g : S → ℝ}
    (hg : Measurable g) (hg1 : ∀ x, |g x| ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    uniformBracketingEntropy (fun θ : Set.Icc (0 : ℝ) 1 ↦ fun x ↦ (θ : ℝ) * g x) ε ≤
      ENNReal.ofReal (√2 * ε ^ (-(1 / 2) : ℝ)) := by
  refine (uniformBracketingEntropy_le (isUniformBracketCover_scale hg hg1 hε)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hK : (⌈1 / ε⌉₊ : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlog : Real.log ((⌈1 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ 2 / ε := by
    have := Real.log_le_sub_one_of_pos (x := ((⌈1 / ε⌉₊ + 1 : ℕ) : ℝ)) (by positivity)
    push_cast at this ⊢
    have h1e : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    calc _ ≤ (⌈1 / ε⌉₊ : ℝ) := by linarith
      _ ≤ 1 / ε + 1 := hK.le
      _ ≤ 2 / ε := by rw [show 2 / ε = 1 / ε + 1 / ε by ring]; linarith
  have hrhs : √2 * ε ^ (-(1 / 2) : ℝ) = √(2 / ε) := by
    rw [Real.rpow_neg hε.le, ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hε.le, div_eq_mul_inv]
  rw [hrhs]
  exact Real.sqrt_le_sqrt hlog

/-- The entropy hypothesis of the main theorem holds for the infinite scaled class. -/
theorem lintegral_uniformBracketingEntropy_scale_ne_top {S : Type*} [MeasurableSpace S]
    {g : S → ℝ} (hg : Measurable g) (hg1 : ∀ x, |g x| ≤ 1) :
    ∫⁻ ε in Set.Ioc 0 1,
      uniformBracketingEntropy (fun θ : Set.Icc (0 : ℝ) 1 ↦ fun x ↦ (θ : ℝ) * g x) ε ≠ ⊤ := by
  have hint : IntegrableOn (fun ε : ℝ ↦ √2 * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
  refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne (lintegral_mono_ae ?_)
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun ε hε ↦
    uniformBracketingEntropy_scale_le hg hg1 hε.1 hε.2)

/-! ### The main theorem on a concrete i.i.d. sample -/

/-- An i.i.d. standard Gaussian sample, realized as coordinates under the infinite product
measure, and the class `{θ • cos : θ ∈ [0, 1]}`: the Donsker conditions hold. -/
example : DonskerConditions (gaussianReal 0 1) (Measure.infinitePi fun _ : ℕ ↦ gaussianReal 0 1)
    (fun k ω ↦ ω k) (fun θ : Set.Icc (0 : ℝ) 1 ↦ fun x ↦ (θ : ℝ) * Real.cos x) := by
  have hcos : Measurable Real.cos := Real.continuous_cos.measurable
  refine donskerConditions_of_uniformBracketingEntropy
    (fun k ↦ (measurePreserving_eval_infinitePi _ k).hasLaw)
    (iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id)
    (fun θ ↦ hcos.const_mul _) (fun θ ↦ ?_)
    (lintegral_uniformBracketingEntropy_scale_ne_top hcos Real.abs_cos_le_one)
  refine MemLp.of_bound (hcos.const_mul _).aestronglyMeasurable 1 (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg θ.2.1]
  calc (θ : ℝ) * |Real.cos x| ≤ 1 * 1 := mul_le_mul θ.2.2 (Real.abs_cos_le_one x)
        (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end BracketingDonskerTest
