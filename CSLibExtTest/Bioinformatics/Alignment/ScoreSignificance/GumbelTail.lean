/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.GumbelTail
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Gumbel tail tests

* `maxSegmentScore` on the scores `1, -2, 3` (best segment `[2, 3)`, score `3`), nonnegativity
  and monotonicity.
* A nontrivial `LadderInput`: i.i.d. `Exp(1)` excursion heights on the product space, one
  excursion per step (`A = 1`), `Mₙ` the running maximum. The nonlattice theorem specializes
  to the classical Gumbel law `P(max_{i ≤ n} Yᵢ ≤ log n + x) → exp (-e^{-x})` (`C = K = 1`).
* The exponential example: `E e^{Y} = 2` for `Y ~ Exp(2)`, and the Cramér root `θ = 1` of
  `X = E₁ - E₂`, `E₁ ~ Exp(2)`, `E₂ ~ Exp(1)` independent.
* The score-level and lattice theorems applied to arbitrary renewal inputs.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### Maximal segment score -/

/-- The scores `1, -2, 3, 0, 0, …`. -/
noncomputable def x₀ : ℕ → ℝ := fun k => if k = 0 then 1 else if k = 1 then -2 else if k = 2
  then 3 else 0

example : maxSegmentScore x₀ 3 = 3 := by
  refine le_antisymm (Finset.sup'_le _ _ fun p hp => ?_) ?_
  · obtain ⟨i, j⟩ := p
    simp only [Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨hi, hj⟩ := hp
    interval_cases i <;> interval_cases j <;>
      simp [segmentScore, x₀, Finset.sum_Ico_eq_sum_range] <;> norm_num [Finset.sum_range_succ]
  · have := segmentScore_le_maxSegmentScore (x := x₀) (n := 3) (i := 2) (j := 3) (by norm_num)
      le_rfl
    simpa [segmentScore, x₀] using this

example (x : ℕ → ℝ) : 0 ≤ maxSegmentScore x 5 := zero_le_maxSegmentScore x 5

example (x : ℕ → ℝ) : maxSegmentScore x 2 ≤ maxSegmentScore x 7 :=
  maxSegmentScore_mono x (by norm_num)

/-! ### A nontrivial ladder input: i.i.d. exponential excursion heights -/

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- I.i.d. `Exp(1)` coordinates. -/
noncomputable abbrev Pexp : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => expMeasure 1

/-- The running maximum `max_{i ≤ n} ω i`. -/
noncomputable def runMax (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ ω

/-- One `Exp(1)` excursion per step: `Y i ω = ω i`, `N n = n`, `A = 1`, `F = cdf Exp(1)`. -/
noncomputable def expLadder : LadderInput Pexp runMax where
  Y i ω := ω i
  N n _ := n
  F t := cdf (expMeasure 1) t
  A := 1
  A_pos := one_pos
  measurable_Y i := measurable_pi_apply i
  iIndepFun_Y := iIndepFun_infinitePi (X := fun _ => (id : ℝ → ℝ)) fun _ => measurable_id
  real_Y_le i t := by
    rw [cdf_eq_real, ← Measure.infinitePi_map_eval (fun _ => expMeasure 1) i,
      map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic]
    rfl
  count_lln ε hε := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hset : {ω : ℕ → ℝ | ε ≤ |(n : ℝ) / n - (1 : ℝ)⁻¹|} = ∅ := by
      ext ω; simp [div_self hn', not_le.2 hε]
    rw [hset, measureReal_empty]
  le_of_forall_le := ae_of_all _ fun ω n t h =>
    Finset.sup'_le _ _ fun i hi => h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  le_of_lt_count := ae_of_all _ fun ω n i hi =>
    Finset.le_sup' ω (Finset.mem_range.2 (by omega))

theorem expLadder_tail :
    Tendsto (fun t => (1 - expLadder.F t) * Real.exp (1 * t)) atTop (𝓝 1) :=
  tendsto_tail_of_eq_exp fun t ht => by
    change 1 - cdf (expMeasure 1) t = _
    rw [cdf_expMeasure_eq one_pos]; simp [ht]

/-- The classical Gumbel law for maxima of i.i.d. `Exp(1)` variables, as an instance of the
nonlattice theorem with `θ = 1`, `C = 1`, `A = 1`. -/
example (x : ℝ) :
    Tendsto (fun n : ℕ => Pexp.real {ω | runMax n ω ≤ Real.log n + x}) atTop
      (𝓝 (Real.exp (-Real.exp (-x)))) := by
  simpa [expLadder] using expLadder.tendsto_real_le_log_div_add one_pos expLadder_tail x

/-- The same instance through the general two-sided bound along a subsequence filter. -/
example (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Pexp.real {ω | runMax n ω ≤ Real.log n / 1 + x} ≤
      Real.exp (-(1 / expLadder.A * Real.exp (-(1 * x)))) + ε :=
  ((expLadder.tendsto_real_le_log_div_add one_pos expLadder_tail x).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ hε))).mono fun _ h => h.le

/-! ### A lattice ladder input: floors of exponential variables -/

/-- The floor `⌊r⌋` as a real number. -/
noncomputable def fl (r : ℝ) : ℝ := (⌊r⌋ : ℝ)

theorem measurable_fl : Measurable fl :=
  (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp Int.measurable_floor

/-- The running maximum `max_{i ≤ n} ⌊ω i⌋`. -/
noncomputable def runMaxFl (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ fun i => fl (ω i)

/-- Lattice excursion heights `Y i = ⌊Eᵢ⌋` (span `1`), one per step. -/
noncomputable def flLadder : LadderInput Pexp runMaxFl where
  Y i ω := fl (ω i)
  N n _ := n
  F t := (expMeasure 1).real {r | fl r ≤ t}
  A := 1
  A_pos := one_pos
  measurable_Y i := measurable_fl.comp (measurable_pi_apply i)
  iIndepFun_Y := iIndepFun_infinitePi (X := fun _ => fl) fun _ => measurable_fl
  real_Y_le i t := by
    rw [← Measure.infinitePi_map_eval (fun _ => expMeasure 1) i,
      map_measureReal_apply (measurable_pi_apply i) (measurableSet_le measurable_fl
        measurable_const)]
    rfl
  count_lln ε hε := expLadder.count_lln ε hε
  le_of_forall_le := ae_of_all _ fun ω n t h =>
    Finset.sup'_le _ _ fun i hi => h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  le_of_lt_count := ae_of_all _ fun ω n i hi =>
    Finset.le_sup' (fun i => fl (ω i)) (Finset.mem_range.2 (by omega))

theorem flLadder_lattice : ∀ i, ∀ᵐ ω ∂Pexp, ∃ k : ℤ, flLadder.Y i ω = k * 1 :=
  fun i => ae_of_all _ fun ω => ⟨⌊ω i⌋, by simp [flLadder, fl]⟩

/-- `P(⌊E⌋ > k) = P(E ≥ k + 1) = e^{-(k + 1)}`: the lattice tail with `θ = 1`, `h = 1`,
`C = 1`. -/
theorem flLadder_tail :
    Tendsto (fun k : ℕ => (1 - flLadder.F (k * 1)) * Real.exp (1 * ((k + 1) * 1))) atTop
      (𝓝 1) := by
  refine tendsto_const_nhds.congr fun k => ?_
  have hset : {r : ℝ | fl r ≤ (k : ℝ) * 1} = Set.Iio ((k : ℝ) + 1) := by
    ext r
    simp only [fl, mul_one, Set.mem_Iio]
    rw [show ((k : ℝ)) = ((k : ℤ) : ℝ) by simp, Set.mem_ofPred_eq, Int.cast_le, Int.floor_le_iff]
  have hatom : expMeasure 1 {(k : ℝ) + 1} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  change 1 = (1 - (expMeasure 1).real {r | fl r ≤ (k : ℝ) * 1}) * _
  rw [hset, measureReal_def, measure_congr (Iio_ae_eq_Iic' hatom), ← measureReal_def,
    ← cdf_eq_real, cdf_expMeasure_eq one_pos]
  have hk0 : (0 : ℝ) ≤ k + 1 := by positivity
  simp only [hk0, ↓reduceIte]
  rw [sub_sub_cancel, ← Real.exp_add]
  simp

/-- **Lattice scores have no Gumbel limit**: `P(max_{i ≤ n} ⌊Eᵢ⌋ ≤ log n + x)` does not
converge (here `K = 1`, and the liminf `exp (-e^{-x})` and limsup `exp (-e^{-(x + 1)})`
differ). -/
example (x l : ℝ) :
    ¬ Tendsto (fun n : ℕ => Pexp.real {ω | runMaxFl n ω ≤ Real.log n / 1 + x}) atTop (𝓝 l) :=
  flLadder.not_tendsto_lattice one_pos one_pos one_pos flLadder_lattice flLadder_tail x l

example (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(1 / 1 * Real.exp (-(1 * x)))) - ε ≤
        Pexp.real {ω | runMaxFl n ω ≤ Real.log n / 1 + x} ∧
      Pexp.real {ω | runMaxFl n ω ≤ Real.log n / 1 + x} ≤
        Real.exp (-(1 / 1 * Real.exp (-(1 * (x + 1))))) + ε :=
  flLadder.eventually_lattice_bounds one_pos one_pos flLadder_lattice flLadder_tail x hε

/-! ### Exponential scores: computed constants -/

example : mgf id (expMeasure 2) 1 = 2 := by
  rw [mgf_id_expMeasure (by norm_num) (by norm_num)]; norm_num

instance : IsProbabilityMeasure (expMeasure 2) := isProbabilityMeasure_expMeasure two_pos

/-- `X = E₁ - E₂` with `E₁ ~ Exp(2)`, `E₂ ~ Exp(1)` independent has Cramér root `θ = 2 - 1`. -/
example : mgf (fun ω : ℝ × ℝ => ω.1 - ω.2) ((expMeasure 2).prod (expMeasure 1)) 1 = 1 := by
  have h := mgf_sub_eq_one (P := (expMeasure 2).prod (expMeasure 1)) (E₁ := Prod.fst)
    (E₂ := Prod.snd) (a := 2) (b := 1) one_pos one_lt_two measurable_fst measurable_snd
    (by simp) (by simp) (indepFun_prod measurable_id measurable_id)
  norm_num at h
  exact h

example : Tendsto (fun t => (1 - (1 - 3 * Real.exp (-(2 * t)))) * Real.exp (2 * t)) atTop
    (𝓝 3) :=
  tendsto_tail_of_eq_exp (F := fun t => 1 - 3 * Real.exp (-(2 * t))) fun _ _ => by ring

/-! ### Score-level and lattice statements -/

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

example (R : NonlatticeRenewalInput P X) (x : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | maxSegmentScore (fun k => X k ω) n ≤
      Real.log n / R.θ + x}) atTop (𝓝 (Real.exp (-(R.C / R.ladder.A * Real.exp (-(R.θ * x)))))) :=
  R.tendsto_gumbel x

example (R : LatticeRenewalInput P X) (hC : 0 < R.C) (x : ℝ) :
    ¬ ∃ l, Tendsto (fun n : ℕ => P.real {ω | maxSegmentScore (fun k => X k ω) n ≤
      Real.log n / R.θ + x}) atTop (𝓝 l) :=
  fun ⟨l, hl⟩ => R.not_tendsto hC x l hl

example (R : LatticeRenewalInput P X) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(R.K * Real.exp (-(R.θ * x)))) - 1 ≤
        P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} ∧
      P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} ≤
        Real.exp (-(R.K * Real.exp (-(R.θ * (x + R.h))))) + 1 :=
  R.eventually_bounds x one_pos

example (R : LatticeRenewalInput P X) (x : ℝ) :
    ∃ᶠ n : ℕ in atTop, P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / R.θ + x} ≤
      Real.exp (-(R.K * Real.exp (-(R.θ * x)))) + 1 :=
  (R.frequently_bounds x one_pos).1

end

end Cslib.Bioinformatics.Alignment.ScoreSignificance
