/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.RenewalDerivation
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Renewal derivation tests

* A concrete lattice instance of `LatticeLadderRenewalData` (span `1`, `θ = 1`): `M' = ⌊E⌋` with
  `E ~ Exp(1)`, so `P(M' > k) = e^{-(k + 1)}`, single-step ladder law `g 1 = e^{-1}`, trivial
  excursion `Y = 0`, `D = 0`. The derived lattice tail theorem (no assumed renewal theorem) applies,
  and the Cramér–Lundberg constant evaluates to `C_∞ = e^{-1}`, matching `e^k P(M' > k) = e^{-1}`.
* A nonlattice `LadderRenewalData` with `G = δ₀` (degenerate but admissible), whose constant
  evaluates to `0`.
* The excursion step `tendsto_exp_mul_real_lt_of_fixedPoint` on the same fixed point.
* The derived inputs `NonlatticeRenewalInput.ofLadder`, `LatticeRenewalInput.ofLadder` and their
  limit theorems applied to arbitrary hypotheses.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Renewal MathlibExt.Probability.Renewal.LatticeConstants

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- The floor `⌊r⌋` as a real number. -/
noncomputable def flr (r : ℝ) : ℝ := (⌊r⌋ : ℝ)

theorem measurable_flr : Measurable flr :=
  (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp Int.measurable_floor

theorem ae_pos_expMeasure : ∀ᵐ r ∂(expMeasure 1), 0 < r := by
  have h0 : expMeasure 1 (Set.Iic 0) = 0 := by
    have h := cdf_expMeasure_eq one_pos 0
    rw [cdf_eq_real] at h
    simp only [le_refl, ↓reduceIte, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
    exact (measureReal_eq_zero_iff).1 h
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with r hr
  simpa using hr

theorem ae_flr_nonneg : ∀ᵐ r ∂(expMeasure 1), 0 ≤ flr r := by
  filter_upwards [ae_pos_expMeasure] with r hr
  exact Int.cast_nonneg (Int.floor_nonneg.2 hr.le)

/-- `P(⌊E⌋ > m) = P(E ≥ m + 1) = e^{-(m + 1)}`. -/
theorem real_lt_flr (m : ℕ) :
    (expMeasure 1).real {r | (m : ℝ) * 1 < flr r} = Real.exp (-((m : ℝ) + 1)) := by
  have hset : {r : ℝ | (m : ℝ) * 1 < flr r} = (Set.Iio ((m : ℝ) + 1))ᶜ := by
    ext r
    simp only [flr, mul_one, Set.mem_compl_iff, Set.mem_Iio, not_lt]
    rw [show ((m : ℝ)) = ((m : ℤ) : ℝ) by simp, Set.mem_ofPred_eq, Int.cast_lt,
      ← Int.add_one_le_iff, Int.le_floor]
    push_cast; rfl
  have hatom : expMeasure 1 {(m : ℝ) + 1} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  rw [hset, measureReal_compl measurableSet_Iio, probReal_univ, measureReal_def,
    measure_congr (Iio_ae_eq_Iic' hatom), ← measureReal_def, ← cdf_eq_real,
    cdf_expMeasure_eq one_pos]
  have hm0 : (0 : ℝ) ≤ m + 1 := by positivity
  simp only [hm0, ↓reduceIte, one_mul]
  ring

/-- The fixed point with trivial first excursion: `Y = 0`, `D = 0`, `M' = ⌊E⌋`. -/
noncomputable def flFixedPoint : LadderFixedPoint (expMeasure 1) (fun _ => 0) where
  D _ := 0
  M' := flr
  measurable_D := measurable_const
  measurable_M' := measurable_flr
  D_nonpos := ae_of_all _ fun _ => le_rfl
  M'_nonneg := ae_flr_nonneg
  indep := indepFun_const_left _ _
  fixedPoint t := by
    refine measureReal_congr ?_
    filter_upwards [ae_flr_nonneg] with r hr
    rw [zero_add, max_eq_right hr]

/-- The single-step ladder law `g 1 = e^{-1}`. -/
noncomputable def gStep (j : ℕ) : ℝ := if j = 1 then Real.exp (-1) else 0

theorem gStep_mul_exp (j : ℕ) :
    gStep j * Real.exp (1 * 1 * j) = if j = 1 then 1 else 0 := by
  unfold gStep
  split_ifs with h
  · subst h; rw [← Real.exp_add]; norm_num
  · simp

/-- **A concrete lattice instance** (`θ = h = 1`): `P(M' > k) = e^{-(k + 1)}` solves the
defective renewal equation of the single-step ladder law `g 1 = e^{-1}`. -/
noncomputable def flData : LatticeLadderRenewalData (expMeasure 1) (fun _ => 0) 1 1 where
  toLadderFixedPoint := flFixedPoint
  D_lattice := ae_of_all _ fun _ => ⟨0, by simp [flFixedPoint]⟩
  g := gStep
  g_zero := by simp [gStep]
  g_nonneg j := by unfold gStep; split_ifs <;> positivity
  cramer_ladder := by
    simp_rw [gStep_mul_exp]; exact hasSum_ite_eq 1 1
  aperiodic := by
    have hset : {j : ℕ | 0 < gStep j} = {1} := by
      ext j; simp only [gStep, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      split_ifs with h <;> simp [h, Real.exp_pos]
    rw [hset]; exact Nat.dvd_one.1 (Nat.setGcd_dvd_of_mem rfl)
  tiltedMean := 1
  hasSum_tiltedMean := by
    simp_rw [gStep_mul_exp]
    convert hasSum_ite_eq 1 (1 : ℝ) using 1
    ext j; split_ifs with h <;> simp [h]
  renewal n := by
    change (expMeasure 1).real {r | (n : ℝ) * 1 < flr r} = ladderTail gStep n +
      ∑ k ∈ Finset.range (n + 1), gStep k * (expMeasure 1).real {r | ((n - k : ℕ) : ℝ) * 1 < flr r}
    simp_rw [real_lt_flr]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have ht : ladderTail gStep 0 = Real.exp (-1) := by
        rw [ladderTail, tsum_eq_single 0 fun j hj => by simp [gStep, hj]]
        simp [gStep]
      simp [ht, gStep]
    · have ht : ladderTail gStep n = 0 := by
        have h0 : (fun j => gStep (j + n + 1)) = fun _ => 0 :=
          funext fun j => by simp only [gStep]; rw [ite_eq_right (by omega)]
        rw [ladderTail, h0, tsum_zero]
      rw [ht, zero_add, Finset.sum_eq_single 1 (fun k _ hk => by simp [gStep, hk])
        (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
      simp only [gStep, ↓reduceIte]
      rw [← Real.exp_add, Nat.cast_sub hn]
      ring_nf

/-- The lattice Cramér–Lundberg constant of the instance: `C_∞ = e^{-1}`, matching
`e^k P(M' > k) = e^{-1}`. -/
example : flData.allTimeConst = Real.exp (-1) := by
  have hs : ∑' j, gStep j = Real.exp (-1) := by
    rw [tsum_eq_single 1 fun j hj => by simp [gStep, hj]]; simp [gStep]
  change (1 - ∑' j, gStep j) / ((Real.exp (1 * 1) - 1) * 1) = _
  rw [hs, mul_one, mul_one]
  have he : Real.exp 1 - 1 ≠ 0 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  field_simp
  rw [mul_sub, mul_one, ← Real.exp_add]; norm_num

/-- The derived lattice tail on the instance (no renewal theorem assumed). The excursion is
trivial, so the excursion constant is `C = e (e^{-1}) (1 - E e^{0}) = 0`. -/
example : Tendsto (fun k : ℕ => (expMeasure 1).real {_r : ℝ | (k : ℝ) * 1 < (0 : ℝ)} *
    Real.exp (1 * ((k + 1) * 1))) atTop (𝓝 flData.tailConst) :=
  flData.tendsto_tail measurable_const one_pos one_pos

example : flData.tailConst = 0 := by
  simp [LatticeLadderRenewalData.tailConst, flData, flFixedPoint]

/-- The excursion step directly on the fixed point `flFixedPoint`, along the lattice points
`s k = k`: `e^k P(M' > k) = e^{-1}` and `e^u P(M' > u) ≤ 1` give the excursion-tail limit
`e^{-1} (1 - E e^{0})` for `Y = 0`. -/
example : Tendsto (fun k : ℕ => Real.exp (1 * ((k : ℝ) * 1)) *
    (expMeasure 1).real {_r : ℝ | (k : ℝ) * 1 < (0 : ℝ)}) atTop
      (𝓝 (Real.exp (-1) * (1 - ∫ _, Real.exp (1 * (0 : ℝ)) ∂(expMeasure 1)))) := by
  have hC : Tendsto (fun k : ℕ => Real.exp (1 * ((k : ℝ) * 1)) *
      (expMeasure 1).real {r | (k : ℝ) * 1 < flr r}) atTop (𝓝 (Real.exp (-1))) := by
    refine tendsto_const_nhds.congr fun k => ?_
    rw [real_lt_flr, ← Real.exp_add]; ring_nf
  refine tendsto_exp_mul_real_lt_of_fixedPoint (Y := fun _ => (0 : ℝ)) (D := fun _ => 0)
    (M' := flr) one_pos measurable_const measurable_const measurable_flr
    (ae_of_all _ fun _ => le_rfl) (indepFun_const_left _ _) flFixedPoint.fixedPoint
    (tendsto_natCast_atTop_atTop.atTop_mul_const one_pos) (B := 1) (fun u hu => ?_) hC
    (ae_of_all _ fun _ => by simpa using hC)
  -- `e^u P(⌊E⌋ > u) ≤ e^u P(E > u) = 1`
  have hsub : {r | u < flr r} ⊆ {r | u < r} := fun r (h : u < flr r) =>
    lt_of_lt_of_le h (Int.floor_le r)
  have hcdf : (expMeasure 1).real {r | u < r} = Real.exp (-u) := by
    rw [show {r : ℝ | u < r} = (Set.Iic u)ᶜ by ext; simp, measureReal_compl measurableSet_Iic,
      probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq one_pos]
    simp [hu]
  calc Real.exp (1 * u) * (expMeasure 1).real {r | u < flr r}
      ≤ Real.exp (1 * u) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_left (hcdf ▸ measureReal_mono hsub) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- A nonlattice `LadderRenewalData` with ladder law `δ₀` (degenerate: the tilted law is `δ₀`,
for which the key renewal theorem fails, so `tendsto_tail` cannot be applied to it). -/
noncomputable def diracData : LadderRenewalData (expMeasure 1) (fun _ => 0) 1 where
  toLadderFixedPoint := flFixedPoint
  G := Measure.dirac 0
  isFiniteMeasure_G := inferInstance
  G_nonneg := by simp
  cramer_ladder := by simp
  integrable_mean := integrable_dirac (by simp)
  renewal t _ := by simp

example : diracData.allTimeConst = 0 := by
  simp [LadderRenewalData.allTimeConst, diracData]

/-! ### Derived inputs on arbitrary data -/

section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {θ h : ℝ}

example (L : LadderInput P (maxSegmentScoreRV X)) (t : ℝ) :
    P.real {ω | t < L.Y 0 ω} = 1 - L.F t :=
  L.real_Y_lt_eq_one_sub t

example (hX : CramerScores P X θ) (hnl : ∀ h > 0, ¬ ∀ᵐ ω ∂P, ∃ k : ℤ, X 0 ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (R : LadderRenewalData P (L.Y 0) θ)
    (hKRT : ∀ V v : ℝ → ℝ, KeyRenewalAdmissible V v →
      (∀ t, V t = v t + ∫ x, V (t - x) ∂(R.G.tilted (fun x => θ * x))) →
      Tendsto V atTop (𝓝 ((∫ s in Set.Ioi 0, v s) / ∫ x, x ∂(R.G.tilted (fun x => θ * x)))))
    (x : ℝ) :
    (NonlatticeRenewalInput.ofLadder hX hnl L R hKRT).C = R.tailConst ∧
      Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x}) atTop
        (𝓝 (Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * x)))))) :=
  ⟨rfl, NonlatticeRenewalInput.tendsto_gumbel_ofLadder hX hnl L R hKRT x⟩

example (hX : CramerScores P X θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, X i ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (hlatY : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, L.Y i ω = k * h)
    (R : LatticeLadderRenewalData P (L.Y 0) θ h) (x : ℝ) (hC : 0 < R.tailConst) :
    (LatticeRenewalInput.ofLadder hX hh hlat L hlatY R).C = R.tailConst ∧
      (∀ᶠ n : ℕ in atTop, Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * x)))) - 1 ≤
          P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x} ∧
        P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x} ≤
          Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * (x + h))))) + 1) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x})
        atTop (𝓝 l) :=
  ⟨rfl, LatticeRenewalInput.eventually_bounds_ofLadder hX hh hlat L hlatY R x one_pos,
    fun ⟨l, hl⟩ => (LatticeRenewalInput.ofLadder hX hh hlat L hlatY R).not_tendsto hC x l hl⟩

end

end Cslib.Bioinformatics.Alignment.ScoreSignificance
