/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
import MathlibExt.Biology.PopulationGenetics.Admixture.F3SufficientNotNecessary
import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
open scoped ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.FStatisticsCovariance

/-! ### Centred covariance on a Dirac measure -/

/-- Three populations with frequencies `0.2`, `0.5`, `0.8` at a single outcome (mean `0.5`). -/
noncomputable def pD : Fin 3 → Unit → ℝ := fun X _ => ![1/5, 1/2, 4/5] X

example : centredCov (Measure.dirac ()) pD 0 2 = -9 / 100 := by
  simp [centredCov, popMean, pD, Fin.sum_univ_three]
  norm_num

example : f2 (Measure.dirac ()) pD 0 2 =
    centredCov (Measure.dirac ()) pD 0 0 + centredCov (Measure.dirac ()) pD 2 2 -
      2 * centredCov (Measure.dirac ()) pD 0 2 :=
  f2_eq_centredCov (fun _ => MemLp.of_discrete) 0 2

example : centredCov (Measure.dirac ()) pD 0 2 = doubleCenter (f2 (Measure.dirac ()) pD) 0 2 / 2 :=
  centredCov_eq_doubleCenter_f2 (fun _ => MemLp.of_discrete) 0 2

/-! ### Symmetry and row sums of the centred covariance -/

example : centredCov (Measure.dirac ()) pD 0 2 = centredCov (Measure.dirac ()) pD 2 0 :=
  centredCov_comm 0 2

example : ∑ Y, centredCov (Measure.dirac ()) pD 0 Y = 0 :=
  sum_centredCov_eq_zero (fun _ => MemLp.of_discrete) 0

/-- Column sums vanish by symmetry. -/
example : ∑ X, centredCov (Measure.dirac ()) pD X 2 = 0 := by
  calc ∑ X, centredCov (Measure.dirac ()) pD X 2
      = ∑ X, centredCov (Measure.dirac ()) pD 2 X :=
        Finset.sum_congr rfl fun X _ => centredCov_comm X 2
    _ = 0 := sum_centredCov_eq_zero (fun _ => MemLp.of_discrete) 2

/-! ### The f-indistinguishable pair, realized on four points

`Ω = Fin 4` with the uniform probability measure and the orthogonal mean-zero sign vectors
`w₁, w₂, w₃`. Both models have root frequency `1/2`; `A`, `B` sit on edges with drift length
`1/64`. In the admixture model `C` is a `1/2 : 1/2` mixture with private drift `9/1024`; in the
star tree the leaf edges have lengths `1/64`, `1/64`, `1/1024`. All frequencies lie in
`[0, 1]`. -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Orthogonal sign vectors, scaled by `s₁`, `s₂`, `s₃`. -/
noncomputable def walsh (s : Fin 3 → ℝ) : Fin 3 → Fin 4 → ℝ :=
  ![fun ω => s 0 * ![1, 1, -1, -1] ω, fun ω => s 1 * ![1, -1, 1, -1] ω,
    fun ω => s 2 * ![1, -1, -1, 1] ω]

/-- The star-tree witness. -/
noncomputable def Mstar : DriftModel μ4 (Fin 3) (Fin 3) where
  root := fun _ => 1/2
  incr := walsh ![1/8, 1/8, 1/32]
  len := starLen (1/2) (1/64) (1/64) (9/1024)
  weight := starWeight
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, walsh]
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, walsh, starLen] <;> norm_num

/-- The admixture witness. -/
noncomputable def Madmix : DriftModel μ4 (Fin 3) (Fin 3) where
  root := fun _ => 1/2
  incr := walsh ![1/8, 1/8, 3/32]
  len := ![1/64, 1/64, 9/1024]
  weight := admixWeight (1/2)
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, walsh]
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, walsh] <;> norm_num

/-- The star tree's leaf edges are `1/64`, `1/64`, `1/1024`. -/
example : Mstar.len = ![1/64, 1/64, 1/1024] := by
  funext e
  fin_cases e <;> simp [Mstar, starLen] <;> norm_num

/-- The two models have the same `f2` at every pair, hence the same f-statistics. -/
example (X Y : Fin 3) : f2 μ4 Mstar.freq X Y = f2 μ4 Madmix.freq X Y :=
  f2_star_eq_f2_admix rfl rfl rfl rfl X Y

example (A B C D : Fin 3) : f4 μ4 Mstar.freq A B C D = f4 μ4 Madmix.freq A B C D :=
  f4_star_eq_f4_admix rfl rfl rfl rfl A B C D

/-- ... and the same centred leaf covariance. -/
example (X Y : Fin 3) : centredCov μ4 Mstar.freq X Y = centredCov μ4 Madmix.freq X Y :=
  (f2_eq_iff_centredCov_eq Mstar.memLp_freq Madmix.memLp_freq).mp
    (f2_star_eq_f2_admix rfl rfl rfl rfl) X Y

/-- One model is a tree (binary loadings), the other is not. -/
example : Mstar.HasBinaryLoadings ∧ ¬ Madmix.HasBinaryLoadings :=
  ⟨hasBinaryLoadings_star rfl, not_hasBinaryLoadings_admix (by norm_num) (by norm_num) rfl⟩

/-- The admixed population is the mixture of `A` and `B` plus its private edge. -/
example : Madmix.weight 2 = (1/2 : ℝ) • Madmix.weight 0 + (1 - 1/2 : ℝ) • Madmix.weight 1 +
    Pi.single 2 1 :=
  admixWeight_two (1/2)

/-- Post-admixture drift masks the admixture: `f3 C A B = 9/1024 - (1/4)(1/32) = 1/1024 > 0`. -/
example : f3 μ4 Madmix.freq 2 0 1 = 1 / 1024 := by
  rw [Madmix.f3_freq]
  simp [Madmix, admixWeight, starWeight, Fin.sum_univ_three]
  norm_num

/-- The star edges are nonnegative exactly in the masked regime. -/
example (e : Fin 3) : 0 ≤ starLen (1/2) (1/64) (1/64) (9/1024) e :=
  starLen_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) e

/-- Boundary: without masking (`c = 0`) the matching star tree needs a negative edge. -/
example : starLen (1/2) 1 1 0 2 < 0 := by
  simp [starLen]
  norm_num

#print axioms centredCov_eq_doubleCenter_f2
#print axioms sum_centredCov_eq_zero
#print axioms centredCov_comm
#print axioms f2_eq_iff_centredCov_eq
#print axioms f2_star_eq_f2_admix

/-! ### Star tree versus admixture: f3 corollaries -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

-- Acceptance "α = 0 degenerates to identical models": `admixWeight 0` is a tree (binary
-- loadings), the matching star lengths are `![a + b, 0, c]`, and frequencies coincide exactly.
example : ∀ X e, admixWeight 0 X e = 0 ∨ admixWeight 0 X e = 1 := by
  intro X e; fin_cases X <;> fin_cases e <;> simp [admixWeight, starWeight]
example (a b c : ℝ) : starLen 0 a b c = ![a + b, 0, c] := by
  funext e; fin_cases e <;> simp [starLen]

-- The degeneration is non-vacuous: for every `a, b, c ≥ 0` there are realized admixed models at
-- `α = 0`, and each has a star-tree partner with identical frequencies.
example {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M M' : DriftModel μ (Fin 3) (Fin 3)), M.weight = admixWeight 0 ∧ M.len = ![a, b, c] ∧
        M'.weight = starWeight ∧ M'.len = ![a + b, 0, c] ∧ M'.freq = M.freq := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel (admixWeight 0) ![a, b, c]
      (by intro e; fin_cases e <;> simp [ha, hb, hc])
  obtain ⟨M', hw', hl', hf⟩ := exists_star_freq_eq_of_admix_zero M hw hl
  refine ⟨Ω, hΩ, μ, hμ, M, M', hw, hl, hw', ?_, hf⟩
  rw [hl']; funext e; fin_cases e <;> simp [starLen]

-- Both directions of the iff are exercised. Boundary `c = α (1 - α) (a + b)`: at `α = 1/2`,
-- `a = b = 1`, `c = 1/2` the star lengths are `(1, 1, 0)` and `f3 = 0`.
example {M : DriftModel μ (Fin 3) (Fin 3)} (hw : M.weight = admixWeight (1 / 2))
    (hl : M.len = ![1, 1, 1 / 2]) :
    f3 μ M.freq 2 0 1 = 0 ∧ (∀ e, 0 ≤ starLen (1 / 2) 1 1 (1 / 2) e) := by
  refine ⟨by rw [f3_admixWeight hw hl]; norm_num, ?_⟩
  rw [starLen_nonneg_iff_f3_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hl,
    f3_admixWeight hw hl]
  norm_num
-- Below the boundary (`c = 1/4`): `f3 = -1/4 < 0` and the star tree's leaf `C` would need a
-- negative length, so no star-tree drift model has those lengths (`len_nonneg`).
example {M : DriftModel μ (Fin 3) (Fin 3)} (hw : M.weight = admixWeight (1 / 2))
    (hl : M.len = ![1, 1, 1 / 4]) :
    f3 μ M.freq 2 0 1 < 0 ∧ ¬ (∀ e, 0 ≤ starLen (1 / 2) 1 1 (1 / 4) e) ∧
      ∀ M' : DriftModel μ (Fin 3) (Fin 3), M'.len ≠ starLen (1 / 2) 1 1 (1 / 4) := by
  have hf : f3 μ M.freq 2 0 1 = -1 / 4 := by rw [f3_admixWeight hw hl]; norm_num
  refine ⟨by rw [hf]; norm_num, ?_, fun M' h => ?_⟩
  · rw [starLen_nonneg_iff_f3_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hl,
      hf]
    norm_num
  · have := M'.len_nonneg 2
    rw [h] at this
    norm_num [starLen] at this

end MathlibExtTest.Biology.PopulationGenetics.FStatisticsCovariance
