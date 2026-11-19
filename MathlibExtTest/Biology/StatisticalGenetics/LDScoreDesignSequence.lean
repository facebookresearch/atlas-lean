/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreDesignSequence

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.FiniteProbability
  MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Biology.StatisticalGenetics.LDScoreVariance
  MathlibExt.Biology.StatisticalGenetics.LDScoreDesignSequence
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScoreDesignSequence

/-! ### The Rademacher law satisfies `IsBoundedUnitLaw` with `C = 1`

Computed from the definition `(δ₁ + δ₋₁) / 2`. -/

/-- The Rademacher law `(δ₁ + δ₋₁) / 2`. -/
noncomputable def rad : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 1 + Measure.dirac (-1))

instance : IsProbabilityMeasure rad := ⟨by
  simp only [rad, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul]
  rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]⟩

theorem rad_law : IsBoundedUnitLaw rad 1 where
  integral_id := by
    rw [rad, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
      (integrable_dirac (by simp)), integral_dirac, integral_dirac]
    norm_num
  integral_sq := by
    rw [rad, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
      (integrable_dirac (by simp)), integral_dirac, integral_dirac]
    norm_num
  ae_abs_le := by
    have hm : MeasurableSet {x : ℝ | ¬ |x| ≤ 1} :=
      (measurableSet_le (f := fun x : ℝ => |x|) (by fun_prop) measurable_const).compl
    rw [ae_iff, rad, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm,
      Measure.dirac_apply' _ hm]
    simp

/-! ### A template block with real LD

Eight individuals, three markers: markers `0` and `1` are equicorrelated with `r = 1/2`, and
marker `2` is uncorrelated with both. The LD scores are `(5/4, 5/4, 1)`, not all equal, with
spread `S_ℓℓ = 1/24`. All values are computed from the definitions. -/

/-- The template genotype matrix (columns standardized: mean `0`, sum of squares `8`). -/
def T8 : Matrix (Fin 8) (Fin 3) ℝ :=
  !![1, 1, 1;
     1, 1, -1;
     1, 1, -1;
     1, -1, 1;
     -1, 1, 1;
     -1, -1, -1;
     -1, -1, -1;
     -1, -1, 1]

theorem T8_isStandardized : IsStandardized T8 := by
  intro a
  fin_cases a <;> simp [T8, Fin.sum_univ_eight] <;> norm_num

/-- Markers `0` and `1` are in LD `r = 1/2`. -/
theorem ldCorr_T8_01 : ldCorr T8 0 1 = 1 / 2 := by
  simp [ldCorr, T8, Fin.sum_univ_eight]
  norm_num

/-- Marker `2` is uncorrelated with marker `0`. -/
theorem ldCorr_T8_02 : ldCorr T8 0 2 = 0 := by
  simp [ldCorr, T8, Fin.sum_univ_eight]

theorem ldScore_T8 : ldScore T8 = ![5 / 4, 5 / 4, 1] := by
  funext a
  fin_cases a <;> simp [ldScore, ldCorr, T8, Fin.sum_univ_eight, Fin.sum_univ_three] <;> norm_num

theorem sxy_ldScore_T8 : sxy (ldScore T8) (ldScore T8) = 1 / 24 := by
  rw [ldScore_T8]
  simp [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

theorem T8_spread : 0 < sxy (ldScore T8) (ldScore T8) := by
  rw [sxy_ldScore_T8]
  norm_num

/-! ### The doubling sequence: `2 ^ n` copies of the template

`N = 8 · 2 ^ n` individuals and `M = 3 · 2 ^ n` markers; every hypothesis is verified above from
the definitions, and the T161 model, the variance bound, the variance limit and the consistency
theorem are instantiated. -/

/-- The design with `2 ^ n` copies of the template. -/
noncomputable def design (n : ℕ) : BlockDesign (2 ^ n * 8) (2 ^ n * 3) 3 8 :=
  replicateDesign T8 T8_isStandardized (2 ^ n)

theorem design_NM (n : ℕ) : ((2 ^ n * 8 : ℕ) : ℝ) ≤ 8 / 3 * ((2 ^ n * 3 : ℕ) : ℝ) := by
  push_cast
  linarith

theorem h2_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num

theorem h2_le_one : (1 : ℝ) / 2 ≤ 1 := by norm_num

/-- The T161 hypotheses along the doubling sequence: the LD-block model with `K = 3`. -/
noncomputable def design_ldBlockModel (n : ℕ) :=
  ldBlockModel (design n) rad_law h2_nonneg h2_le_one (by norm_num) (design_NM n)

/-- The almost-sure bound on the statistics is `8 · 2 · (9 · 8/3 + 1) = 400`. -/
theorem chiSqBound_design : chiSqBound 3 8 1 (8 / 3) = 400 := by
  norm_num [chiSqBound]

/-- Within a copy, the replicated design keeps the template's LD `r = 1/2`. -/
theorem ldCorr_design (n : ℕ) (u : Fin (2 ^ n)) :
    ldCorr (design n).X (finProdFinEquiv (u, 0)) (finProdFinEquiv (u, 1)) = 1 / 2 := by
  change ldCorr (replicate T8 (2 ^ n)) _ _ = _
  rw [ldCorr_replicate T8 (pow_ne_zero n two_ne_zero), ite_eq_left rfl, ldCorr_T8_01]

/-- Across copies, markers are uncorrelated. -/
theorem ldCorr_design_ne (n : ℕ) {u u' : Fin (2 ^ n)} (h : u ≠ u') :
    ldCorr (design n).X (finProdFinEquiv (u, 0)) (finProdFinEquiv (u', 0)) = 0 := by
  change ldCorr (replicate T8 (2 ^ n)) _ _ = _
  rw [ldCorr_replicate T8 (pow_ne_zero n two_ne_zero), ite_eq_right h]

/-- The T161 variance bound for each design of the sequence. -/
theorem variance_design_le (n : ℕ) :
    Var[fun ω => olsH2Hat (2 ^ n * 8) (2 ^ n * 3) (ldScore (design n).X) fun j =>
      chiSqStrat (model rad_law h2_nonneg h2_le_one (2 ^ n * 8) (2 ^ n * 3)) (design n).X 0 0 j ω;
      coordMeasure rad] ≤
      (((2 ^ n * 3 : ℕ) : ℝ) / ((2 ^ n * 8 : ℕ) : ℝ)) ^ 2 *
        (3 * (chiSqBound 3 8 1 (8 / 3) / 2) ^ 2 /
          sxy (ldScore (design n).X) (ldScore (design n).X)) :=
  variance_olsH2Hat_le (design n) rad_law h2_nonneg h2_le_one (by norm_num) (design_NM n)

/-- `Var(ĥ²) → 0` along the doubling sequence. -/
theorem tendsto_variance_design :
    Tendsto (fun n : ℕ => Var[fun ω => olsH2Hat (2 ^ n * 8) (2 ^ n * 3)
      (ldScore (replicate T8 (2 ^ n))) fun j =>
        chiSqStrat (model rad_law h2_nonneg h2_le_one (2 ^ n * 8) (2 ^ n * 3))
          (replicate T8 (2 ^ n)) 0 0 j ω; coordMeasure rad]) atTop (𝓝 0) :=
  tendsto_variance_olsH2Hat_replicate T8 rad_law h2_nonneg h2_le_one T8_isStandardized T8_spread
    (fun n => pow_ne_zero n two_ne_zero) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **`ĥ² → 1/2` in probability along the doubling sequence.** -/
theorem tendstoInMeasure_design :
    TendstoInMeasure (coordMeasure rad) (fun (n : ℕ) ω => olsH2Hat (2 ^ n * 8) (2 ^ n * 3)
      (ldScore (replicate T8 (2 ^ n))) fun j =>
        chiSqStrat (model rad_law h2_nonneg h2_le_one (2 ^ n * 8) (2 ^ n * 3))
          (replicate T8 (2 ^ n)) 0 0 j ω) atTop fun _ => 1 / 2 :=
  tendstoInMeasure_olsH2Hat_replicate T8 rad_law h2_nonneg h2_le_one T8_isStandardized T8_spread
    (fun n => pow_ne_zero n two_ne_zero) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-! ### Unbounded LD: the limit is not claimed

`copies m` has `m` identical markers on two individuals (perfect LD). Its LD scores are all `m`,
so LD is unbounded as `m → ∞`; every marker shares its individuals, so any block design for it
has a block of size `m`, and no uniform block bound `K` exists. The spread is `0` as well. The
hypotheses of `tendstoInMeasure_olsH2Hat_blockDesign` fail, and no limit is claimed. -/

/-- `m` copies of the standardized column `(1, -1)`. -/
def copies (m : ℕ) : Matrix (Fin 2) (Fin m) ℝ := fun i _ => if i = 0 then 1 else -1

theorem copies_isStandardized (m : ℕ) : IsStandardized (copies m) := by
  intro j
  simp [copies, Fin.sum_univ_two]

theorem ldScore_copies (m : ℕ) (j : Fin m) : ldScore (copies m) j = m := by
  simp [ldScore, ldCorr, copies, Fin.sum_univ_two]

/-- The LD scores of `copies` are unbounded. -/
theorem not_bounded_ldScore_copies : ¬ ∃ B : ℝ, ∀ m (j : Fin m), ldScore (copies m) j ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨m, hm⟩ := exists_nat_gt B
  have h := hB (m + 1) 0
  rw [ldScore_copies] at h
  push_cast at h
  linarith

/-- The LD scores of `copies` are all equal, so the slope is not identified. -/
theorem sxy_ldScore_copies (m : ℕ) : sxy (ldScore (copies m)) (ldScore (copies m)) = 0 := by
  have h : ldScore (copies m) = fun _ => (m : ℝ) := funext (ldScore_copies m)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [sxy]
  · rw [h]
    simp [sxy, sampleMean_eq_sum_div]

/-- Every block design for `copies m` has a block with all `m` markers. -/
theorem le_of_blockDesign_copies {m K G : ℕ} (D : BlockDesign 2 m K G) (hD : D.X = copies m) :
    m ≤ K := by
  have hblock : ∀ j, D.block j = D.group 0 := fun j =>
    (D.support 0 j (by simp [hD, copies])).symm
  have h := D.card_block_le (D.group 0)
  simpa [hblock] using h

/-- **No uniform block bound.** No `K` bounds the block sizes of block designs for every
`copies m`. -/
theorem not_uniform_blockDesign_copies :
    ¬ ∃ K G : ℕ, ∀ m, ∃ D : BlockDesign 2 m K G, D.X = copies m := by
  rintro ⟨K, G, h⟩
  obtain ⟨D, hD⟩ := h (K + 1)
  have := le_of_blockDesign_copies D hD
  omega

/-! ### A fixed design: the sequence hypotheses fail

With a single copy repeated (`b n = 1`, so `M n = 3` for every `n`), the marker count does not
tend to infinity, so neither `tendstoInMeasure_olsH2Hat_replicate` nor
`tendstoInMeasure_olsH2Hat_blockDesign` applies. -/

theorem not_tendsto_fixed_copies : ¬ Tendsto (fun _ : ℕ => (1 : ℕ)) atTop atTop :=
  not_tendsto_const_atTop 1 atTop

theorem not_tendsto_fixed_markers : ¬ Tendsto (fun _ : ℕ => 1 * 3) atTop atTop :=
  not_tendsto_const_atTop (1 * 3) atTop

end MathlibExtTest.Biology.StatisticalGenetics.LDScoreDesignSequence
