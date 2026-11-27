/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.BAFContamination
import Mathlib.Tactic.NormNum

/-!
# Tests for the B-allele-frequency regression estimator of contamination

* BAF values of clean and contaminated samples.
* The conditional mean `α p_B` at `AA` markers for population frequency `p_B = 1/4`, and the
  page's remark: when `B` is always the minor allele, with `f = 1/4`, the conditional mean is
  `α / 4`, not the minor-allele value `3 α / 10`.
* Under the minor-allele model with `f = 1/4`: the probabilities `9/16` and `1/16` that the
  target's genotype, in `A`/`B` labels, is `AA`, the posterior probability `9/10` that `B` is the
  minor allele, and the conditional mean `3 α / 10`.
* A full-rank design of four homozygous markers, on which the regression recovers `α` from
  noiseless data and the null law of the `t` statistic is Student's `t` with one degree of
  freedom.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Biology.PopulationGenetics.HardyWeinberg
open Domains.Biology.StatisticalGenetics.BAFContamination
open scoped ENNReal NNReal

namespace DomainsTest.Biology.StatisticalGenetics.BAFContamination

/-! ### BAF values -/

/-- A clean heterozygous sample has BAF `1/2`, whatever the second genotype. -/
example (g₂ : Bool × Bool) : baf 0 (false, true) g₂ = 1 / 2 := by
  rw [baf_eq]
  simp [countB]

/-- An `AA` target with 10% of its DNA from a `BB` contaminant has BAF `1/10`. -/
example : baf (1 / 10) (false, false) (true, true) = 1 / 10 := by
  rw [baf_eq]
  norm_num [countB]

/-! ### Conditional means -/

/-- Allele frequencies with `p_B = 1/4` and `p_A = 3/4`. -/
noncomputable def quarterB : PMF Bool :=
  PMF.ofFintype (fun b => if b then 1 / 4 else 3 / 4) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [ENNReal.div_add_div_same, ENNReal.div_eq_one_iff (by norm_num) (by norm_num)]
    norm_num)

theorem quarterB_true : (quarterB true).toReal = 1 / 4 := by
  simp [quarterB]

theorem quarterB_false : (quarterB false).toReal = 3 / 4 := by
  simp [quarterB, ENNReal.toReal_div]

/-- A target whose genotype is drawn from the same frequencies is `AA` with probability `9/16`,
so conditioning on `g = AA` is possible. -/
theorem iidGenotype_quarterB_AA_ne_zero : iidGenotype quarterB (false, false) ≠ 0 := by
  simp [iidGenotype_apply, quarterB]

/-- At `p_B = 1/4`, `E[BAF | g = AA] = α / 4` and `E[BAF | g = BB] = 1 - 3 α / 4`. -/
example (α : ℝ) (T : PMF (Bool × Bool)) (hAA : T (false, false) ≠ 0)
    (hBB : T (true, true) ≠ 0) :
    ∫ x, baf α x.1 x.2 ∂((markerLaw T quarterB).toMeasure[|Prod.fst ⁻¹' {(false, false)}]) =
        α / 4 ∧
      ∫ x, baf α x.1 x.2 ∂((markerLaw T quarterB).toMeasure[|Prod.fst ⁻¹' {(true, true)}]) =
        1 - 3 * α / 4 := by
  rw [integral_baf_cond_homA α T quarterB hAA, integral_baf_cond_homB α T quarterB hBB,
    quarterB_true, quarterB_false]
  constructor <;> ring

/-- **The minor-allele formula needs its assumptions** (the page's remark): if `B` is always
the minor allele, with frequency `f = 1/4`, then at an `AA` marker the conditional mean is
`α p_B = α / 4`, which differs from the minor-allele value
`α f (1 - f) / ((1 - f)² + f²) = 3 α / 10` whenever `α ≠ 0`. -/
example (α : ℝ) (hα : α ≠ 0) :
    ∫ x, baf α x.1 x.2 ∂((markerLaw (iidGenotype quarterB) quarterB).toMeasure[|
        Prod.fst ⁻¹' {(false, false)}]) ≠
      α * (1 / 4) * (1 - 1 / 4) / ((1 - 1 / 4) ^ 2 + (1 / 4) ^ 2) := by
  rw [integral_baf_cond_homA α _ quarterB iidGenotype_quarterB_AA_ne_zero, quarterB_true]
  intro h
  apply hα
  norm_num at h
  linarith

/-! ### The minor-allele covariate -/

/-- A population in Hardy–Weinberg proportions whose minor allele (`true`) has frequency `1/4`. -/
noncomputable def quarterMinor : PMF (Bool × Bool) := iidGenotype quarterB

theorem gamete_quarterMinor_true : (gamete quarterMinor true).toReal = 1 / 4 := by
  rw [quarterMinor, gamete_iidGenotype, quarterB_true]

/-- With minor allele frequency `f = 1/4`, the target's genotype, in `A`/`B` labels, is `AA` with
probability `(1 - f)² = 9/16` when `B` is the minor allele and `f² = 1/16` when `A` is. -/
example : (callLikelihood quarterMinor true).real {(false, false)} = 9 / 16 ∧
    (callLikelihood quarterMinor false).real {(false, false)} = 1 / 16 := by
  have h := freq_true_add_freq_false quarterMinor
  rw [gamete_quarterMinor_true] at h
  rw [Measure.real, Measure.real, callLikelihood_true_homA, callLikelihood_false_homA,
    ENNReal.toReal_pow, ENNReal.toReal_pow, gamete_quarterMinor_true,
    show (gamete quarterMinor false).toReal = 3 / 4 by linarith]
  constructor <;> norm_num

/-- With minor allele frequency `f = 1/4`, the posterior probability that `B` is the minor allele
when the target's genotype, in `A`/`B` labels, is `AA` is `(9/16) / (9/16 + 1/16) = 9/10`. -/
example : (((callLikelihood quarterMinor)†(PMF.uniformFintype Bool).toMeasure)
    (false, false)).real {true} = 9 / 10 := by
  rw [posterior_callLikelihood_homA, gamete_quarterMinor_true]
  norm_num

/-- With minor allele frequency `f = 1/4`, `E[BAF | g = AA] = α f (1 - f) / ((1 - f)² + f²)`
is `3 α / 10`. -/
example (α : ℝ) :
    ∫ x, baf α (toABGenotype x.1 x.2.1) (toABGenotype x.1 x.2.2)
        ∂((minorAlleleLaw quarterMinor).toMeasure[|
          {x | toABGenotype x.1 x.2.1 = (false, false)}]) = 3 * α / 10 := by
  rw [integral_baf_cond_minorAllele, gamete_quarterMinor_true]
  ring

/-! ### A full-rank design -/

/-- Two `AA` markers and two `BB` markers. -/
def callsEx : Fin 4 → Bool := ![false, false, true, true]

/-- Population frequencies of `B` at the four markers. -/
noncomputable def freqsEx : Fin 4 → ℝ := ![1 / 4, 1 / 2, 1 / 4, 1 / 2]

/-- The design with rows `(1, 1/4, 1)`, `(1, 1/2, 1)`, `(1, -3/4, 0)`, `(1, -1/2, 0)` has full
rank: `det (Xᵀ X) = 1/4`. -/
theorem isUnit_gram_designMatrix_ex :
    IsUnit ((designMatrix callsEx freqsEx)ᵀ * designMatrix callsEx freqsEx) := by
  have h : (designMatrix callsEx freqsEx)ᵀ * designMatrix callsEx freqsEx =
      !![4, -1 / 2, 2; -1 / 2, 9 / 8, 3 / 4; 2, 3 / 4, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [designMatrix, designRow, signedFreq, indicatorAA, callsEx, freqsEx, Matrix.mul_apply,
        Function.swap,
        Fin.sum_univ_four] <;> norm_num
  rw [h, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_three]
  simp
  norm_num

/-- On this design the regression recovers the contamination level from noiseless BAF values on
the line `1 + α p - 1(g = AA)` of the conditional means. -/
example (α : ℝ) :
    contaminationEstimate callsEx freqsEx (designMatrix callsEx freqsEx *ᵥ ![1, α, -1]) = α :=
  contaminationEstimate_mulVec callsEx freqsEx isUnit_gram_designMatrix_ex 1 α (-1)

/-- On this design, with no contamination and standard Gaussian errors, the `t` statistic has
Student's `t` law with `4 - 3 = 1` degree of freedom. -/
example (γ τ : ℝ) :
    HasLaw (fun ε : Fin 4 → ℝ =>
        contaminationTStatistic callsEx freqsEx (designMatrix callsEx freqsEx *ᵥ ![γ, 0, τ] + ε))
      (studentTMeasure 1) (Measure.pi fun _ : Fin 4 => gaussianReal 0 1) := by
  have h := hasLaw_contaminationTStatistic callsEx freqsEx isUnit_gram_designMatrix_ex
    (by simp) γ τ (μ := Measure.pi fun _ : Fin 4 => gaussianReal 0 1) (ε := id) one_pos
    (by simp only [inv_one, one_smul, id_eq]; exact HasLaw.id)
  simpa using h

end DomainsTest.Biology.StatisticalGenetics.BAFContamination
