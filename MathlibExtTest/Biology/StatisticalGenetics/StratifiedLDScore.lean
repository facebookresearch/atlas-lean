/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.StratifiedLDScore

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.StatisticalGenetics.StratifiedLDScore
open MathlibExt.Biology.StatisticalGenetics
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.StratifiedLDScore

/-! ### A non-vacuous model with unequal per-marker variances

`Ω = Fin 4` with the uniform probability measure; `had i` are the four orthogonal Hadamard sign
vectors scaled by `1/2` (second moment `1/4`). Two markers with effects `had 1` and `2 had 2`
(variances `1/4` and `1`) and two individuals with noise `had 0`, `had 3` (variance `1/4`). -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Hadamard sign vectors of length `4`, scaled by `1/2`. -/
noncomputable def had : Fin 4 → Fin 4 → ℝ :=
  ![![1/2, 1/2, 1/2, 1/2], ![1/2, 1/2, -1/2, -1/2], ![1/2, -1/2, 1/2, -1/2],
    ![1/2, -1/2, -1/2, 1/2]]

/-- The witness model: `σ² = (1/4, 1)`, `σ²_e = 1/4`. -/
noncomputable def D : Model μ4 2 2 where
  sigma2 := ![1 / 4, 1]
  sigmaE2 := 1 / 4
  beta := ![had 1, fun ω => 2 * had 2 ω]
  eps := ![had 0, had 3]
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [integral_μ4, had] <;> norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ4, had] <;> norm_num

/-- Two individuals, two markers in perfect LD (identical standardized columns `(1, -1)`). -/
def X2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, -1]

theorem isStandardized_X2 : LDScore.IsStandardized X2 := by
  intro k
  fin_cases k <;> simp [X2, Fin.sum_univ_two] <;> norm_num

theorem ldCorr_X2 (j k : Fin 2) : LDScore.ldCorr X2 j k = 1 := by
  fin_cases j <;> fin_cases k <;> simp [LDScore.ldCorr, X2, Fin.sum_univ_two]

/-- `𝔼[χ²₀] = N (r₀₀² σ²₀ + r₀₁² σ²₁) + σ²_e = 2 (1/4 + 1) + 1/4 = 11/4`. -/
example : ∫ ω, D.chiSq X2 0 ω ∂μ4 = 11 / 4 := by
  rw [D.integral_chiSq_of_standardized X2 (by norm_num) 0 isStandardized_X2]
  simp [ldCorr_X2, D, Fin.sum_univ_two]
  norm_num

/-- The same value by direct computation of the expectation. -/
example : ∫ ω, D.chiSq X2 0 ω ∂μ4 = 11 / 4 := by
  simp [integral_μ4, Model.chiSq, Model.betaHat, Model.pheno, D, X2, had, Fin.sum_univ_two]
  norm_num

/-! ### Annotations -/

/-- Two annotations: the base annotation `1` and an indicator of marker `1`. -/
def annot : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![1, 1]]

/-- With `τ = (1/4, 3/4)`, `σ²_k = ∑_C τ_C a_{kC}` reproduces `D.sigma2`. -/
theorem sigma2_annot (k : Fin 2) : D.sigma2 k = ∑ C, ![1 / 4, 3 / 4] C * annot k C := by
  fin_cases k <;> simp [D, annot, Fin.sum_univ_two]; norm_num

/-- The annotation LD scores of marker `0`: `ℓ(0, base) = 2`, `ℓ(0, marker 1) = 1`. -/
example : annotLDScore X2 annot 0 0 = 2 ∧ annotLDScore X2 annot 0 1 = 1 := by
  constructor <;> simp [annotLDScore, annot, ldCorr_X2, Fin.sum_univ_two]; norm_num

/-- Stratified LDSC on the witness: `𝔼[χ²₀] = 2 (1/4 · 2 + 3/4 · 1) + 1/4 = 11/4`. -/
example : ∫ ω, D.chiSq X2 0 ω ∂μ4 = 11 / 4 := by
  rw [D.integral_chiSq_of_annot X2 annot _ sigma2_annot (by norm_num) 0 isStandardized_X2]
  simp [annotLDScore, annot, ldCorr_X2, D, Fin.sum_univ_two]
  norm_num

/-- The α model with `p_k = 1/2` and `α = -1` (all annotation values `[1/4]^0 = 1`) on any
model whose per-marker variances follow it with `c = 3`: `𝔼[χ²₀] = 2 · 3 · 2 + σ²_e`. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} (D' : Model μ 2 2)
    (h : ∀ k, D'.sigma2 k = 3 * ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ (1 + (-1 : ℝ))) :
    ∫ ω, D'.chiSq X2 0 ω ∂μ = 12 + D'.sigmaE2 := by
  rw [D'.integral_chiSq_of_alpha X2 (fun _ => 1 / 2) (-1) 3 h (by norm_num) 0
    isStandardized_X2]
  simp [ldCorr_X2]
  norm_num

/-! ### Enrichment -/

/-- Each marker is its own category. -/
def cat : Fin 2 → Fin 2 := id

/-- Category `1` holds `1 / (5/4) = 4/5` of the heritability with `1/2` of the markers:
enrichment `8/5`. -/
example : enrichment D.sigma2 cat 1 = 8 / 5 := by
  have hf : (Finset.univ.filter fun k : Fin 2 => cat k = 1) = {1} := by decide
  simp only [enrichment, catH2, catSize, hf]
  simp [D, Fin.sum_univ_two]
  norm_num

/-- The weighted enrichments sum to one. -/
example : ∑ C, ((catSize cat C : ℝ) / 2) * enrichment D.sigma2 cat C = 1 :=
  sum_size_mul_enrichment D.sigma2 cat (by simp [D, Fin.sum_univ_two]; norm_num)

/-- Junk value outside the domain: with zero total heritability every enrichment is `0`, so the
identity `sum_size_mul_enrichment` (which assumes `h² ≠ 0`) fails. -/
example : ∑ C, ((catSize cat C : ℝ) / 2) * enrichment (fun _ : Fin 2 => (0 : ℝ)) cat C = 0 := by
  simp [enrichment, catH2]

/-! ### Identifiability -/

/-- With markers in perfect LD and only the base annotation, the design `[1 | N ℓ]` has two equal
rows `(1, 4)`: the intercept and `τ` are not identifiable. -/
example : ¬ Function.Injective (design X2 (fun _ (_ : Unit) => (1 : ℝ))).mulVec := by
  intro h
  have h1 : (design X2 (fun _ (_ : Unit) => (1 : ℝ))) *ᵥ (fun c => Option.elim c 4 fun _ => 0) =
      (design X2 (fun _ (_ : Unit) => (1 : ℝ))) *ᵥ (fun c => Option.elim c 0 fun _ => 1) := by
    ext j
    fin_cases j <;>
      simp [design, annotLDScore, ldCorr_X2, mulVec, dotProduct, Fintype.sum_option] <;> norm_num
  have := congrFun (h h1) none
  norm_num at this

/-- Equivalently, the design matrix does not have full column rank. -/
example : (design X2 (fun _ (_ : Unit) => (1 : ℝ))).rank ≠ Fintype.card (Option Unit) := by
  intro hr
  have h := (injective_mulVec_iff_rank_eq_card _).mpr hr
  have h1 : (design X2 (fun _ (_ : Unit) => (1 : ℝ))) *ᵥ (fun c => Option.elim c 4 fun _ => 0) =
      (design X2 (fun _ (_ : Unit) => (1 : ℝ))) *ᵥ (fun c => Option.elim c 0 fun _ => 1) := by
    ext j
    fin_cases j <;>
      simp [design, annotLDScore, ldCorr_X2, mulVec, dotProduct, Fintype.sum_option] <;> norm_num
  have := congrFun (h h1) none
  norm_num at this

/-! ### LDSC-SEG contrast -/

/-- Annotations `(base, G, S)` for three SNPs: SNP `0` in `S ⊆ G`, SNP `1` in `G ∖ S`, SNP `2`
outside `G`. The `S`-vs-`(G ∖ S)` contrast of per-SNP variances is `τ_S`. -/
example (τ : Fin 3 → ℝ) :
    let a : Fin 3 → Fin 3 → ℝ := ![![1, 1, 1], ![1, 1, 0], ![1, 0, 0]]
    ∑ C, τ C * a 0 C - ∑ C, τ C * a 1 C = τ 2 := by
  intro a
  rw [sigma2_sub_sigma2_eq a τ 2 0 1 (by intro C hC; fin_cases C <;> simp_all [a])]
  simp [a]

end MathlibExtTest.Biology.StatisticalGenetics.StratifiedLDScore
