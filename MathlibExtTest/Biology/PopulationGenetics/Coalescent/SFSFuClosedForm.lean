/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm
public import MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSCovariance

/-!
# Tests for Fu's closed form of the SFS covariances

Entries of `fuSigma` for `n = 2, 3, 4` computed from the definitions. Agreement with the
branch-length covariances of Kingman's coalescent is mechanized only for `n = 2` (`fuSigma_K2`);
for `n = 3` it is hand arithmetic, not a Lean check (`L₁ = 3 T₃ + T₂`, `L₂ = T₂`, so
`Var L₁ = 2`, `Cov(L₁, L₂) = Var L₂ = 1`, and `σ = Cov / 4`). Also a row sum, `a₂`, `b₂`
and `c₂` at `n = 4` computed directly, independently of the theorems; the boundary `n = 3`, where
Tajima's numerator vanishes; and the Kingman witness of sample size `2`, on which the
hypothesis `Cov(L_i, L_j) = 4 σ_{ij}` holds with a nonzero covariance (`Var L₁ = 4`), and on
which every theorem taking that hypothesis is instantiated.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSCovariance

/-! ### Entries computed from the definitions -/

/-- `n = 2` (the case `2 i = n`): `σ₁₁ = 2 (a₂ - a₁) / 1 - 1 = 1`, i.e. `Var L₁ = Var(2 T₂) = 4`. -/
example : fuSigma 2 1 1 = 1 := by
  norm_num [fuSigma, tajimaA1]

/-- `n = 3`: `σ₁₁ = β₃(2) = 1/2`, `σ₁₂ = 1/4` (the case `i + j = n`), `σ₂₂ = β₃(2) - 1/4 = 1/4`. -/
example : fuSigma 3 1 1 = 1 / 2 ∧ fuSigma 3 1 2 = 1 / 4 ∧ fuSigma 3 2 2 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]

/-- `n = 4`: an entry of each kind: `σ₁₂ = -1/18` (`i + j < n`), `σ₂₂ = 7/12` (`2 i = n`),
`σ₂₃ = -1/9` (`i + j > n`), `σ₁₃ = 2/9` (`i + j = n`). -/
example : fuSigma 4 1 2 = -1 / 18 ∧ fuSigma 4 2 2 = 7 / 12 ∧ fuSigma 4 2 3 = -1 / 9 ∧
    fuSigma 4 1 3 = 2 / 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]

/-- Symmetry. -/
example : fuSigma 4 3 1 = fuSigma 4 1 3 := fuSigma_comm 4 3 1

/-- `n = 4`, row `2`, computed directly: `-1/18 + 7/12 - 1/9 = 5/12`. -/
example : ∑ j ∈ Ico 1 4, fuSigma 4 2 j = 5 / 12 := by
  norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]

/-- The same row from `sum_fuSigma_row`: `(a₄ - a₂) / 2 = 5/12`. -/
example : ∑ j ∈ Ico 1 4, fuSigma 4 2 j = 5 / 12 := by
  rw [sum_fuSigma_row (by simp)]
  norm_num [tajimaA1, sum_Ico_succ_top]

/-- `n = 4`: `∑_{i,j} σ_{ij} = 49/36 = a₂`, computed directly. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4, fuSigma 4 i j = 49 / 36 := by
  norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]

/-- The same from `sum_sum_fuSigma`. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4, fuSigma 4 i j = 49 / 36 := by
  rw [sum_sum_fuSigma]
  norm_num [tajimaA2, sum_Ico_succ_top]

/-- `n = 4`: `∑_{i,j} π_i σ_{ij} = 3/4 = (n + 2) / (2 n)`, computed directly. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4,
    (((4 : ℕ) : ℝ) - i) / ((4 : ℕ).choose 2 : ℝ) * i * fuSigma 4 i j = 3 / 4 := by
  norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top, Nat.choose]

/-- `n = 4`: `∑_{i,j} π_i π_j σ_{ij} = 23/54 = b₂`, computed from the definitions, independently
of `sum_sum_piWeight_mul_piWeight_mul_fuSigma`. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4,
    (((4 : ℕ) : ℝ) - i) / ((4 : ℕ).choose 2 : ℝ) * i *
      ((((4 : ℕ) : ℝ) - j) / ((4 : ℕ).choose 2 : ℝ) * j) * fuSigma 4 i j = tajimaB2 4 := by
  norm_num [fuSigma, fuBeta, tajimaA1, tajimaB2, sum_Ico_succ_top, Nat.choose]

/-- `n = 5`: the same, computed from the definitions. -/
example : ∑ i ∈ Ico 1 5, ∑ j ∈ Ico 1 5,
    (((5 : ℕ) : ℝ) - i) / ((5 : ℕ).choose 2 : ℝ) * i *
      ((((5 : ℕ) : ℝ) - j) / ((5 : ℕ).choose 2 : ℝ) * j) * fuSigma 5 i j = tajimaB2 5 := by
  norm_num [fuSigma, fuBeta, tajimaA1, tajimaB2, sum_Ico_succ_top, Nat.choose]

/-- `n = 4`: `∑_{i,j} w_i w_j σ_{ij} = 83/6534`, computed directly from the definitions. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4,
    tajimaNumWeight 4 i * tajimaNumWeight 4 j * fuSigma 4 i j = 83 / 6534 := by
  norm_num [fuSigma, fuBeta, tajimaA1, tajimaNumWeight, sum_Ico_succ_top, Nat.choose]

/-- `n = 4` from `sum_sum_piWeight_mul_piWeight_mul_fuSigma`: `b₂ = 23/54`. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4,
    (((4 : ℕ) : ℝ) - i) / ((4 : ℕ).choose 2 : ℝ) * i *
      ((((4 : ℕ) : ℝ) - j) / ((4 : ℕ).choose 2 : ℝ) * j) * fuSigma 4 i j = 23 / 54 := by
  rw [sum_sum_piWeight_mul_piWeight_mul_fuSigma (by norm_num)]
  norm_num [tajimaB2]

/-- `n = 4`: `∑_{i,j} w_i w_j σ_{ij} = 83/6534` is Tajima's `c₂`, via
`sum_sum_tajimaNumWeight_mul_fuSigma`. -/
example : ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4,
    tajimaNumWeight 4 i * tajimaNumWeight 4 j * fuSigma 4 i j = 83 / 6534 := by
  rw [sum_sum_tajimaNumWeight_mul_fuSigma (by norm_num)]
  norm_num [tajimaC2, tajimaB2, tajimaA1, tajimaA2, sum_Ico_succ_top]

/-- `n = 4`: `c₂ > 0` from Fu's closed form (`TajimaD.tajimaC2_pos`). -/
example : 0 < ∑ i ∈ Ico 1 4, ∑ j ∈ Ico 1 4,
    tajimaNumWeight 4 i * tajimaNumWeight 4 j * fuSigma 4 i j := by
  rw [sum_sum_tajimaNumWeight_mul_fuSigma (by norm_num)]
  exact tajimaC2_pos le_rfl

/-- Boundary `n = 3`: the numerator weights vanish, so the double sum is `0 = c₂`. -/
example : ∑ i ∈ Ico 1 3, ∑ j ∈ Ico 1 3,
    tajimaNumWeight 3 i * tajimaNumWeight 3 j * fuSigma 3 i j = 0 := by
  norm_num [tajimaNumWeight, tajimaA1, sum_Ico_succ_top, Nat.choose]

/-! ### The Kingman witness of sample size `2` -/

section Kingman

/-- On the witness, `L₁ = 2 T₂` is the total branch length. -/
lemma sfsLength_K2_one :
    (fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω)) = K2.totalLength := by
  funext ω
  simp [sfsLength, tau2, KingmanTimes.totalLength]

/-- **The Fu hypothesis holds with a nonzero covariance**: `Cov(L₁, L₁) = Var(2 T₂) = 4 = 4 σ₁₁`
on the Kingman witness of sample size `2`. -/
lemma fuSigma_K2 : ∀ i ∈ Ico 1 2, ∀ j ∈ Ico 1 2,
    cov[fun ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω),
      fun ω => sfsLength 2 j (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 * fuSigma 2 i j := by
  intro i hi j hj
  obtain rfl : i = 1 := by simp at hi; omega
  obtain rfl : j = 1 := by simp at hj; omega
  rw [sfsLength_K2_one, covariance_self
    ((memLp_sfsLength (K := K2) comap_tau2_le law_tau2 1).aestronglyMeasurable.aemeasurable.congr
      (by rw [sfsLength_K2_one])), K2.variance_totalLength]
  norm_num [fuSigma, tajimaA1, tajimaA2]

/-- `variance_sum_sfsLength_of_fuSigma` on the witness: `Var(c L₁) = 4 c²`. -/
example (c : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ Ico 1 2, c i * sfsLength 2 i (tau2 ω) (fun k => K2.T k ω); piMeasure 2] =
      4 * c 1 ^ 2 := by
  rw [variance_sum_sfsLength_of_fuSigma comap_tau2_le law_tau2 fuSigma_K2]
  norm_num [fuSigma, tajimaA1]
  ring

/-- `variance_sum_sfsLength_one_of_fuSigma` on the witness: `Var L₁ = 4 a₂ = 4`. -/
example : Var[fun ω => ∑ i ∈ Ico 1 2, sfsLength 2 i (tau2 ω) (fun k => K2.T k ω);
    piMeasure 2] = 4 := by
  rw [variance_sum_sfsLength_one_of_fuSigma comap_tau2_le law_tau2 fuSigma_K2]
  norm_num [tajimaA2]

/-- `variance_thetaPi_sfsLength_of_fuSigma` on the witness: `Var(θ_π[L]) = 4 b₂ = 4`. -/
example : Var[thetaPi 2 (fun i ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω)); piMeasure 2] =
    4 := by
  rw [variance_thetaPi_sfsLength_of_fuSigma le_rfl comap_tau2_le law_tau2 fuSigma_K2]
  norm_num [tajimaB2]

/-- All hypotheses of `covariance_count_kingman_of_fuSigma` hold jointly on the witness. -/
example : cov[(fun _ _ => (0 : ℝ)) 1, (fun _ _ => (0 : ℝ)) 1; piMeasure 2] =
    (if 1 = 1 then 0 / ((1 : ℕ) : ℝ) else 0) + 0 ^ 2 * fuSigma 2 1 1 :=
  covariance_count_kingman_of_fuSigma measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2 fuSigma_K2 (by simp) (by simp)

/-- All hypotheses of `variance_sum_kingman_of_fuSigma` hold jointly on the witness. -/
example (a : ℕ → ℝ) : Var[fun ω => ∑ i ∈ Ico 1 2, a i * (fun _ _ => (0 : ℝ)) i ω; piMeasure 2] =
    0 * ∑ i ∈ Ico 1 2, a i ^ 2 / i +
      0 ^ 2 * ∑ i ∈ Ico 1 2, ∑ j ∈ Ico 1 2, a i * a j * fuSigma 2 i j :=
  variance_sum_kingman_of_fuSigma measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2 fuSigma_K2 a

/-- All hypotheses of `variance_watterson_kingman_of_fuSigma` hold jointly on the witness. -/
example : Var[fun ω => (∑ i ∈ Ico 1 2, (fun _ _ => (0 : ℝ)) i ω) / tajimaA1 2; piMeasure 2] =
    0 / tajimaA1 2 + 0 ^ 2 * tajimaA2 2 / tajimaA1 2 ^ 2 :=
  variance_watterson_kingman_of_fuSigma le_rfl measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2 fuSigma_K2

/-- All hypotheses of `variance_thetaPi_kingman_of_fuSigma` hold jointly on the witness. -/
example : Var[thetaPi 2 (fun _ _ => (0 : ℝ)); piMeasure 2] = tajimaB1 2 * 0 + tajimaB2 2 * 0 ^ 2 :=
  variance_thetaPi_kingman_of_fuSigma le_rfl measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2 fuSigma_K2

/-- `variance_tajimaNumWeight_sfsLength_of_fuSigma` on the witness. Degenerate: at `n = 2`,
`w₁ = 0` and `c₂ = 0`, so this is `0 = 0`; only the `Var L₁ = 4` and `4 b₂ = 4` instances above
are non-degenerate. -/
example : Var[fun ω => ∑ i ∈ Ico 1 2, tajimaNumWeight 2 i *
      sfsLength 2 i (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 * tajimaC2 2 :=
  variance_tajimaNumWeight_sfsLength_of_fuSigma le_rfl comap_tau2_le law_tau2 fuSigma_K2

/-- All hypotheses of `variance_tajimaNumerator_kingman_of_fuSigma` hold jointly on the witness. -/
example : Var[fun ω => thetaPi 2 (fun _ _ => (0 : ℝ)) ω -
      (∑ i ∈ Ico 1 2, (fun _ _ => (0 : ℝ)) i ω) / tajimaA1 2; piMeasure 2] =
    tajimaC1 2 * 0 + tajimaC2 2 * 0 ^ 2 :=
  variance_tajimaNumerator_kingman_of_fuSigma le_rfl measurable_K2 comap_tau2_le law_tau2
    indep_tau2 sfsCondMoments_K2 fuSigma_K2

end Kingman

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm
