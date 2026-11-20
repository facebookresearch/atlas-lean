/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuCovariance
public import MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuDerivation

/-!
# Tests for Fu's branch-length covariances for every sample size

* Clade weights, and the clade identity on the block list `[1, 1, 2]`: both sides computed from
  the definitions (`joinStep` and the sub-multisets), each equal to `4/3`.
* Small sample (`n ≤ 4`): the level moment `levelMoment 3 3 1 1 = 6` from the definitions of
  `joinPair` and from `levelMoment_closed`, and `fuTopologyCov 4 1 3 = 8/9` from the definitions
  against `4 σ₁₃` through the general theorem.
* General `n`: `hσ` and Fu's SFS covariance applied for an arbitrary sample size; the entry
  `fuTopologyCov 5 4 4 = 3/4` computed from the definitions (`Var(c T₂)`, `P(c = 1) = 1/2`) and
  compared with `4 σ₄₄` from the general theorem; and the Kingman witness of sample size `2`
  with every hypothesis discharged.
* Without the `KingmanTimes` hypotheses the conclusion is not claimed: deterministic holding
  times `T₂ = 1` give `Var L₁ = 0 ≠ 4 = 4 σ₁₁`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuCovariance

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuDerivation
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuCovariance
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSCovariance
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuDerivation

/-! ### Clade weights and the clade identity -/

/-- `2 / (m C(3, m))`: `2/3` for one of three blocks, `1/3` for two, `0` for all three. -/
example : cladeWeight 3 1 = 2 / 3 ∧ cladeWeight 3 2 = 1 / 3 ∧ cladeWeight 3 3 = 0 ∧
    cladeWeight 3 0 = 0 := by
  norm_num [cladeWeight, Nat.choose]

/-- Left side of the clade identity on `[1, 1, 2]`, from the definitions: two singletons while
three blocks remain (weight `C(3,2)⁻¹ = 1/3`), then `[1, 3]` with probability `2/3` (weight `1`). -/
lemma clade_lhs_112 :
    ∑ l ∈ Icc 2 3, ((l.choose 2 : ℕ) : ℝ)⁻¹ *
      (joinStep^[3 - l] fun y => (y.map (sizeInd 1)).sum) [1, 1, 2] = 4 / 3 := by
  norm_num [show Icc 2 3 = {2, 3} by decide, step_112, sizeInd, Nat.choose]

/-- Right side on `[1, 1, 2]`, from the definition of `cladeStat`: the two singletons `{1}`
carry weight `2/3` each; no other sub-multiset sums to `1`. -/
lemma clade_rhs_112 : cladeStat 3 (sizeInd 1) ([1, 1, 2] : Multiset ℕ) = 4 / 3 := by
  norm_num [cladeStat, cladeWeight, sizeInd, Multiset.powerset_coe, List.sublists',
    Nat.choose]

/-- The clade identity on `[1, 1, 2]` agrees with both hand computations. -/
example : ∑ l ∈ Icc 2 3, ((l.choose 2 : ℕ) : ℝ)⁻¹ *
      (joinStep^[3 - l] fun y => (y.map (sizeInd 1)).sum) [1, 1, 2] =
    cladeStat 3 (sizeInd 1) ([1, 1, 2] : Multiset ℕ) :=
  sum_inv_choose_two_mul_joinStep_iterate (sizeInd 1) 3 [1, 1, 2] rfl

/-! ### Small samples, from the definitions -/

/-- `n = 3`, `k = 3`, `i = j = 1`: `C(2,2)⁻¹ E[c_{3,1} c_{2,1}] + C(3,2)⁻¹ E[c_{3,1}²]
= 3 · 1 + 9 / 3 = 6`, computed from `joinPair`. -/
lemma levelMoment_331 : levelMoment 3 3 1 1 = 6 := by
  norm_num [levelMoment, joinPair, step_111, show Icc 2 3 = {2, 3} by decide, Nat.choose]

/-- The same value from the closed form `levelMoment_closed` (`coefA = 3`, the other
coefficients vanish or multiply `0`). -/
example : levelMoment 3 3 1 1 = 6 := by
  have h := levelMoment_closed (n := 3) (k := 3) (i := 1) (j := 1) (by norm_num) le_rfl le_rfl
    le_rfl (by norm_num)
  norm_num [coefA, coefB, coefC, coefD, Nat.choose] at h
  linarith

/-- `n = 4`, `i + j = n`: `fuTopologyCov 4 1 3 = 8/9` from the definitions (T155's hand value
`Var(c T₂)`, `P(c = 1) = 2/3`) equals `4 σ₁₃` through the general theorem. -/
example : fuTopologyCov 4 1 3 = 8 / 9 ∧ fuTopologyCov 4 1 3 = 4 * fuSigma 4 1 3 := by
  refine ⟨?_, fuTopologyCov_eq_four_mul_fuSigma 4 1 (by simp) 3 (by simp)⟩
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose, Function.iterate_succ_apply', step_1111, step_112, step_pair, step_singleton,
    show Icc 2 4 = {2, 3, 4} by decide]

/-- The general theorem reproduces T155's small-sample theorem at `n = 4`. -/
example : ∀ i ∈ Ico 1 4, ∀ j ∈ Ico 1 4, fuTopologyCov 4 i j = 4 * fuSigma 4 i j :=
  fuTopologyCov_eq_four_mul_fuSigma 4

/-! ### General sample size -/

/-! ### One step of random joining on the lists reached from five singletons -/

lemma step_11111 (g : List ℕ → ℝ) : joinStep g [1, 1, 1, 1, 1] = g [1, 1, 1, 2] := by
  have : blockPairs 5 = {(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4),
      (3, 4)} := by decide
  simp [joinStep, this, mergeBlocks]
  ring

lemma step_1112 (g : List ℕ → ℝ) :
    joinStep g [1, 1, 1, 2] = (g [1, 2, 2] + g [1, 1, 3]) / 2 := by
  have : blockPairs 4 = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  simp [joinStep, this, mergeBlocks]
  ring

lemma step_122 (g : List ℕ → ℝ) : joinStep g [1, 2, 2] = (2 * g [2, 3] + g [1, 4]) / 3 := by
  simp [joinStep, blockPairs_three, mergeBlocks]
  ring

lemma step_113 (g : List ℕ → ℝ) : joinStep g [1, 1, 3] = (g [3, 2] + 2 * g [1, 4]) / 3 := by
  simp [joinStep, blockPairs_three, mergeBlocks]
  ring

/-- `n = 5`, `i = j = 4`, from the definitions: `L₄ = c T₂` with `c = 1` exactly when the last
two blocks are `[1, 4]` (probability `1/2`), so `Var L₄ = (1/2) · 2 - (1/2)² = 3/4`. -/
lemma fuTopologyCov_544 : fuTopologyCov 5 4 4 = 3 / 4 := by
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose, Function.iterate_succ_apply', step_11111, step_1112, step_122, step_113,
    step_pair, step_singleton, show Icc 2 5 = {2, 3, 4, 5} by decide]

/-- The general theorem at `n = 5` agrees: `4 σ₄₄ = 4 (β₅(4) - 1/16) = 4 (1/4 - 1/16) = 3/4`,
with `σ₄₄` evaluated from the definition of `fuSigma`. -/
example : fuTopologyCov 5 4 4 = 4 * fuSigma 5 4 4 ∧ 4 * fuSigma 5 4 4 = 3 / 4 := by
  refine ⟨fuTopologyCov_eq_four_mul_fuSigma 5 4 (by simp) 4 (by simp), ?_⟩
  norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : KingmanTimes μ n} {τ : Ω → List (List ℕ)}

/-- `hσ` for an arbitrary sample size `n`, in the exact form T114's theorems take it. -/
example (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ) :
    ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j :=
  covariance_sfsLength_eq_four_mul_fuSigma hτ hτ_law h_indep

/-- `hσ` applied to T114's `variance_sum_sfsLength_one_of_fuSigma`: the variance of the total
branch length is `4 a₂` for every `n`. -/
example (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ) :
    Var[fun ω => ∑ i ∈ Ico 1 n, sfsLength n i (τ ω) (fun k => K.T k ω); μ] = 4 * tajimaA2 n :=
  variance_sum_sfsLength_one_of_fuSigma hτ hτ_law
    (covariance_sfsLength_eq_four_mul_fuSigma hτ hτ_law h_indep)

/-- `hσ` applied to T114's `variance_tajimaNumerator_kingman_of_fuSigma` for every `n ≥ 2`. -/
example (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k)) (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} {ξ : ℕ → Ω → ℝ}
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω))) :
    Var[fun ω => VariableSFS.thetaPi n ξ ω - (∑ i ∈ Ico 1 n, ξ i ω) / tajimaA1 n; μ] =
      tajimaC1 n * θ + tajimaC2 n * θ ^ 2 :=
  variance_tajimaNumerator_kingman_of_fuSigma hn hT hτ hτ_law h_indep h
    (covariance_sfsLength_eq_four_mul_fuSigma hτ hτ_law h_indep)

end General

/-! ### The Kingman witness of sample size `2` -/

/-- `hσ` on the witness, all hypotheses discharged. -/
example : ∀ i ∈ Ico 1 2, ∀ j ∈ Ico 1 2,
    cov[fun ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω),
      fun ω => sfsLength 2 j (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 * fuSigma 2 i j :=
  covariance_sfsLength_eq_four_mul_fuSigma comap_tau2_le law_tau2 indep_tau2

/-- On the witness, `hσ` gives `Var L₁ = 4`, the value T155's test computes from the
definitions (`covariance_K2_one`). -/
example : cov[fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω),
    fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 := by
  rw [covariance_sfsLength_eq_four_mul_fuSigma comap_tau2_le law_tau2 indep_tau2 1 (by simp) 1
    (by simp)]
  norm_num [fuSigma, tajimaA1]

/-- Fu's SFS covariance on the witness, every hypothesis discharged. -/
example : cov[(fun _ _ => (0 : ℝ)) 1, (fun _ _ => (0 : ℝ)) 1; piMeasure 2] =
    (if 1 = 1 then 0 / ((1 : ℕ) : ℝ) else 0) + 0 ^ 2 * fuSigma 2 1 1 :=
  covariance_count_kingman_eq_fuSigma measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2 (by simp) (by simp)

/-- The variance of a linear SFS statistic on the witness. -/
example : Var[fun _ => ∑ _i ∈ Ico 1 2, (1 : ℝ) * 0; piMeasure 2] =
    0 * ∑ i ∈ Ico (1 : ℕ) 2, (1 : ℝ) ^ 2 / i +
      0 ^ 2 * ∑ i ∈ Ico 1 2, ∑ j ∈ Ico 1 2, (1 : ℝ) * 1 * fuSigma 2 i j :=
  variance_sum_kingman_eq_fuSigma measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2 (fun _ => 1)

/-! ### Without the `KingmanTimes` hypotheses -/

/-- With the same topology but deterministic holding times `T₂ = 1` (not `Exp(1)`, so not
`KingmanTimes`), `L₁ = 2` is constant and `Var L₁ = 0`, while `4 σ₁₁ = 4`: `hσ` is not claimed
without the Kingman hypotheses. Both sides are computed from the definitions. -/
example : cov[fun _ : Unit => sfsLength 2 1 [[1, 1], [2]] (fun _ => 1),
    fun _ : Unit => sfsLength 2 1 [[1, 1], [2]] (fun _ => 1); Measure.dirac ()] ≠
      4 * fuSigma 2 1 1 := by
  rw [covariance_const_left]
  norm_num [fuSigma, tajimaA1]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuCovariance
