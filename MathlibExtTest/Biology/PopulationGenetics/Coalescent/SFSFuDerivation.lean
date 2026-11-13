/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuDerivation
public import MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm

/-!
# Tests for the derivation of Fu's branch-length covariances

* The moments `blockCountMean`, `blockCountMoment`, `kingmanTimeMoment` computed from the
  definitions, and `blockCountMean` checked against the merged closed form
  `joinStep_iterate_count`.
* Entries of `fuTopologyCov` computed from the definitions and compared with hand arithmetic on
  the genealogies (`n = 3`: `L₁ = 3 T₃ + T₂`, `L₂ = T₂`; `n = 4`: `L₃ = c T₂` with
  `c = 1` when the last two blocks are `[1, 3]`, probability `2/3`), and with `4 σ_{ij}`.
* The two-level Markov property carries total mass `1`.
* The Kingman witness of sample size `2`: the reduction gives `Var L₁ = 4`, the same value the
  merged test obtains from `KingmanTimes.variance_totalLength`, and every theorem of the file is
  instantiated on it with all hypotheses discharged.
* Boundary entries: `n = 1` (no holding times) and an index `i = n` outside `[1, n - 1]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuDerivation

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuDerivation
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSCovariance
open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm

/-! ### One step of random joining on the lists reached from `n ≤ 4` singletons -/

lemma step_singleton (g : List ℕ → ℝ) (a : ℕ) : joinStep g [a] = g [] := by
  simp [joinStep, blockPairs]

lemma step_pair (g : List ℕ → ℝ) (a b : ℕ) : joinStep g [a, b] = g [a + b] := by
  simp [joinStep, blockPairs_two, mergeBlocks]

lemma step_111 (g : List ℕ → ℝ) : joinStep g [1, 1, 1] = g [1, 2] := by
  simp [joinStep, blockPairs_three, mergeBlocks]
  ring

lemma step_112 (g : List ℕ → ℝ) : joinStep g [1, 1, 2] = (g [2, 2] + 2 * g [1, 3]) / 3 := by
  simp [joinStep, blockPairs_three, mergeBlocks]
  ring

lemma step_1111 (g : List ℕ → ℝ) : joinStep g [1, 1, 1, 1] = g [1, 1, 2] := by
  have : blockPairs 4 = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  simp [joinStep, this, mergeBlocks]
  ring

/-! ### Moments computed from the definitions -/

/-- `n = 4`, `k = 3`: the blocks are `[1, 1, 2]`, so `E[c_{3,1}] = 2`. -/
example : blockCountMean 4 3 1 = 2 := by
  norm_num [blockCountMean, step_1111]

/-- The same from the merged closed form `k C(n-i-1, k-2) / C(n-1, k-1) = 3 · 2 / 3`. -/
example : blockCountMean 4 3 1 = 2 := by
  rw [blockCountMean, joinStep_iterate_count (by norm_num) (by norm_num) le_rfl (by norm_num)]
  norm_num [Nat.choose]

/-- `n = 4`, `k = 2`: `[2, 2]` with probability `1/3`, `[1, 3]` with probability `2/3`, so
`E[c_{2,1}] = 2/3`. -/
example : blockCountMean 4 2 1 = 2 / 3 := by
  norm_num [blockCountMean, Function.iterate_succ_apply', step_1111, step_112]

/-- `n = 3`: `E[c_{3,1} c_{2,1}] = 3 · 1` (three singletons, then `[1, 2]`). -/
example : blockCountMoment 3 3 2 1 1 = 3 := by
  norm_num [blockCountMoment, joinPair, step_111]

/-- The moment does not depend on the order of the two levels: `E[c_{2,1} c_{3,1}] = 3`. -/
example : blockCountMoment 3 2 3 1 1 = 3 := by
  norm_num [blockCountMoment, joinPair, step_111]

/-- `n = 4`: `E[c_{2,1}²] = 2/3` (the indicator of `[1, 3]`). -/
example : blockCountMoment 4 2 2 1 1 = 2 / 3 := by
  norm_num [blockCountMoment, joinPair, Function.iterate_succ_apply', step_1111, step_112]

/-- `E[T₂²] = 2` and `E[T₂ T₃] = 1/3`. -/
example : kingmanTimeMoment 2 2 = 2 ∧ kingmanTimeMoment 2 3 = 1 / 3 := by
  norm_num [kingmanTimeMoment, Nat.choose]

/-! ### Entries of `fuTopologyCov` -/

/-- `n = 3`: `Var(3 T₃ + T₂) = 9 · (1/3)² + 1 = 2`, computed from the definitions. -/
example : fuTopologyCov 3 1 1 = 2 := by
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose, step_111, step_pair, show Icc 2 3 = {2, 3} by decide]

/-- `n = 3`: `Cov(3 T₃ + T₂, T₂) = Var T₂ = 1`. -/
example : fuTopologyCov 3 1 2 = 1 := by
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose, step_111, step_pair, show Icc 2 3 = {2, 3} by decide]

/-- `n = 4`, the case `i + j = n`: `Cov(L₁, L₃) = Var(c T₂) = (2/3) · 2 - (2/3)² = 8/9`. -/
example : fuTopologyCov 4 1 3 = 8 / 9 := by
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose, Function.iterate_succ_apply', step_1111, step_112, step_pair, step_singleton,
    show Icc 2 4 = {2, 3, 4} by decide]

/-- The hand values agree with Fu's matrix: `4 σ₁₁ = 2`, `4 σ₁₂ = 1` at `n = 3` and
`4 σ₁₃ = 8/9` at `n = 4`, through `fuTopologyCov_eq_four_mul_fuSigma_of_le_four`. -/
example : fuTopologyCov 3 1 1 = 4 * (1 / 2) ∧ fuTopologyCov 3 1 2 = 4 * (1 / 4) ∧
    fuTopologyCov 4 1 3 = 4 * (2 / 9) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fuTopologyCov_eq_four_mul_fuSigma_of_le_four (by norm_num) 1 (by simp) 1 (by simp)]
    norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]
  · rw [fuTopologyCov_eq_four_mul_fuSigma_of_le_four (by norm_num) 1 (by simp) 2 (by simp)]
    norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]
  · rw [fuTopologyCov_eq_four_mul_fuSigma_of_le_four (by norm_num) 1 (by simp) 3 (by simp)]
    norm_num [fuSigma, fuBeta, tajimaA1, sum_Ico_succ_top]

/-- Boundary `n = 1`: no holding times, so `fuTopologyCov 1 i j = 0`. -/
example (i j : ℕ) : fuTopologyCov 1 i j = 0 := by
  simp [fuTopologyCov]

/-- Boundary index `i = n = 3`: no branch subtends all three copies, so the entry is `0`. -/
example : fuTopologyCov 3 3 3 = 0 := by
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose, step_111, step_pair, show Icc 2 3 = {2, 3} by decide]

/-! ### The two-level Markov property -/

/-- The random-joining law from three singletons has total mass `1`, through
`exists_finset_randomJoining_pair` with constant statistics. -/
example : ∃ F : Finset (List (List ℕ)),
    ∑ ps ∈ F, randomJoining 2 [1, 1, 1] ps = 1 := by
  obtain ⟨F, -, hF⟩ := exists_finset_randomJoining_pair 2 [1, 1, 1]
  refine ⟨F, ?_⟩
  simpa [joinPair] using hF 0 0 le_rfl (Nat.zero_le _) (fun _ => 1) (fun _ => 1)

/-- The two-level expectation of `c_{3,1} c_{2,2}` from three singletons is `3 · 1`. -/
example : ∃ F : Finset (List (List ℕ)),
    ∑ ps ∈ F, randomJoining 2 [1, 1, 1] ps *
      (((ps.getD 0 []).count 1 : ℝ) * ((ps.getD 1 []).count 2 : ℝ)) = 3 := by
  obtain ⟨F, -, hF⟩ := exists_finset_randomJoining_pair 2 [1, 1, 1]
  refine ⟨F, ?_⟩
  rw [hF 0 1 (Nat.zero_le _) (by norm_num) (fun b => (b.count 1 : ℝ))
    (fun b => (b.count 2 : ℝ))]
  norm_num [joinPair, step_111]

/-! ### The Kingman witness of sample size `2` -/

section Kingman

/-- **The reduction is non-vacuous**: on the witness, `Var L₁ = fuTopologyCov 2 1 1 = 4`, with
`fuTopologyCov 2 1 1` computed from the definitions. -/
lemma covariance_K2_one :
    cov[fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω),
      fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 := by
  rw [covariance_sfsLength_eq_fuTopologyCov comap_tau2_le law_tau2 indep_tau2]
  norm_num [fuTopologyCov, blockCountMoment, blockCountMean, joinPair, kingmanTimeMoment,
    Nat.choose]

/-- The same value from the merged test, computed through `KingmanTimes.variance_totalLength`
and Fu's `σ₁₁ = 1`. -/
example : cov[fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω),
    fun ω => sfsLength 2 1 (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 := by
  rw [fuSigma_K2 1 (by simp) 1 (by simp)]
  norm_num [fuSigma, tajimaA1]

/-- `covariance_sfsLength_eq_four_mul_fuSigma_of_le_four` on the witness. -/
example : ∀ i ∈ Ico 1 2, ∀ j ∈ Ico 1 2,
    cov[fun ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω),
      fun ω => sfsLength 2 j (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 * fuSigma 2 i j :=
  covariance_sfsLength_eq_four_mul_fuSigma_of_le_four (by norm_num) comap_tau2_le law_tau2
    indep_tau2

/-- `covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov` on the witness, with the
topology identity supplied by `fuTopologyCov_eq_four_mul_fuSigma_of_le_four`. -/
example : ∀ i ∈ Ico 1 2, ∀ j ∈ Ico 1 2,
    cov[fun ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω),
      fun ω => sfsLength 2 j (tau2 ω) (fun k => K2.T k ω); piMeasure 2] = 4 * fuSigma 2 i j :=
  covariance_sfsLength_eq_four_mul_fuSigma_of_fuTopologyCov comap_tau2_le law_tau2 indep_tau2
    (fuTopologyCov_eq_four_mul_fuSigma_of_le_four (by norm_num))

/-- All hypotheses of `covariance_count_kingman_of_le_four` hold jointly on the witness. -/
example : cov[(fun _ _ => (0 : ℝ)) 1, (fun _ _ => (0 : ℝ)) 1; piMeasure 2] =
    (if 1 = 1 then 0 / ((1 : ℕ) : ℝ) else 0) + 0 ^ 2 * fuSigma 2 1 1 :=
  covariance_count_kingman_of_le_four (by norm_num) measurable_K2 comap_tau2_le law_tau2
    indep_tau2 sfsCondMoments_K2 (by simp) (by simp)

/-- `integral_T_mul_T` on the witness: `E[T₂²] = 2`. -/
example : (piMeasure 2)[K2.T 2 * K2.T 2] = 2 := by
  rw [integral_T_mul_T K2 (by simp) (by simp)]
  norm_num [kingmanTimeMoment, Nat.choose]

end Kingman

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSFuDerivation
