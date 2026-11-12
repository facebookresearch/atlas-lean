/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
public import MathlibExt.Probability.Distributions.PoissonKernel
public import MathlibExt.Biology.PopulationGenetics.Coalescent.TajimaD
public import MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-!
# Tests for the covariances of the site frequency spectrum

Boundary values of the estimator weights (`n = 2`, where Tajima's `D` numerator vanishes, and
`n = 3`), a non-vacuity witness for `SFSCondMoments` with a genuinely random count (a Poisson
count given a trivial genealogy, whose variance `covariance_count` recovers), and a witness
that the Kingman hypotheses are jointly satisfiable (sample size `2`, the product model of the
holding times from the `SiteFrequencySpectrum` tests, `θ = 0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSCovariance

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
open MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance

/-! ### Weights -/

/-- `n = 2`: the only weight of Tajima's `D` numerator vanishes (`π = S` for two copies). -/
example : tajimaNumWeight 2 1 = 0 := by
  norm_num [tajimaNumWeight, tajimaA1]

/-- `n = 3`: the weights of Tajima's `D` numerator are `4/3 - 2/3 = 2/3`, both equal, so that
`θ_π - S / a₁` is again identically zero on the SFS (Tajima's `c₁ = c₂ = 0` at `n = 3`). -/
example : tajimaNumWeight 3 1 = 0 ∧ tajimaNumWeight 3 2 = 0 := by
  refine ⟨?_, ?_⟩ <;> norm_num [tajimaNumWeight, tajimaA1, Finset.sum_Ico_succ_top]

/-- `n = 4`: `b₁ = 5/9` from the SFS weights. -/
example : ∑ i ∈ (Ico 1 4 : Finset ℕ),
    ((((4 : ℕ) : ℝ) - (i : ℝ)) / ((4 : ℕ).choose 2 : ℝ)) ^ 2 * (i : ℝ) = 5 / 9 := by
  rw [sum_piWeight_sq_mul (by norm_num)]
  norm_num [tajimaB1]

/-- `n = 4`: the same sum computed directly, independently of `sum_piWeight_sq_mul`. -/
example : ∑ i ∈ (Ico 1 4 : Finset ℕ),
    ((((4 : ℕ) : ℝ) - (i : ℝ)) / ((4 : ℕ).choose 2 : ℝ)) ^ 2 * (i : ℝ) = 5 / 9 := by
  simp [Finset.sum_Ico_succ_top, Nat.choose]
  norm_num

/-- `n = 4`: the `θ`-linear coefficient of `Var(θ_π - S / a₁)` is Tajima's `c₁`, which is
positive. -/
example : 0 < ∑ i ∈ Ico 1 4, tajimaNumWeight 4 i ^ 2 / i := by
  rw [sum_tajimaNumWeight_sq_div (by norm_num)]
  exact tajimaC1_pos le_rfl

/-- `n = 4`: the same sum computed directly, `c₁ = 5/9 - 6/11 = 1/99`, independently of
`sum_tajimaNumWeight_sq_div`. -/
example : ∑ i ∈ Ico 1 4, tajimaNumWeight 4 i ^ 2 / i = 1 / 99 := by
  simp [Finset.sum_Ico_succ_top, tajimaNumWeight, tajimaA1, Nat.choose]
  norm_num

/-! ### A Poisson witness for `SFSCondMoments` -/

section Poisson

/-- A single class: `ξ 1` is a `Po(1)` count, every other class is empty. -/
noncomputable def xiPo (i : ℕ) (k : ℕ) : ℝ := if i = 1 then (k : ℝ) else 0

/-- The branch length of class `1` is `1`, the others are `0`. -/
noncomputable def lenPo (i : ℕ) (_ : ℕ) : ℝ := if i = 1 then 1 else 0

/-- The witness counts are square integrable. -/
lemma memLp_xiPo (i : ℕ) : MemLp (xiPo i) 2 (poissonMeasure (1 : ℝ≥0)) := by
  unfold xiPo
  split_ifs
  · exact (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2
      (integrable_natCast_sq_poissonMeasure 1)
  · exact memLp_const 0

/-- `SFSCondMoments` holds for the trivial genealogy `⊥`, `θ = 2`, and a `Po(1)` count. -/
lemma sfsCondMoments_po : SFSCondMoments (poissonMeasure (1 : ℝ≥0)) ⊥ 2 xiPo lenPo where
  memLp_count := memLp_xiPo
  memLp_length i := memLp_const _
  condExp_count i := by
    rw [condExp_bot]
    refine Filter.Eventually.of_forall fun _ => ?_
    unfold xiPo lenPo
    split_ifs
    · simpa using integral_natCast_poissonMeasure (1 : ℝ≥0)
    · simp
  condExp_count_mul i j := by
    rw [condExp_bot]
    refine Filter.Eventually.of_forall fun _ => ?_
    unfold xiPo lenPo
    by_cases hi : i = 1 <;> by_cases hj : j = 1
    · subst hi hj
      have := integral_natCast_sq_poissonMeasure (1 : ℝ≥0)
      simp only [sq] at this
      simp only [↓reduceIte, this]
      norm_num
    · subst hi
      simp [hj, Ne.symm hj]
    · subst hj
      simp [hi]
    · simp [hi, hj]

/-- `lenPo i` as a constant function. -/
lemma lenPo_eq (i : ℕ) : lenPo i = fun _ => if i = 1 then 1 else 0 := rfl

/-- **Non-vacuity with a random count**: `covariance_count` recovers `Var Po(1) = 1`. -/
example : cov[xiPo 1, xiPo 1; poissonMeasure (1 : ℝ≥0)] = 1 := by
  rw [sfsCondMoments_po.covariance_count bot_le, lenPo_eq, covariance_const_left]
  simp

/-- Distinct classes are uncorrelated when the branch lengths are deterministic. -/
example : cov[xiPo 1, xiPo 2; poissonMeasure (1 : ℝ≥0)] = 0 := by
  rw [sfsCondMoments_po.covariance_count bot_le, lenPo_eq, covariance_const_left]
  simp

end Poisson

/-! ### The Kingman hypotheses are jointly satisfiable -/

section Kingman

open MathlibExtTest.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-- With `θ = 0` and no segregating sites, the Kingman hypotheses (holding times from the
product model, the unique topology for `n = 2`) all hold. -/
lemma sfsCondMoments_K2 :
    SFSCondMoments (piMeasure 2) (MeasurableSpace.comap tau2 ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K2.T k ω) MeasurableSpace.pi) 0 (fun _ _ => 0)
      (fun i ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω)) :=
  sfsCondMoments_kingman comap_tau2_le law_tau2 (fun _ => memLp_const 0)
    (fun _ => by simp)
    (fun _ _ => by simp)

/-- `variance_watterson_kingman` instantiated on the witness (`0 = 0`). -/
example : Var[fun ω => (∑ i ∈ Ico 1 2, (fun _ _ => (0 : ℝ)) i ω) / tajimaA1 2; piMeasure 2] =
    0 / tajimaA1 2 + (0 / (2 * tajimaA1 2)) ^ 2 *
      Var[fun ω => ∑ i ∈ Ico 1 2, sfsLength 2 i (tau2 ω) (fun k => K2.T k ω); piMeasure 2] :=
  variance_watterson_kingman le_rfl measurable_K2 comap_tau2_le law_tau2 indep_tau2
    sfsCondMoments_K2

/-- Branch lengths of the witness are square integrable (`memLp_sfsLength`). -/
example (i : ℕ) : MemLp (fun ω => sfsLength 2 i (tau2 ω) (fun k => K2.T k ω)) 2 (piMeasure 2) :=
  memLp_sfsLength comap_tau2_le law_tau2 i

end Kingman

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.SFSCovariance
