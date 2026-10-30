/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Tajima

/-!
# Tests for the moments behind Tajima's D

Tajima's constants for `n = 2` (`a₁ = a₂ = b₁ = b₂ = 1`, `c₁ = c₂ = 0`) and `n = 3`, and the
junk value of `b₁` at `n = 1`;
`Var L = 4` and `Var S = θ + θ²` for a sample of two; `E S = θ` for a sample of two; and a
witness that the hypotheses of `integral_meanPairDiff` and `integral_tajimaNumerator` are
satisfiable: on the product model `KingmanTimes.ofPi 2`, the pair coalescence time is `T 2`
and the pairwise difference count `θ T 2` has the required conditional mean.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Tajima

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- `n = 2`: `a₁ = a₂ = b₁ = b₂ = 1`. -/
example : tajimaA1 2 = 1 ∧ tajimaA2 2 = 1 ∧ tajimaB1 2 = 1 ∧ tajimaB2 2 = 1 := by
  norm_num [tajimaA1, tajimaA2, tajimaB1, tajimaB2]

/-- `n = 2`: `c₁ = c₂ = 0`, so `e₁ = e₂ = 0` (Tajima's `D` is undefined for two sequences). -/
example : tajimaC1 2 = 0 ∧ tajimaC2 2 = 0 ∧ tajimaE1 2 = 0 ∧ tajimaE2 2 = 0 := by
  norm_num [tajimaC1, tajimaC2, tajimaE1, tajimaE2, tajimaA1, tajimaA2, tajimaB1, tajimaB2]

/-- Outside the domain `n ≥ 2`: `b₁ = (n + 1) / (3 (n - 1))` divides by zero at `n = 1`, and
the definition returns Lean's junk value `0`. -/
example : tajimaB1 1 = 0 := by
  norm_num [tajimaB1]

/-- `n = 3`: `a₁ = 3/2`, `a₂ = 5/4`. -/
example : tajimaA1 3 = 3 / 2 ∧ tajimaA2 3 = 5 / 4 := by
  norm_num [tajimaA1, tajimaA2, sum_Ico_succ_top]

/-- `n = 3`: `a₁ = H₂`. -/
example : tajimaA1 3 = (harmonic 2 : ℝ) := tajimaA1_eq_harmonic 3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A sample of two: `Var L = Var (2 T₂) = 4`. -/
example (K : KingmanTimes μ 2) : Var[K.totalLength; μ] = 4 := by
  rw [K.variance_totalLength]
  norm_num [tajimaA2]

/-- A sample of three: `Var L = 4 (1 + 1/4) = 5`. -/
example (K : KingmanTimes μ 3) : Var[K.totalLength; μ] = 5 := by
  rw [K.variance_totalLength]
  norm_num [tajimaA2, sum_Ico_succ_top]

/-- A sample of two: `Var S = θ + θ²`. -/
example [IsProbabilityMeasure μ] (K : KingmanTimes μ 2) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {S : Ω → ℝ} {θ : ℝ} (hS2 : MemLp S 2 μ)
    (hmean : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hvar : Var[S; μ | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    Var[S; μ] = θ + θ ^ 2 := by
  rw [K.variance_segSites hm hS2 hmean hvar]
  norm_num [tajimaA1, tajimaA2]

/-- A sample of two (`T₂ ~ Exp(1)`): `E S₂ = θ`. -/
example (K : KingmanTimes μ 2) {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {S : Ω → ℝ} {θ : ℝ} (hSi : Integrable S μ)
    (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    μ[S] = θ := by
  rw [K.integral_segSites hm hSi hS]
  norm_num [harmonic]

/-- Non-vacuity witness for the pairwise-difference hypotheses: on the product model for a
sample of two, take the pair coalescence time `τ = T 2 ~ Exp(1)` and the pairwise difference
count `D = θ τ`, with the full σ-algebra as genealogy; then `E π = θ`. -/
example (θ : ℝ) :
    (piMeasure 2)[meanPairDiff 2 fun _ ω => θ * (KingmanTimes.ofPi 2).T 2 ω] = θ := by
  have : IsProbabilityMeasure (piMeasure 2) := by
    unfold piMeasure
    infer_instance
  have hlaw : HasLaw ((KingmanTimes.ofPi 2).T 2) (expMeasure 1) (piMeasure 2) := by
    simpa using (KingmanTimes.ofPi 2).hasLaw 2 (by simp)
  have hint : Integrable (fun ω => θ * (KingmanTimes.ofPi 2).T 2 ω) (piMeasure 2) :=
    (hlaw.integrable_of_expMeasure one_pos).const_mul θ
  exact integral_meanPairDiff le_rfl (τ := fun _ => (KingmanTimes.ofPi 2).T 2) le_rfl
    (fun _ _ => hlaw) (fun _ _ => hint) fun _ _ =>
      condExp_of_aestronglyMeasurable' le_rfl
        (hlaw.aemeasurable.aestronglyMeasurable.const_mul θ) hint

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Tajima
