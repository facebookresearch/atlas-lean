/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Kingman

/-!
# Tests for Kingman's coalescent

Small-sample instances of the expected TMRCA (`1` for `n = 2`, `4/3` for `n = 3`), the
expected total branch length (`2`, `3`), the TMRCA variance, Watterson's identity, the
concrete product model `KingmanTimes.ofPi`, and small values and limits of the Wright–Fisher
no-coalescence probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Kingman

open MathlibExt.Biology.PopulationGenetics.Coalescent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Two lineages: `E[T_MRCA] = 1`. -/
example (K : KingmanTimes μ 2) : μ[K.tmrca] = 1 := by
  rw [K.integral_tmrca (by norm_num)]
  norm_num

/-- Three lineages: `E[T_MRCA] = 4/3`. -/
example (K : KingmanTimes μ 3) : μ[K.tmrca] = 4 / 3 := by
  rw [K.integral_tmrca (by norm_num)]
  norm_num

/-- One lineage: the TMRCA is `0`. -/
example (K : KingmanTimes μ 1) : μ[K.tmrca] = 0 := by
  rw [K.integral_tmrca le_rfl]
  norm_num

/-- Two lineages: `E[L] = 2`. -/
example (K : KingmanTimes μ 2) : μ[K.totalLength] = 2 := by
  rw [K.integral_totalLength]
  norm_num [harmonic]

/-- Three lineages: `E[L] = 2 (1 + 1/2) = 3`. -/
example (K : KingmanTimes μ 3) : μ[K.totalLength] = 3 := by
  rw [K.integral_totalLength]
  norm_num [harmonic, Finset.sum_range_succ]

/-- Empty sample: the total length is `0`. -/
example (K : KingmanTimes μ 0) : μ[K.totalLength] = 0 := by
  rw [K.integral_totalLength]
  norm_num [harmonic]

/-- Three lineages: `Var[T_MRCA] = 1 + 1/9`. -/
example (K : KingmanTimes μ 3) : Var[K.tmrca; μ] = 10 / 9 := by
  rw [K.variance_tmrca, show Finset.Icc 2 3 = {2, 3} from rfl, Finset.sum_pair (by norm_num)]
  norm_num [Nat.choose]

/-- Watterson's identity for `n = 3`: `E S = θ (1 + 1/2)`. -/
example (K : KingmanTimes μ 3) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {S : Ω → ℝ} {θ : ℝ}
    (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    μ[S] = 3 / 2 * θ := by
  rw [K.integral_segSites hm hS]
  norm_num [harmonic, Finset.sum_range_succ]
  ring

/-- Watterson's estimator for `n = 2` is `S` itself and is unbiased. -/
example (K : KingmanTimes μ 2) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {S : Ω → ℝ} {θ : ℝ}
    (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    μ[fun ω => S ω / (harmonic 1 : ℝ)] = θ :=
  K.watterson_unbiased hm hS le_rfl

/-- The concrete product model has `E[T_MRCA] = 4/3` for `n = 3`. -/
example : (piMeasure 3)[(KingmanTimes.ofPi 3).tmrca] = 4 / 3 := by
  rw [(KingmanTimes.ofPi 3).integral_tmrca (by norm_num)]
  norm_num

/-- The concrete product model is a probability space. -/
example : IsProbabilityMeasure (piMeasure 3) := by
  unfold piMeasure
  infer_instance

/-- No lineages or one lineage: no coalescence is certain. -/
example (M : ℕ) : noCoalProb M 0 = 1 ∧ noCoalProb M 1 = 1 := by
  simp [noCoalProb]

/-- Two lineages among two gene copies pick distinct parents with probability `1/2`. -/
example : noCoalProb 2 2 = 1 / 2 := by
  norm_num [noCoalProb, Finset.prod_range_succ]

/-- Three lineages among four gene copies: `1 · 3/4 · 1/2 = 3/8 = 4·3·2/4³`. -/
example : noCoalProb 4 3 = 3 / 8 := by
  norm_num [noCoalProb, Finset.prod_range_succ]

/-- The falling-factorial form agrees: `4·3·2 / 4³ = 3/8`. -/
example : noCoalProb 4 3 = 3 / 8 := by
  rw [noCoalProb_eq_descFactorial_div (by norm_num)]
  norm_num [Nat.descFactorial]

/-- More lineages than gene copies must coalesce. -/
example : noCoalProb 2 3 = 0 := by
  norm_num [noCoalProb, Finset.prod_range_succ]

/-- Two lineages coalesce at rate `1`. -/
example : Tendsto (fun M : ℕ => (M : ℝ) * (1 - noCoalProb M 2)) atTop (𝓝 1) := by
  simpa using tendsto_coalescence_rate 2

/-- Three lineages coalesce at rate `3`. -/
example : Tendsto (fun M : ℕ => (M : ℝ) * (1 - noCoalProb M 3)) atTop (𝓝 3) := by
  simpa [Nat.choose] using tendsto_coalescence_rate 3

/-- Survival of two lineages for one coalescent time unit: `exp (-1)`. -/
example : Tendsto (fun M : ℕ => noCoalProb M 2 ^ ⌊(1 : ℝ) * M⌋₊) atTop
    (𝓝 (Real.exp (-1))) := by
  simpa using tendsto_noCoalProb_pow_floor 2 zero_le_one

/-- Survival of three lineages for two coalescent time units: `exp (-6)`. -/
example : Tendsto (fun M : ℕ => noCoalProb M 3 ^ ⌊(2 : ℝ) * M⌋₊) atTop
    (𝓝 (Real.exp (-6))) := by
  convert tendsto_noCoalProb_pow_floor 3 zero_le_two using 3
  norm_num [Nat.choose]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Kingman
