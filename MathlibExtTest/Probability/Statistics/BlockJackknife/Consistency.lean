/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.BlockJackknife.Consistency
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for block-jackknife consistency

The examples check the smallest nondegenerate sample, the zero-variance boundary, and
that the hypotheses are satisfiable by a coordinate process on an iid product space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Matrix Filter
open scoped Topology


namespace MathlibExtTest.Probability.Statistics.BlockJackknife.Consistency

open MathlibExt.Probability.Statistics.BlockJackknife

variable {n : Type*} [Fintype n] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

-- smallest nondegenerate case: one coordinate, two blocks, `2 V_jack = (x - y)² / 2`
example (x y : ℝ) :
    (((2 : ℕ) : ℝ) • jackCov (fun b : Fin 2 => (![![x], ![y]] b : Fin 1 → ℝ))) 0 0 =
      (x - y) ^ 2 / 2 := by
  rw [card_smul_jackCov_apply le_rfl]
  simp [mean, Fin.sum_univ_two]
  ring

-- zero variance / rank zero: constant blocks give `B V_jack = 0` for every `B ≥ 2`
omit [Fintype n] in
example (c : n → ℝ) {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) • jackCov (fun _ : Fin B => c) = 0 := by
  ext i j
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hB' : (B : ℝ) ≠ 0 := by linarith
  have hm : mean (fun _ : Fin B => c) = c := by
    ext k
    simp only [mean, Pi.smul_apply, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, smul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    field_simp
  rw [card_smul_jackCov_apply hB, hm]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.zero_apply]
  rw [← mul_assoc, inv_mul_cancel₀ hB', one_mul, sub_self, mul_zero]

-- and the limit is the zero covariance (constant coordinates)
example (c : n → ℝ) (i j : n) : cov[fun _ : Ω => c i, fun _ : Ω => c j; μ] = 0 := by
  simp [covariance]

-- non-vacuity: for any law `ν` on `n → ℝ` with square-integrable coordinates, the coordinate
-- process of the iid product `infinitePi ν` satisfies every hypothesis
example (ν : Measure (n → ℝ)) [IsProbabilityMeasure ν]
    (h2 : ∀ i, MemLp (fun v : n → ℝ => v i) 2 ν) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∀ i j,
      Tendsto (fun B : ℕ => ((B : ℝ) • jackCov (fun b : Fin B => ω b)) i j) atTop
        (𝓝 (cov[fun ω : ℕ → n → ℝ => ω 0 i, fun ω => ω 0 j; Measure.infinitePi fun _ => ν])) := by
  have hmp : ∀ b, MeasurePreserving (fun ω : ℕ → n → ℝ => ω b)
      (Measure.infinitePi fun _ : ℕ => ν) ν := fun b =>
    ⟨measurable_pi_apply b, Measure.infinitePi_map_eval _ b⟩
  have hind : iIndepFun (fun (b : ℕ) (ω : ℕ → n → ℝ) => ω b) (Measure.infinitePi fun _ : ℕ => ν) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ v => v) fun _ => measurable_id
  have hid : ∀ b, IdentDistrib (fun ω : ℕ → n → ℝ => ω b) (fun ω => ω 0)
      (Measure.infinitePi fun _ : ℕ => ν) (Measure.infinitePi fun _ : ℕ => ν) := fun b =>
    { aemeasurable_fst := (hmp b).measurable.aemeasurable
      aemeasurable_snd := (hmp 0).measurable.aemeasurable
      map_eq := by rw [(hmp b).map_eq, (hmp 0).map_eq] }
  have hL : ∀ i, MemLp (fun ω : ℕ → n → ℝ => ω 0 i) 2 (Measure.infinitePi fun _ : ℕ => ν) :=
    fun i => (h2 i).comp_measurePreserving (hmp 0)
  have key := ae_tendsto_card_smul_jackCov_apply hind hid hL
  refine key.mono fun ω h i j => ?_
  have h' := h i j
  exact h'

#print axioms MathlibExt.Probability.Statistics.BlockJackknife.card_smul_jackCov_apply
#print axioms MathlibExt.Probability.Statistics.BlockJackknife.ae_tendsto_card_smul_jackCov_apply
#print axioms MathlibExt.Probability.Statistics.BlockJackknife.ae_tendsto_card_smul_jackCov

end MathlibExtTest.Probability.Statistics.BlockJackknife.Consistency
