/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FullConformal
public import MathlibExt.Probability.Distributions.BetaBinomialSampleRank
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.SplitConformal
  MathlibExt.Probability.Statistics.SplitConformalExactCoverage
  MathlibExt.Probability.Statistics.FullConformal
  MathlibExt.Probability.Distributions.BetaBinomialSampleRank

namespace MathlibExtTest.Probability.Statistics.FullConformal

/-- The uniform law on `[0, 1]`, an atomless probability measure, for non-vacuity checks. -/
noncomputable abbrev unifIcc : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unifIcc := ⟨by simp [unifIcc]⟩

/-! ### Residuals of a symmetric algorithm -/

/-- The sample-mean predictor (the constant fit `x ↦ mean of the responses`) is symmetric, so its
absolute residuals are permutation equivariant. -/
example (n : ℕ) :
    IsPermEquivariant (absResidualScore (𝒳 := ℝ) (n := n)
      (fun z _ => (∑ i, (z i).2) / (n + 1))) :=
  isPermEquivariant_absResidualScore fun σ z => by
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp σ (fun i => (z i).2)]

/-- The full conformal set of the zero predictor at `n = 1`, `k = 1`, with one data point of
response `2`: the trial response `y` is kept iff `|y| ≤ 2`. -/
example (x : Unit) (y : ℝ) :
    y ∈ fullConformalSet (absResidualScore (n := 1) fun _ _ => 0) 1 ![((), 2)] x ↔ |y| ≤ 2 := by
  have h : (1 : ℕ) ≤ 1 := le_rfl
  simp only [fullConformalSet, Set.mem_ofPred_eq]
  rw [coe_le_splitConformalThreshold_iff h, strictLowerCount]
  simp [absResidualScore, Fin.snoc]

/-! ### The hypotheses are jointly satisfiable, with no ties -/

/-- Unit covariates and i.i.d. uniform responses. -/
noncomputable abbrev embed (n : ℕ) (ω : Fin (n + 1) → ℝ) : Fin (n + 1) → Unit × ℝ :=
  fun i => ((), ω i)

theorem measurable_embed (n : ℕ) : Measurable (embed n) :=
  Measurable.of_eval fun i => measurable_const.prodMk (measurable_pi_apply i)

/-- The data law: i.i.d. uniform responses with a constant covariate. -/
noncomputable abbrev dataLaw (n : ℕ) : Measure (Fin (n + 1) → Unit × ℝ) :=
  (Measure.pi fun _ : Fin (n + 1) => unifIcc).map (embed n)

theorem dataLaw_exchangeable (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (dataLaw n).map (fun z => z ∘ σ) = dataLaw n := by
  have hσZ : Measurable (fun z : Fin (n + 1) → Unit × ℝ => z ∘ σ) :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  have hσR : Measurable (fun ω : Fin (n + 1) → ℝ => ω ∘ σ) :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  rw [Measure.map_map hσZ (measurable_embed n)]
  have : (fun z : Fin (n + 1) → Unit × ℝ => z ∘ σ) ∘ embed n =
      embed n ∘ fun ω => ω ∘ σ := rfl
  rw [this, ← Measure.map_map (measurable_embed n) hσR, map_comp_perm_pi unifIcc σ]

/-- The response score `S z i = Y_i` (the zero predictor, responses in `[0, 1]`). -/
abbrev respScore (n : ℕ) (z : Fin (n + 1) → Unit × ℝ) : Fin (n + 1) → ℝ := fun i => (z i).2

theorem measurable_respScore (n : ℕ) : Measurable (respScore n) :=
  Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i)

theorem ae_injective_respScore (n : ℕ) :
    ∀ᵐ z ∂dataLaw n, Function.Injective (respScore n z) := by
  exact (ae_map_iff (p := fun z => respScore n z ∈ {ω | Function.Injective ω})
    (measurable_embed n).aemeasurable
    (measurableSet_setOf_injective.preimage (measurable_respScore n))).2
    (ae_injective_pi unifIcc)

/-- Full conformal coverage at `n = 9`, `α = 1/2` lies in `[1/2, 1/2 + 1/10]`. -/
example :
    ENNReal.ofReal (1 - 1 / 2) ≤
        dataLaw 9 {z | (z (Fin.last 9)).2 ∈ fullConformalSet (respScore 9)
          ⌈(1 - (1 / 2 : ℝ)) * ((9 : ℕ) + 1)⌉₊ (Fin.init z) (z (Fin.last 9)).1} ∧
      dataLaw 9 {z | (z (Fin.last 9)).2 ∈ fullConformalSet (respScore 9)
          ⌈(1 - (1 / 2 : ℝ)) * ((9 : ℕ) + 1)⌉₊ (Fin.init z) (z (Fin.last 9)).1} ≤
        ENNReal.ofReal (1 - 1 / 2 + 1 / ((9 : ℕ) + 1)) :=
  ⟨ofReal_one_sub_le_measure_mem_fullConformalSet _ (dataLaw_exchangeable 9)
      (fun _ _ => rfl) (measurable_respScore 9) (by norm_num) (by norm_num),
    measure_mem_fullConformalSet_le _ (dataLaw_exchangeable 9) (fun _ _ => rfl)
      (measurable_respScore 9) (ae_injective_respScore 9) (by norm_num) (by norm_num)⟩

end MathlibExtTest.Probability.Statistics.FullConformal
