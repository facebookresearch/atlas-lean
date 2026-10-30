/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BackwardsMartingale

/-! Signed, nonzero, shrinking-filtration characterization and importing clients. -/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MathlibExtTest.Probability.BackwardsMartingaleCanonical

local instance : MeasurableSpace Bool := ⊤

private noncomputable def twoAtomMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)

local instance : IsProbabilityMeasure twoAtomMeasure :=
  ⟨by norm_num [twoAtomMeasure, ENNReal.inv_two_add_inv_two]⟩

private def signedInitial (b : Bool) : ℝ := if b then 3 else -1

private theorem signedInitial_stronglyMeasurable : StronglyMeasurable signedInitial := by
  apply Measurable.stronglyMeasurable
  intro s hs
  trivial

private theorem signedInitial_integrable (μ : Measure Bool) [IsFiniteMeasure μ] :
    Integrable signedInitial μ := by
  refine (integrable_const (3 : ℝ)).mono'
    signedInitial_stronglyMeasurable.aestronglyMeasurable ?_
  exact ae_of_all μ fun b => by cases b <;> norm_num [signedInitial]

private theorem signedInitial_integral : ∫ b, signedInitial b ∂twoAtomMeasure = 1 := by
  rw [twoAtomMeasure, integral_smul_measure,
    integral_add_measure (signedInitial_integrable _) (signedInitial_integrable _),
    integral_dirac, integral_dirac]
  norm_num [signedInitial]

private def shrinkingFiltration : Filtration ℕᵒᵈ (⊤ : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊤ else ⊥
  mono' := by
    intro i j hij
    change Nat.le j i at hij
    change (if i = 0 then ⊤ else ⊥) ≤ (if j = 0 then ⊤ else ⊥)
    by_cases hi : i = 0
    · subst i
      have hj : j = 0 := Nat.le_zero.mp hij
      simp [hj]
    · simp [hi]
  le' _ := le_top

private theorem conditional_zero :
    twoAtomMeasure[signedInitial | shrinkingFiltration 0] = signedInitial := by
  change twoAtomMeasure[signedInitial | ⊤] = signedInitial
  exact condExp_of_stronglyMeasurable le_rfl signedInitial_stronglyMeasurable
    (signedInitial_integrable _)

private theorem conditional_one :
    twoAtomMeasure[signedInitial | shrinkingFiltration 1] = fun _ => 1 := by
  change twoAtomMeasure[signedInitial | ⊥] = fun _ => 1
  rw [condExp_bot, signedInitial_integral]

private theorem process_changes :
    (twoAtomMeasure[signedInitial | shrinkingFiltration 0]) false ≠
      (twoAtomMeasure[signedInitial | shrinkingFiltration 1]) false := by
  rw [conditional_zero, conditional_one]
  norm_num [signedInitial]

private theorem filtration_changes : shrinkingFiltration 0 ≠ shrinkingFiltration 1 := by
  intro h
  exact process_changes (congrArg
    (fun m : MeasurableSpace Bool => (twoAtomMeasure[signedInitial | m]) false) h)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Every term is integrable without a finite-measure or adaptedness premise. -/
theorem canonical_integrable_client {M : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}
    (hM : MeasureTheory.IsBackwardsMartingale M m μ) (n : ℕ) : Integrable (M n) μ :=
  hM.integrable n

/-- The analytic APIs need canonical membership, order and ambient bounds. -/
theorem canonical_analytic_clients [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}
    (hM : MeasureTheory.IsBackwardsMartingale M m μ) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) (n : ℕ) :
    Integrable (M n) μ ∧ UniformIntegrable M 1 μ ∧
      μ[M n | m (n + 1)] =ᵐ[μ] M (n + 1) :=
  ⟨hM.integrable n, hM.uniformIntegrable hm0, hM.condExp_succ_ae_eq hm hm0 n⟩

/-- Arbitrary-g construction preserves separate representative adaptedness. -/
theorem canonical_constructor_client [IsFiniteMeasure μ] (g : Ω → ℝ)
    (ℱ : Filtration ℕᵒᵈ m0) :
    MeasureTheory.IsBackwardsMartingale (fun n => μ[g | ℱ n]) ℱ.seq μ ∧
      StronglyAdapted ℱ (fun n => μ[g | ℱ n]) := by
  refine ⟨MeasureTheory.isBackwardsMartingale_condExp (μ := μ) g ℱ.seq ?_ ℱ.le',
    ℱ.stronglyAdapted_condExp g μ⟩
  intro i j hij
  exact ℱ.mono' hij

/-- The constructor and recurrence include the first n=0 step. -/
theorem canonical_zero_recurrence_client [IsFiniteMeasure μ] (g : Ω → ℝ)
    (ℱ : Filtration ℕᵒᵈ m0) : μ[μ[g | ℱ 0] | ℱ 1] =ᵐ[μ] μ[g | ℱ 1] := by
  have hm : Antitone (fun n : ℕ => ℱ n) := by
    intro i j hij
    exact ℱ.mono' hij
  have hM := MeasureTheory.isBackwardsMartingale_condExp (μ := μ)
    g (fun n : ℕ => ℱ n) hm ℱ.le'
  exact hM.condExp_succ_ae_eq hm ℱ.le' 0

/-- The same canonical witness feeds both existing convergence APIs. -/
theorem canonical_same_witness_convergence_client [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (ℱ : Filtration ℕᵒᵈ m0) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (μ[g | ℱ n]) ω) atTop
      (𝓝 ((μ[μ[g | ℱ 0] | ℱ.tailAlgebra]) ω))) ∧
      Tendsto (fun n : ℕ => eLpNorm (μ[g | ℱ n] - μ[μ[g | ℱ 0] | ℱ.tailAlgebra]) 1 μ)
        atTop (𝓝 0) := by
  have hm : Antitone (fun n : ℕ => ℱ n) := by
    intro i j hij
    exact ℱ.mono' hij
  have hM := MeasureTheory.isBackwardsMartingale_condExp (μ := μ)
    g (fun n : ℕ => ℱ n) hm ℱ.le'
  exact ⟨backwards_martingale_ae_tendsto (fun n : ℕ => ℱ n) hm ℱ.le' hM,
    backwards_martingale_tendsto_eLpNorm_one (fun n : ℕ => ℱ n) hm ℱ.le' hM⟩

/-- Tail and constant data use the canonical dual filtration. -/
theorem canonical_tail_client (ℱ : Filtration ℕᵒᵈ m0) (n : ℕᵒᵈ)
    (m : MeasurableSpace Ω) (hm : m ≤ m0) :
    ℱ.tailAlgebra ≤ m0 ∧ ℱ.tailAlgebra ≤ ℱ n ∧
      (Filtration.const ℕᵒᵈ m hm).tailAlgebra = m :=
  ⟨ℱ.tailAlgebra_le, ℱ.tailAlgebra_le_seq n, Filtration.tailAlgebra_const m hm⟩

/-- The signed shrinking example reaches the actual bottom tail algebra. -/
private theorem signed_tail_client : shrinkingFiltration.tailAlgebra = ⊥ := by
  apply le_antisymm ?_ bot_le
  simpa [shrinkingFiltration] using shrinkingFiltration.tailAlgebra_le_seq 1

end MathlibExtTest.Probability.BackwardsMartingaleCanonical
