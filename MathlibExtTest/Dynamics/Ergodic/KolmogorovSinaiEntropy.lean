/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy

namespace MathlibExtTest.Dynamics.Ergodic.KolmogorovSinaiEntropy

/-- The trivial partition `{α}` is a measurable partition. -/
theorem isMeasurablePartition_univ {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    IsMeasurablePartition μ (fun _ : Fin 1 => (Set.univ : Set α)) where
  measurableSet _ := MeasurableSet.univ
  aedisjoint i j hij := absurd (Subsingleton.elim i j) hij
  measure_compl_iUnion := by rw [Set.iUnion_const, Set.compl_univ, measure_empty]

/-- The trivial partition of a probability space has entropy `0`. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    partitionEntropy μ (fun _ : Fin 1 => (Set.univ : Set α)) = 0 := by
  simp [partitionEntropy]

-- Relative entropy of the trivial partition is bounded by the Kolmogorov–Sinai entropy.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (T : α → α) :
    entropyRel μ T (fun _ : Fin 1 => (Set.univ : Set α)) ≤ ksEntropy μ T :=
  entropyRel_le_ksEntropy T (isMeasurablePartition_univ μ)

-- Conjugating by a measure-preserving equivalence does not change the entropy.
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsProbabilityMeasure μ] {ν : Measure β} [IsProbabilityMeasure ν] (T : α → α)
    (hT : Measurable T) (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    ksEntropy μ T = ksEntropy ν (e ∘ T ∘ e.symm) := by
  refine ksEntropy_eq_of_isomorphic e he hT
    (e.measurable.comp (hT.comp e.symm.measurable)) fun x => ?_
  simp

-- The identity, hence any map isomorphic to it, has zero entropy.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    ksEntropy μ id = 0 :=
  ksEntropy_id μ

/-! The entropies are defined for probability measures only: for the zero measure, which would
give every map entropy `0`, none of them elaborates. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example {α : Type} [MeasurableSpace α] (ξ : Fin 2 → Set α) : ℝ :=
  partitionEntropy (0 : Measure α) ξ

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example {α : Type} [MeasurableSpace α] (T : α → α) (ξ : Fin 2 → Set α) :
    ENNReal :=
  entropyRel (0 : Measure α) T ξ

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example {α : Type} [MeasurableSpace α] (T : α → α) : ENNReal :=
  ksEntropy (0 : Measure α) T

-- Under the identity the refinement of the trivial partition keeps entropy `0`.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    partitionEntropy μ (iterateJoin id (fun _ : Fin 1 => (Set.univ : Set α)) 5) = 0 := by
  rw [partitionEntropy_iterateJoin_id (isMeasurablePartition_univ μ) (by norm_num)]
  simp [partitionEntropy]

/-- Isomorphism modulo null sets ignores null sets: a Dirac mass on `Bool` and on `Unit`, with
the identity maps, are isomorphic although `Bool` and `Unit` have different cardinalities. -/
theorem isIsomorphicMod0_dirac_bool_unit :
    IsIsomorphicMod0 (Measure.dirac true) (id : Bool → Bool)
      (Measure.dirac ()) (id : Unit → Unit) := by
  refine ⟨fun _ => (), fun _ => true, ⟨measurable_const, by simp⟩,
    ⟨measurable_const, by simp⟩,
    ?_, ?_, ?_, ?_⟩
  · change ∀ᵐ x ∂Measure.dirac true, true = x
    rw [ae_dirac_eq, Filter.eventually_pure]
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

-- Hence both systems have the same entropy (zero, as identities).
example : ksEntropy (Measure.dirac true) (id : Bool → Bool) =
    ksEntropy (Measure.dirac ()) (id : Unit → Unit) :=
  ksEntropy_eq_of_isIsomorphicMod0 (MeasurePreserving.id _) (MeasurePreserving.id _)
    isIsomorphicMod0_dirac_bool_unit

-- An everywhere conjugacy by a measure-preserving equivalence is an isomorphism modulo null sets.
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    (T : α → α) (e : α ≃ᵐ β) :
    IsIsomorphicMod0 μ T (μ.map e) (e ∘ T ∘ e.symm) :=
  isIsomorphicMod0_of_measurableEquiv e (e.measurable.measurePreserving μ) fun x => by simp

end MathlibExtTest.Dynamics.Ergodic.KolmogorovSinaiEntropy
