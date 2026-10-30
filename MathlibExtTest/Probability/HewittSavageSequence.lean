/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HewittSavageSequence

import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.HewittSavageSequence

namespace MathlibExtTest.Probability.HewittSavageSequence

/-- The empty set is an exchangeable event: it is measurable and invariant. -/
example {S : Type*} [MeasurableSpace S] :
    IsExchangeableEvent (∅ : Set (ℕ → S)) :=
  ⟨MeasurableSet.empty, fun _ _ => by simp⟩

/-- The whole space is an exchangeable event. -/
example {S : Type*} [MeasurableSpace S] :
    IsExchangeableEvent (Set.univ : Set (ℕ → S)) :=
  ⟨MeasurableSet.univ, fun _ _ => by simp⟩

/-- The empty event is exchangeable with respect to any sequence. -/
example {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (X : ℕ → Ω → S) :
    IsExchangeableEventWrt X (∅ : Set Ω) :=
  ⟨∅, ⟨MeasurableSet.empty, fun _ _ => by simp⟩, by simp⟩

/-- The whole space is exchangeable with respect to any sequence. -/
example {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (X : ℕ → Ω → S) :
    IsExchangeableEventWrt X (Set.univ : Set Ω) :=
  ⟨Set.univ, ⟨MeasurableSet.univ, fun _ _ => by simp⟩, by simp⟩

/-- An exchangeable event with respect to a measurable sequence is measurable,
applied to the whole space. -/
example {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n)) :
    MeasurableSet (Set.univ : Set Ω) :=
  IsExchangeableEventWrt.measurableSet hX
    ⟨Set.univ, ⟨MeasurableSet.univ, fun _ _ => by simp⟩, by simp⟩

/-- The set of constant sequences is an exchangeable event: permuting coordinates
preserves constancy, and it is measurable as a countable intersection of
diagonal preimages. -/
theorem exchangeable_constSeq :
    IsExchangeableEvent {x : ℕ → ℝ | ∀ n, x n = x 0} := by
  refine ⟨?_, ?_⟩
  · have hdiag : ∀ n : ℕ,
        MeasurableSet {x : ℕ → ℝ | x n = x 0} := by
      intro n
      have hmeas : Measurable (fun x : ℕ → ℝ => (x n, x 0)) :=
        (measurable_pi_apply n).prodMk (measurable_pi_apply 0)
      have hset : {x : ℕ → ℝ | x n = x 0} =
          (fun x : ℕ → ℝ => (x n, x 0)) ⁻¹' Set.diagonal ℝ := by
        ext x
        simp [Set.diagonal]
      rw [hset]
      exact hmeas (isClosed_diagonal.measurableSet)
    have hset : {x : ℕ → ℝ | ∀ n, x n = x 0} =
        ⋂ n : ℕ, {x : ℕ → ℝ | x n = x 0} := by
      ext x
      simp
    rw [hset]
    exact MeasurableSet.iInter hdiag
  · intro σ _
    ext x
    show (∀ n, (x ∘ σ) n = (x ∘ σ) 0) ↔ ∀ n, x n = x 0
    simp only [Function.comp_apply]
    constructor
    · intro h n
      have h0 : x 0 = x (σ 0) := by
        have h0' := h (σ.symm 0)
        rwa [Equiv.apply_symm_apply] at h0'
      have hn : x n = x (σ 0) := by
        have := h (σ.symm n)
        rwa [Equiv.apply_symm_apply] at this
      rw [hn, ← h0]
    · intro h n
      rw [h (σ n), h (σ 0)]

/-- Coordinate projections on the i.i.d. product space are measurable. -/
private theorem coord_measurable (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ => ω n) :=
  measurable_pi_apply n

/-- Coordinate projections on the i.i.d. product space are identically
distributed. -/
private theorem coord_identDistrib (i : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω 0)
      (Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ)))
      (Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩

/-- Coordinate projections on the i.i.d. product space are independent. -/
private theorem coord_indepFun :
    iIndepFun (m := fun _ => inferInstance) (fun (n : ℕ) (ω : ℕ → ℝ) => ω n)
      (Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))) :=
  ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)

/-- Hewitt–Savage applied to the whole space on the coordinate sequence. -/
example :
    Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))
        (Set.univ : Set (ℕ → ℝ)) = 0 ∨
      Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))
        (Set.univ : Set (ℕ → ℝ)) = 1 :=
  hewittSavage_zeroOne (X := fun (n : ℕ) (ω : ℕ → ℝ) => ω n) coord_measurable
    coord_identDistrib coord_indepFun
    (E := Set.univ)
    ⟨Set.univ, ⟨MeasurableSet.univ, fun _ _ => by simp⟩, by simp⟩

/-- Hewitt–Savage applied to the event that the coordinate sequence is
constant: a nontrivial exchangeable event of the i.i.d. coordinate sequence. -/
example :
    Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))
        {ω : ℕ → ℝ | ∀ n, ω n = ω 0} = 0 ∨
      Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))
        {ω : ℕ → ℝ | ∀ n, ω n = ω 0} = 1 :=
  hewittSavage_zeroOne (X := fun (n : ℕ) (ω : ℕ → ℝ) => ω n) coord_measurable
    coord_identDistrib coord_indepFun
    (E := {ω : ℕ → ℝ | ∀ n, ω n = ω 0})
    ⟨{x : ℕ → ℝ | ∀ n, x n = x 0}, exchangeable_constSeq, rfl⟩

end MathlibExtTest.Probability.HewittSavageSequence

#print axioms MathlibExt.Probability.HewittSavageSequence.hewittSavage_zeroOne
