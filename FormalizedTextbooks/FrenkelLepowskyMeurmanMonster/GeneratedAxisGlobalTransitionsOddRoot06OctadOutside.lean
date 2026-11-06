/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSourceCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSparseBindings

/-! Every original octad outside the complete finite active source list has exactly zero outgoing coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

private theorem initial_sparse_zero (r : GriessShortIndex)
    (hr : ∀ p : GeneratedAxisGlobalOddShortPacketIndex, generatedAxisGlobalOddSparseLabel 1 p ≠ r) :
    generatedAxisGlobalOddSparseShortQ 1 r = 0 := by
  rw [← generatedAxisGlobalOddSparseShortQ_sum]
  apply Finset.sum_eq_zero
  intro p _
  simp only [hr p, ite_false, mul_zero]

/-- The original root-six source has zero at every odd short label. -/
theorem generatedAxisGlobalOddRoot06Initial_odd_zero (d : Fin 2048) (j : Fin 24) :
    generatedAxisGlobalOddSparseShortQ 1 (Sum.inr (Sum.inr (d, j))) = 0 := by
  apply initial_sparse_zero
  intro p hp
  have h := generatedAxisGlobalOddRoot06InitialAllowed_certificate p
  rw [hp] at h
  exact h

/-- The original root-six input vanishes on every octad absent from the complete active source list. -/
theorem generatedAxisGlobalOddRoot06Initial_octad_zero (o : Fin 759) (e : Fin 64)
    (ho : ∀ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k ≠ o) :
    generatedAxisGlobalOddSparseShortQ 1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  apply initial_sparse_zero
  intro p hp
  have h := generatedAxisGlobalOddRoot06InitialAllowed_certificate p
  rw [hp] at h
  obtain ⟨k, hk⟩ := h
  exact ho k hk

/-- Complete original Fourier transport introduces no coefficient on an absent source octad. -/
theorem generatedAxisGlobalOddRoot06Positive_octad_zero (o : Fin 759) (e : Fin 64)
    (ho : ∀ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k ≠ o) :
    generatedAxisGlobalOddRoot06PositiveShortQ (Sum.inr (Sum.inl (o, e))) = 0 := by
  simp only [generatedAxisGlobalOddRoot06PositiveShortQ, generatedAxisGlobalRationalTriality,
    generatedAxisGlobalTrialityShortQ, generatedAxisGlobalOddSparseRootPacket]
  apply Finset.sum_eq_zero
  intro f _
  change (trialityIntegerMatrix e f : ℚ) / 8 *
    generatedAxisGlobalOddSparseShortQ 1 (Sum.inr (Sum.inl (o, f))) = 0
  rw [generatedAxisGlobalOddRoot06Initial_octad_zero o f ho, mul_zero]

/-- The complete candidate sparse output has no coefficient on an absent original octad. -/
theorem generatedAxisGlobalOddRoot06Sparse_octad_zero (o : Fin 759) (e : Fin 64)
    (ho : ∀ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k ≠ o) :
    generatedAxisGlobalOddRoot06OctadSparseShortQ (Sum.inr (Sum.inl (o, e))) = 0 := by
  have hn : generatedAxisGlobalOddRoot06OctadSparseSource (Sum.inr (Sum.inl (o, e))) = none := by
    cases hg : generatedAxisGlobalOddRoot06OctadSparseSource (Sum.inr (Sum.inl (o, e))) with
    | none => rfl
    | some p =>
      have hp := generatedAxisGlobalOddRoot06OctadSparse_sound _ p hg
      have h := generatedAxisGlobalOddRoot06OutgoingAllowed_certificate p
      rw [hp] at h
      obtain ⟨k, hk⟩ := h
      exact False.elim (ho k hk)
  simp only [generatedAxisGlobalOddRoot06OctadSparseShortQ, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
