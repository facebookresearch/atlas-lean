/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionActualFibers

/-! Genuine weighted symmetry for all actual local-orbit transition coset counts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original triality transitions obey weighted reciprocity for every pair of actual H orbits. -/
theorem generatedAxisActualTransition_reciprocity (a b : GriessSpace) :
    Nat.card (MulAction.orbit H a) * Nat.card (generatedAxisActualTransitionCosets a b) =
      Nat.card (MulAction.orbit H b) * Nat.card (generatedAxisActualTransitionCosets b a) := by
  have ha := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H a)
  have hb := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H b)
  rw [Nat.card_prod] at ha hb
  have hab := generatedAxisActualTransition_fiber_balance a b
  have hba := generatedAxisActualTransition_fiber_balance b a
  have he :
      (Nat.card (MulAction.orbit H a) * Nat.card (generatedAxisActualTransitionCosets a b)) *
          Nat.card localOmegaStabilizer =
        (Nat.card (MulAction.orbit H b) * Nat.card (generatedAxisActualTransitionCosets b a)) *
          Nat.card localOmegaStabilizer := by
    calc
      _ = Nat.card (MulAction.orbit H a) *
          (Nat.card (generatedAxisActualTransitionCosets a b) * Nat.card localOmegaStabilizer) :=
        Nat.mul_assoc _ _ _
      _ = Nat.card (MulAction.orbit H a) *
          (Nat.card (generatedAxisTransitionVectors a b) * Nat.card (MulAction.stabilizer H a)) :=
        congrArg (Nat.card (MulAction.orbit H a) * ·) hab
      _ = Nat.card (generatedAxisTransitionVectors a b) * Nat.card H := by
        rw [← ha]
        ring
      _ = Nat.card (generatedAxisTransitionVectors b a) * Nat.card H := by
        rw [generatedAxisTransition_vectors_card_reverse]
      _ = Nat.card (MulAction.orbit H b) *
          (Nat.card (generatedAxisTransitionVectors b a) *
            Nat.card (MulAction.stabilizer H b)) := by
        rw [← hb]
        ring
      _ = Nat.card (MulAction.orbit H b) *
          (Nat.card (generatedAxisActualTransitionCosets b a) * Nat.card localOmegaStabilizer) :=
        congrArg (Nat.card (MulAction.orbit H b) * ·) hba.symm
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hn : 0 < Nat.card localOmegaStabilizer := by
    rw [localOmegaStabilizer_card, co1OmegaFrameStabilizer_card]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right hn he

/-- The generalized actual transition destination recovers the frozen starting-axis map. -/
theorem generatedAxisActualTransitionDestination_start (p : Fin 276) :
    generatedAxisActualTransitionDestination (conwayAxis p) =
      generatedAxisTransitionDestination p :=
  rfl

/-- Generalized transition cosets recover the exact frozen first-column fibers. -/
theorem generatedAxisActualTransitionCosets_start (p : Fin 276) (b : GriessSpace) :
    generatedAxisActualTransitionCosets (conwayAxis p) b =
      generatedAxisTransitionDestination p ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace) b} := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
