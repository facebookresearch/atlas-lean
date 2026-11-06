/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationFeasibleSecondaryCount

/-! Actual feasible transition destinations and the complete first feasible transition column. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine feasible transition inputs, as left transition-subgroup cosets. -/
abbrev generatedFeasibleTransitionCosetSpace (p : Fin 276) :=
  Quotient (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p))

/-- Actual local feasible orbit classes under the actual first-axis stabilizer. -/
abbrev generatedFeasibleLocalOrbitSpace (p : Fin 276) :=
  Quotient (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)

/-- The genuine feasible transition domain has 93,150 actual cosets. -/
theorem generatedFeasibleTransitionCosetSpace_card (p : Fin 276) :
    Nat.card (generatedFeasibleTransitionCosetSpace p) = 93150 := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (localFeasibleTransitionSubgroup p)), ← Subgroup.index_eq_card]
  exact localFeasibleTransitionSubgroup_index p

/-- Feasible triality destinations are invariant as actual local orbit classes on genuine cosets. -/
theorem generatedFeasibleTransition_destination_congr (p : Fin 276) (x : GriessSpace)
    (a b : localAxisStabilizer p)
    (hab : QuotientGroup.rightRel (localFeasibleTransitionSubgroup p) a b) :
    Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
        (sExtra (rhoLocal a.val x)) =
      Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
        (sExtra (rhoLocal b.val x)) := by
  have hn : b * a⁻¹ ∈ localFeasibleTransitionSubgroup p :=
    QuotientGroup.rightRel_apply.mp hab
  obtain ⟨h, hh⟩ := localFeasibleTransition_triality_orbit p ⟨b * a⁻¹, hn⟩
    (rhoLocal a.val x)
  have he : rhoLocal h.val (sExtra (rhoLocal a.val x)) = sExtra (rhoLocal b.val x) := by
    rw [hh]
    apply congrArg sExtra
    change rhoLocal (b.val * a.val⁻¹) (rhoLocal a.val x) = rhoLocal b.val x
    rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel_right]
  apply Quotient.sound'
  rw [MulAction.orbitRel_apply]
  exact MulAction.mem_orbit_symm.mp ⟨h, he⟩

/-- The actual feasible triality transition map, before any ten-class labeling. -/
noncomputable def generatedFeasibleTransitionDestination (p : Fin 276) (x : GriessSpace) :
    generatedFeasibleTransitionCosetSpace p → generatedFeasibleLocalOrbitSpace p :=
  Quotient.lift
    (fun h : localAxisStabilizer p =>
      Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
        (sExtra (rhoLocal h.val x)))
    (generatedFeasibleTransition_destination_congr p x)

/-- Every transition from the actual singleton feasible orbit goes to the proved secondary orbit. -/
theorem generatedFeasibleTransitionDestination_first (p : Fin 276)
    (c : generatedFeasibleTransitionCosetSpace p) :
    generatedFeasibleTransitionDestination p (conwayShortAxis (Sum.inl (0, p)) 1) c =
      Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
        (generatedFeasibleSecondaryAxis p) := by
  induction c using Quotient.inductionOn with
  | h h =>
    change Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
      (sExtra (rhoLocal h.val (conwayShortAxis (Sum.inl (0, p)) 1))) = _
    rw [localAxisStabilizer_signedAxis_fixed h.val p h.property 1]
    rfl

/-- The first feasible transition column has all its actual inputs in the secondary destination. -/
theorem generatedFeasibleTransitionDestination_first_fiber (p : Fin 276) :
    generatedFeasibleTransitionDestination p (conwayShortAxis (Sum.inl (0, p)) 1) ⁻¹'
      {Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
        (generatedFeasibleSecondaryAxis p)} = Set.univ := by
  ext c
  simp only [Set.mem_preimage, Set.mem_singleton_iff,
    generatedFeasibleTransitionDestination_first, Set.mem_univ]

/-- Exactly 93,150 actual first feasible transition inputs reach the secondary orbit. -/
theorem generatedFeasibleTransitionDestination_first_fiber_card (p : Fin 276) :
    Nat.card (generatedFeasibleTransitionDestination p
      (conwayShortAxis (Sum.inl (0, p)) 1) ⁻¹'
        {Quotient.mk (MulAction.orbitRel (localAxisStabilizer p) GriessSpace)
          (generatedFeasibleSecondaryAxis p)}) = 93150 := by
  rw [generatedFeasibleTransitionDestination_first_fiber,
    Nat.card_congr (Equiv.Set.univ _)]
  exact generatedFeasibleTransitionCosetSpace_card p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
