/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationFeasibleSecondaryStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationFeasibleAnchor

/-! The actual second feasible local orbit and its exact size. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual first-axis stabilizer acts by the restricted local representation. -/
noncomputable instance (priority := 2000) generatedAxisLocalStabilizerActualSmul
    (p : Fin 276) : SMul (localAxisStabilizer p) GriessSpace where
  smul h x := rhoLocal h.val x

/-- The genuine restricted action of the actual local first-axis stabilizer. -/
noncomputable instance generatedAxisLocalStabilizerActualAction (p : Fin 276) :
    MulAction (localAxisStabilizer p) GriessSpace where
  smul h x := rhoLocal h.val x
  one_smul x := by
    change rhoLocal 1 x = x
    rw [rhoLocal.map_one]
    rfl
  mul_smul h k x := by
    change rhoLocal (h.val * k.val) x = rhoLocal h.val (rhoLocal k.val x)
    rw [rhoLocal.map_mul]
    rfl

/-- The actual secondary stabilizer is precisely the genuine transition subgroup. -/
theorem generatedFeasibleSecondaryAxis_stabilizer (p : Fin 276) :
    MulAction.stabilizer (localAxisStabilizer p) (generatedFeasibleSecondaryAxis p) =
      localFeasibleTransitionSubgroup p := by
  ext h
  change rhoLocal h.val (generatedFeasibleSecondaryAxis p) =
      generatedFeasibleSecondaryAxis p ↔ h.val ∈ localOmegaStabilizer
  constructor
  · exact localAxisStabilizer_secondary_fixes_omega p h
  · intro hh
    exact localFeasibleTransition_fixes_secondary p ⟨h, hh⟩

/-- The secondary actual local feasible orbit, inside the original vector space. -/
noncomputable def generatedFeasibleSecondaryLocalOrbit (p : Fin 276) : Set GriessSpace :=
  MulAction.orbit (localAxisStabilizer p) (generatedFeasibleSecondaryAxis p)

/-- The actual secondary feasible local orbit has exactly 93,150 vectors. -/
theorem generatedFeasibleSecondaryLocalOrbit_card (p : Fin 276) :
    Nat.card (generatedFeasibleSecondaryLocalOrbit p) = 93150 := by
  rw [generatedFeasibleSecondaryLocalOrbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer, generatedFeasibleSecondaryAxis_stabilizer]
  exact localFeasibleTransitionSubgroup_index p

/-- The second actual local orbit consists of genuinely feasible global axes. -/
theorem generatedFeasibleSecondaryLocalOrbit_subset (p : Fin 276) :
    generatedFeasibleSecondaryLocalOrbit p ⊆ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, p)) 0) (conwayShortAxis (Sum.inl (0, p)) 1) := by
  rintro x ⟨h, rfl⟩
  have hfix : (localIntoGenerated h.val * extraIntoGenerated).val
      (conwayShortAxis (Sum.inl (0, p)) 0) =
        conwayShortAxis (Sum.inl (0, p)) 0 := by
    rw [conwayShortAxis_pair_zero]
    change rhoLocal h.val (sExtra (conwayAxis p)) = conwayAxis p
    rw [conwayAxis_triality]
    exact h.property
  exact ⟨⟨localIntoGenerated h.val * extraIntoGenerated, hfix⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
