/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionReversibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleDestinations

/-! Original triality reverses actual feasible transitions by a reflector fixing the first axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original odd cocode reflector fixes every original pair axis. -/
theorem generatedFeasibleTransition_reflector_fixes (p : Fin 276) :
    rhoLocal generatedAxisTransitionReflector (conwayAxis p) = conwayAxis p := by
  apply trialityBlocksEquiv.injective
  rw [generatedAxisTransitionReflector, cocodeQ_blocks _ (by simp), conwayAxis_blocks]
  ext <;> simp [cocodeDictionaryAction, conwayAxisBlocks]

/-- The actual reflector belongs to the original first-axis stabilizer. -/
def generatedFeasibleTransitionReflector (p : Fin 276) : localAxisStabilizer p :=
  ⟨generatedAxisTransitionReflector, generatedFeasibleTransition_reflector_fixes p⟩

/-- Actual vectors in one local orbit whose triality image is in another local orbit. -/
def generatedFeasibleTransitionVectors (p : Fin 276) (a b : GriessSpace) : Set GriessSpace :=
  {x | x ∈ MulAction.orbit (localAxisStabilizer p) a ∧
    sExtra x ∈ MulAction.orbit (localAxisStabilizer p) b}

private theorem generatedFeasibleTransition_local_orbit_mem (p : Fin 276)
    (h : localAxisStabilizer p) (x a : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer p) a) :
    rhoLocal h.val x ∈ MulAction.orbit (localAxisStabilizer p) a := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact MulAction.mem_orbit_iff.mpr ⟨h * g, by
    change rhoLocal (h.val * g.val) a = rhoLocal h.val (rhoLocal g.val a)
    rw [map_mul, LinearEquiv.mul_apply]⟩

/-- The concrete reflection sends each actual transition vector to the reverse transition. -/
theorem generatedFeasibleTransition_reflection_mem (p : Fin 276) (a b x : GriessSpace)
    (hx : x ∈ generatedFeasibleTransitionVectors p a b) :
    generatedAxisTransitionReflection x ∈ generatedFeasibleTransitionVectors p b a := by
  constructor
  · change rhoLocal generatedAxisTransitionReflector (sExtra x) ∈
      MulAction.orbit (localAxisStabilizer p) b
    exact generatedFeasibleTransition_local_orbit_mem p
      (generatedFeasibleTransitionReflector p) _ _ hx.2
  · have he : sExtra (generatedAxisTransitionReflection x) =
        rhoLocal generatedAxisTransitionReflector x := by
      rw [← LinearEquiv.mul_apply, generatedAxisTransition_triality_reflection]
    rw [he]
    exact generatedFeasibleTransition_local_orbit_mem p
      (generatedFeasibleTransitionReflector p) _ _ hx.1

/-- Exact equivalence between both directions of actual triality transitions. -/
def generatedFeasibleTransitionReverseEquiv (p : Fin 276) (a b : GriessSpace) :
    generatedFeasibleTransitionVectors p a b ≃ generatedFeasibleTransitionVectors p b a where
  toFun x := ⟨generatedAxisTransitionReflection x.val,
    generatedFeasibleTransition_reflection_mem p a b x.val x.property⟩
  invFun x := ⟨generatedAxisTransitionReflection x.val,
    generatedFeasibleTransition_reflection_mem p b a x.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    change generatedAxisTransitionReflection (generatedAxisTransitionReflection x.val) = x.val
    rw [← LinearEquiv.mul_apply, generatedAxisTransition_reflection_square]
    rfl
  right_inv x := by
    apply Subtype.ext
    change generatedAxisTransitionReflection (generatedAxisTransitionReflection x.val) = x.val
    rw [← LinearEquiv.mul_apply, generatedAxisTransition_reflection_square]
    rfl

/-- Actual triality transition vector counts are symmetric, without orbit-class assumptions. -/
theorem generatedFeasibleTransition_vectors_card_reverse (p : Fin 276) (a b : GriessSpace) :
    Nat.card (generatedFeasibleTransitionVectors p a b) =
      Nat.card (generatedFeasibleTransitionVectors p b a) :=
  Nat.card_congr (generatedFeasibleTransitionReverseEquiv p a b)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
