/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFiberCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

/-! Actual triality transitions reverse by an explicit odd-cocode reflection in H. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A fixed actual odd cocode, with its genuine local-group lift. -/
def generatedAxisTransitionReflector : H := inclQ (cocodeQ (Pi.single 11 1))

/-- The actual local reflector has square one. -/
theorem generatedAxisTransition_reflector_square :
    generatedAxisTransitionReflector * generatedAxisTransitionReflector = 1 := by
  unfold generatedAxisTransitionReflector
  rw [← map_mul, cocodeQ_square, map_one]

/-- Actual triality followed by the odd local reflector is an involution. -/
def generatedAxisTransitionReflection : GriessSpace ≃ₗ[ℝ] GriessSpace :=
  rhoLocal generatedAxisTransitionReflector * sExtra

/-- The genuine reflector conjugates original triality to its inverse. -/
theorem generatedAxisTransition_reflector_conjugates :
    rhoLocal generatedAxisTransitionReflector * sExtra *
      (rhoLocal generatedAxisTransitionReflector)⁻¹ = sExtra⁻¹ :=
  cocodeQ_conjugates_sExtra_inverse _ (by simp)

/-- The concrete transition-reflection matrix squares to the identity. -/
theorem generatedAxisTransition_reflection_square :
    generatedAxisTransitionReflection * generatedAxisTransitionReflection = 1 := by
  have ha : rhoLocal generatedAxisTransitionReflector *
      rhoLocal generatedAxisTransitionReflector = 1 := by
    rw [← map_mul, generatedAxisTransition_reflector_square, map_one]
  have hi := generatedAxisTransition_reflector_conjugates
  rw [inv_eq_of_mul_eq_one_left ha] at hi
  calc
    _ = (rhoLocal generatedAxisTransitionReflector * sExtra *
      rhoLocal generatedAxisTransitionReflector) * sExtra := by
        unfold generatedAxisTransitionReflection
        group
    _ = 1 := by rw [hi, inv_mul_cancel]

/-- Applying triality after reflection equals applying the genuine H reflector. -/
theorem generatedAxisTransition_triality_reflection :
    sExtra * generatedAxisTransitionReflection = rhoLocal generatedAxisTransitionReflector := by
  have ha : rhoLocal generatedAxisTransitionReflector *
      rhoLocal generatedAxisTransitionReflector = 1 := by
    rw [← map_mul, generatedAxisTransition_reflector_square, map_one]
  have hi := generatedAxisTransition_reflector_conjugates
  rw [inv_eq_of_mul_eq_one_left ha] at hi
  have h := congrArg (fun e => rhoLocal generatedAxisTransitionReflector * e * sExtra) hi
  simpa only [generatedAxisTransitionReflection, mul_assoc, ← mul_assoc
    (rhoLocal generatedAxisTransitionReflector) (rhoLocal generatedAxisTransitionReflector),
    ha, one_mul, inv_mul_cancel, mul_one] using h

/-- Actual vectors in one local orbit whose triality image is in another local orbit. -/
def generatedAxisTransitionVectors (a b : GriessSpace) : Set GriessSpace :=
  {x | x ∈ MulAction.orbit H a ∧ sExtra x ∈ MulAction.orbit H b}

private theorem generatedAxisTransition_local_orbit_mem (h : H) (x a : GriessSpace)
    (hx : x ∈ MulAction.orbit H a) : rhoLocal h x ∈ MulAction.orbit H a := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact MulAction.mem_orbit_iff.mpr ⟨h * g, by
    change rhoLocal (h * g) a = rhoLocal h (rhoLocal g a)
    rw [map_mul, LinearEquiv.mul_apply]⟩

/-- The concrete reflection sends each actual transition vector to the reverse transition. -/
theorem generatedAxisTransition_reflection_mem (a b x : GriessSpace)
    (hx : x ∈ generatedAxisTransitionVectors a b) :
    generatedAxisTransitionReflection x ∈ generatedAxisTransitionVectors b a := by
  constructor
  · change rhoLocal generatedAxisTransitionReflector (sExtra x) ∈ MulAction.orbit H b
    exact generatedAxisTransition_local_orbit_mem _ _ _ hx.2
  · have he : sExtra (generatedAxisTransitionReflection x) =
        rhoLocal generatedAxisTransitionReflector x := by
      rw [← LinearEquiv.mul_apply, generatedAxisTransition_triality_reflection]
    rw [he]
    exact generatedAxisTransition_local_orbit_mem _ _ _ hx.1

/-- Exact equivalence between both directions of actual triality transitions. -/
def generatedAxisTransitionReverseEquiv (a b : GriessSpace) :
    generatedAxisTransitionVectors a b ≃ generatedAxisTransitionVectors b a where
  toFun x := ⟨generatedAxisTransitionReflection x.val,
    generatedAxisTransition_reflection_mem a b x.val x.property⟩
  invFun x := ⟨generatedAxisTransitionReflection x.val,
    generatedAxisTransition_reflection_mem b a x.val x.property⟩
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
theorem generatedAxisTransition_vectors_card_reverse (a b : GriessSpace) :
    Nat.card (generatedAxisTransitionVectors a b) =
      Nat.card (generatedAxisTransitionVectors b a) :=
  Nat.card_congr (generatedAxisTransitionReverseEquiv a b)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
