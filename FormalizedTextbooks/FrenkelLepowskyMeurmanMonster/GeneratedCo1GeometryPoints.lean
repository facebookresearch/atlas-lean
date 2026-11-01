/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleSubspaces

/-! Actual norm-eight frame-class points of the Conway geometry in binary coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Conway geometry points are the binary coordinates of the norm-eight frame orbit. -/
def generatedCo1GeometryPoints : Set (Fin 24 → ZMod 2) :=
  leechHyperbolicCoordinates '' MulAction.orbit leechIsomSubgroup
    (leechReduction (leechCoordinateFrameLattice 0))

/-- The actual faithful Conway action preserves the actual frame-class point set. -/
theorem generatedCo1GeometryPoints_action (g : Co1) (v : Fin 24 → ZMod 2)
    (hv : v ∈ generatedCo1GeometryPoints) : co1BinaryAction g v ∈ generatedCo1GeometryPoints := by
  induction g using QuotientGroup.induction_on with
  | H e =>
    obtain ⟨x, ⟨h, hh⟩, rfl⟩ := hv
    refine ⟨leechModTwoAction e x, ⟨e * h, ?_⟩, ?_⟩
    · change leechModTwoAction (e * h) _ = leechModTwoAction e x
      rw [map_mul, LinearEquiv.mul_apply]
      exact congrArg (leechModTwoAction e) hh
    · change leechHyperbolicCoordinates (leechModTwoAction e x) =
        leechBinaryAction e (leechHyperbolicCoordinates x)
      simp [leechBinaryAction, LinearEquiv.trans_apply]

/-- The genuine point coordinates and lattice frame orbit have identical cardinality. -/
def generatedCo1GeometryPointsEquiv :
    MulAction.orbit leechIsomSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)) ≃ generatedCo1GeometryPoints where
  toFun x := ⟨leechHyperbolicCoordinates x.val, x.val, x.property, rfl⟩
  invFun x := ⟨leechHyperbolicCoordinates.symm x.val, by
    obtain ⟨y, hy, he⟩ := x.property
    rw [← he, LinearEquiv.symm_apply_apply]
    exact hy⟩
  left_inv x := Subtype.ext (leechHyperbolicCoordinates.symm_apply_apply x.val)
  right_inv x := Subtype.ext (leechHyperbolicCoordinates.apply_symm_apply x.val)

/-- The actual Conway geometry has 8,292,375 frame-class points. -/
theorem generatedCo1GeometryPoints_card : Nat.card generatedCo1GeometryPoints = 8292375 := by
  rw [← Nat.card_congr generatedCo1GeometryPointsEquiv]
  exact leechFrameClass_orbit_card

/-- The span of the actual point coordinates inside the genuine binary Conway module. -/
def generatedCo1GeometryPointSpan : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Submodule.span (ZMod 2) generatedCo1GeometryPoints

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
