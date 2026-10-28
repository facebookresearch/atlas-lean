/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitReachability

/-! The genuine sixty-three-root orbit in the original actual Tenth matrix coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each actual root class transported into the original actual matrix coordinates. -/
def generatedTenthE7OriginalRootClass (n : Fin 63) : LeechModTwo :=
  leechModTwoAction generatedTenthE7OrbitTransport (generatedTenthE7OrbitNodeClass n)

/-- All sixty-three original actual root classes are distinct. -/
theorem generatedTenth_e7_original_root_class_injective :
    Function.Injective generatedTenthE7OriginalRootClass := by
  intro i j h
  apply generatedTenth_e7_orbit_node_class_injective
  exact (leechModTwoAction generatedTenthE7OrbitTransport).injective h

private theorem conjugate_image (p g : leechIsomSubgroup) (x y : LeechModTwo)
    (h : leechModTwoAction g x = y) :
    leechModTwoAction (p * g * p⁻¹) (leechModTwoAction p x) = leechModTwoAction p y := by
  rw [map_mul, map_mul, map_inv]
  change leechModTwoAction p (leechModTwoAction g
    ((leechModTwoAction p).symm (leechModTwoAction p x))) = _
  rw [LinearEquiv.symm_apply_apply, h]

/-- Actual complete original matrix fixers join every pair of the
sixty-three actual root classes. -/
theorem generatedTenth_e7_original_root_orbit_between (i j : Fin 63) :
    ∃ g : generatedTenthE7OriginalMatrixGroup,
      leechModTwoAction g.val (generatedTenthE7OriginalRootClass i) =
        generatedTenthE7OriginalRootClass j := by
  obtain ⟨g, hg⟩ := generatedTenth_e7_root_orbit_between i j
  refine ⟨⟨generatedTenthE7OrbitConjugation g.val, g.property⟩, ?_⟩
  exact conjugate_image generatedTenthE7OrbitTransport g.val _ _ hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
