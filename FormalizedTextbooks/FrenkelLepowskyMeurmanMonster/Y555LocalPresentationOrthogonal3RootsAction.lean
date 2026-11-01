/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual original E7 image fixes its explicit finite root set. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7ParabolicWords
public import Mathlib.GroupTheory.GroupAction.Defs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise

/-- Each actual source E7 matrix reflection fixes the explicit finite root set. -/
theorem y322Orthogonal3E7Roots_generator_fixed (g : Fin 7) :
    y322Orthogonal3Generator g.castSucc • y322Orthogonal3E7Roots =
      y322Orthogonal3E7Roots := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨y322Orthogonal3E7RootIndex g i, Finset.mem_univ _, ?_⟩
    exact (y322Orthogonal3E7RootMatrix_action g i).symm
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_smul_finset.mpr
    refine ⟨y322Orthogonal3E7RootMatrix (y322Orthogonal3E7RootIndex g i), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · change y322Orthogonal3Reflection g.castSucc *
        y322Orthogonal3E7RootMatrix (y322Orthogonal3E7RootIndex g i) =
          y322Orthogonal3E7RootMatrix i
      rw [y322Orthogonal3E7RootMatrix_action, y322Orthogonal3E7RootIndex_involution]

/-- The actual finite subgroup image of the original E7 source parabolic. -/
def y322Orthogonal3E7Image : Subgroup (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :=
  y322E7Parabolic.map y322Orthogonal3Hom

/-- Every actual element of the original E7 finite image fixes the explicit source root set. -/
theorem y322Orthogonal3E7Image_le_stabilizer :
    y322Orthogonal3E7Image ≤ MulAction.stabilizer
      (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) y322Orthogonal3E7Roots := by
  rw [y322Orthogonal3E7Image, Subgroup.map_le_iff_le_comap,
    y322E7Parabolic, Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  change y322Orthogonal3Hom (PresentedGroup.of g.castSucc) • y322Orthogonal3E7Roots =
    y322Orthogonal3E7Roots
  rw [y322Orthogonal3Hom_generator]
  exact y322Orthogonal3E7Roots_generator_fixed g

/-- The literal source root set is fixed under every actual original E7 image element. -/
theorem y322Orthogonal3E7Image_fixed
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (hg : g ∈ y322Orthogonal3E7Image) :
    g • y322Orthogonal3E7Roots = y322Orthogonal3E7Roots :=
  y322Orthogonal3E7Image_le_stabilizer hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
