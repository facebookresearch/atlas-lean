/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual fixed finite columns for the original A5 and D6 parabolic matrix images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootsAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationParabolicWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The reduced D6 fundamental-weight column fixed by the five actual A5 source vertices. -/
def y322Orthogonal3A5FixedColumn : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![![2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]

/-- The reduced E7 fundamental-weight column fixed by the six actual D6 source vertices. -/
def y322Orthogonal3D6FixedColumn : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0]]

/-- Every literal A5 generator fixes its genuine reduced fundamental-weight column. -/
theorem y322Orthogonal3A5Fixed_generator (i : Fin 5) :
    y322Orthogonal3Reflection (y322A5Chain i) * y322Orthogonal3A5FixedColumn =
      y322Orthogonal3A5FixedColumn := by
  fin_cases i <;> decide +kernel

/-- Every literal D6 generator fixes its genuine reduced fundamental-weight column. -/
theorem y322Orthogonal3D6Fixed_generator (i : Fin 6) :
    y322Orthogonal3Reflection (y322D6Generator i) * y322Orthogonal3D6FixedColumn =
      y322Orthogonal3D6FixedColumn := by
  fin_cases i <;> decide +kernel

/-- The actual A5 source image fixes the exact finite fundamental-weight column. -/
theorem y322Orthogonal3A5Image_le_column_stabilizer :
    y322A5Parabolic.map y322Orthogonal3Hom ≤ MulAction.stabilizer
      (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) y322Orthogonal3A5FixedColumn := by
  rw [Subgroup.map_le_iff_le_comap, y322A5Parabolic, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change y322Orthogonal3Hom (PresentedGroup.of (y322A5Chain i)) •
    y322Orthogonal3A5FixedColumn = y322Orthogonal3A5FixedColumn
  rw [y322Orthogonal3Hom_generator]
  exact y322Orthogonal3A5Fixed_generator i

/-- The actual characteristic-three image of the original six-generator D6 source parabolic. -/
def y322Orthogonal3D6Image : Subgroup (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :=
  y322D6Parabolic.map y322Orthogonal3Hom

/-- The actual D6 source image fixes the exact finite fundamental-weight column. -/
theorem y322Orthogonal3D6Image_le_column_stabilizer :
    y322Orthogonal3D6Image ≤ MulAction.stabilizer
      (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) y322Orthogonal3D6FixedColumn := by
  rw [y322Orthogonal3D6Image, Subgroup.map_le_iff_le_comap,
    y322D6Parabolic, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change y322Orthogonal3Hom (PresentedGroup.of (y322D6Generator i)) •
    y322Orthogonal3D6FixedColumn = y322Orthogonal3D6FixedColumn
  rw [y322Orthogonal3Hom_generator]
  exact y322Orthogonal3D6Fixed_generator i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
