/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Constructive actual D6 and E7 image lower bounds from checked source-word column orbits. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5LowerBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3D6A5Orbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3E7D6Orbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ParabolicFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationImageSubgroupLowerBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationD6Order
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7Order

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The checked D6 fundamental-weight vector has exactly the actual A5 fixed column matrix. -/
theorem y322Orthogonal3D6A5Point_column : y322Orthogonal3A5FixedColumn =
    Matrix.vecMulVec y322Orthogonal3D6A5Point (Pi.single (0 : Fin 7) 1) := by
  decide +kernel

/-- The checked E7 fundamental-weight vector has exactly the actual D6 fixed column matrix. -/
theorem y322Orthogonal3E7D6Point_column : y322Orthogonal3D6FixedColumn =
    Matrix.vecMulVec y322Orthogonal3E7D6Point (Pi.single (0 : Fin 7) 1) := by
  decide +kernel

/-- Each original D6 source representative has its exact inverse action on the A5 fixed column. -/
theorem y322Orthogonal3D6A5Orbit_source_column (i : Fin 32) :
    (y322Orthogonal3Hom (y322PositiveWord (y322D6A5RepresentativeWord i)))⁻¹ •
        y322Orthogonal3A5FixedColumn =
      Matrix.vecMulVec (y322Orthogonal3D6A5Orbit i) (Pi.single (0 : Fin 7) 1) := by
  rw [y322Orthogonal3D6A5Point_column]
  exact y322InverseWordOrbit_checked_column _ _ _ _ _ y322Orthogonal3D6A5Orbit_checked i

/-- Each original E7 source representative has its exact inverse action on the D6 fixed column. -/
theorem y322Orthogonal3E7D6Orbit_source_column (i : Fin 126) :
    (y322Orthogonal3Hom (y322PositiveWord (y322E7D6RepresentativeWord i)))⁻¹ •
        y322Orthogonal3D6FixedColumn =
      Matrix.vecMulVec (y322Orthogonal3E7D6Orbit i) (Pi.single (0 : Fin 7) 1) := by
  rw [y322Orthogonal3E7D6Point_column]
  exact y322InverseWordOrbit_checked_column _ _ _ _ _ y322Orthogonal3E7D6Orbit_checked i

/-- The actual D6 image contains at least 32 times the genuine A5 image order. -/
theorem y322Orthogonal3D6Image_card_ge : 23040 ≤ Nat.card y322Orthogonal3D6Image := by
  let representative := fun i : Fin 32 =>
    y322Orthogonal3Hom (y322PositiveWord (y322D6A5RepresentativeWord i))
  have hrep (i : Fin 32) : representative i ∈ y322Orthogonal3D6Image :=
    ⟨_, y322D6A5Representative_mem i, rfl⟩
  have hle : y322Orthogonal3A5Image ≤ y322Orthogonal3D6Image :=
    Subgroup.map_mono y322A5Parabolic_le_D6
  have hd : Function.Injective (fun i => (representative i)⁻¹ •
      y322Orthogonal3A5FixedColumn) := by
    intro i j hij
    apply y322OrbitColumn_injective _ y322Orthogonal3D6A5Orbit_injective
    dsimp only
    rw [← y322Orthogonal3D6A5Orbit_source_column, ← y322Orthogonal3D6A5Orbit_source_column]
    exact hij
  have h := y322FiniteSubgroup_card_ge_of_orbit y322Orthogonal3A5Image
    y322Orthogonal3D6Image hle y322Orthogonal3A5FixedColumn
    (fun _ hk => y322Orthogonal3A5Image_le_column_stabilizer hk) representative hrep hd
  exact (Nat.mul_le_mul_right 32 y322Orthogonal3A5Image_card_ge).trans h

/-- The actual E7 image contains at least 126 times the genuine D6 image order. -/
theorem y322Orthogonal3E7Image_card_ge : 2903040 ≤ Nat.card y322Orthogonal3E7Image := by
  let representative := fun i : Fin 126 =>
    y322Orthogonal3Hom (y322PositiveWord (y322E7D6RepresentativeWord i))
  have hrep (i : Fin 126) : representative i ∈ y322Orthogonal3E7Image :=
    ⟨_, y322E7D6Representative_mem i, rfl⟩
  have hle : y322Orthogonal3D6Image ≤ y322Orthogonal3E7Image :=
    Subgroup.map_mono y322D6Parabolic_le_E7
  have hd : Function.Injective (fun i => (representative i)⁻¹ •
      y322Orthogonal3D6FixedColumn) := by
    intro i j hij
    apply y322OrbitColumn_injective _ y322Orthogonal3E7D6Orbit_injective
    dsimp only
    rw [← y322Orthogonal3E7D6Orbit_source_column, ← y322Orthogonal3E7D6Orbit_source_column]
    exact hij
  have h := y322FiniteSubgroup_card_ge_of_orbit y322Orthogonal3D6Image
    y322Orthogonal3E7Image hle y322Orthogonal3D6FixedColumn
    (fun _ hk => y322Orthogonal3D6Image_le_column_stabilizer hk) representative hrep hd
  exact (Nat.mul_le_mul_right 126 y322Orthogonal3D6Image_card_ge).trans h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
