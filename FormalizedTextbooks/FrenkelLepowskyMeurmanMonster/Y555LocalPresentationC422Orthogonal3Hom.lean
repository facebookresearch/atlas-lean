/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete projective characteristic-three homomorphism of the original C422/S/Q source.
Its kernel and image order are not assumed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3Relations
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The concrete source reflection as an actual invertible eight-dimensional matrix. -/
def y422Orthogonal3Generator (i : Fin 9) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) where
  val := y422Orthogonal3Reflection i
  inv := y422Orthogonal3Reflection i
  val_inv := y422Orthogonal3Reflection_square i
  inv_val := y422Orthogonal3Reflection_square i

/-- Every invertible source generator retains its declared actual matrix. -/
theorem y422Orthogonal3Generator_matrix (i : Fin 9) :
    (y422Orthogonal3Generator i).val = y422Orthogonal3Reflection i := rfl

/-- The actual invertible generators satisfy their original source squares. -/
theorem y422Orthogonal3Generator_square (i : Fin 9) : y422Orthogonal3Generator i ^ 2 = 1 := by
  apply Units.ext
  change y422Orthogonal3Reflection i ^ 2 = 1
  rw [pow_two]
  exact y422Orthogonal3Reflection_square i

/-- Actual invertible pairs satisfy every exact original source Coxeter exponent. -/
theorem y422Orthogonal3Generator_coxeter (i j : Fin 9) (h : i ≠ j) :
    (y422Orthogonal3Generator i * y422Orthogonal3Generator j) ^
      (if y444Adjacent (y422Vertex i) (y422Vertex j) then 3 else 2 : ℕ) = 1 := by
  apply Units.ext
  change (y422Orthogonal3Reflection i * y422Orthogonal3Reflection j) ^
    (if y444Adjacent (y422Vertex i) (y422Vertex j) then 3 else 2 : ℕ) = 1
  exact y422Orthogonal3Reflection_coxeter i j h

/-- The literal original spider lifts to its declared actual finite matrix. -/
theorem y422Orthogonal3Spider_matrix :
    (FreeGroup.lift y422Orthogonal3Generator y422Spider).val = y422Orthogonal3Spider := by
  unfold y422Spider
  simp only [map_mul, FreeGroup.lift_apply_of]
  rfl

/-- The corrected first longest spelling lifts to its actual checked matrix value. -/
theorem y422Orthogonal3Longest_matrix :
    (FreeGroup.lift y422Orthogonal3Generator y422F12).val = y422Orthogonal3Longest := by
  unfold y422F12
  simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
  rfl

/-- The original Q cubic is exactly the central minus-identity element before projection. -/
theorem y422Orthogonal3Cubic_scalar :
    FreeGroup.lift y422Orthogonal3Generator y422Cubic =
      Matrix.GeneralLinearGroup.scalar (Fin 8) (-1 : (ZMod 3)ˣ) := by
  apply Units.ext
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 8) (-1 : (ZMod 3)ˣ)).val =
      (-1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) := by decide +kernel
  rw [hs]
  unfold y422Cubic
  simp only [map_pow, map_mul, FreeGroup.lift_apply_of, Units.val_pow_eq_pow_val,
    Units.val_mul, y422Orthogonal3Longest_matrix, y422Orthogonal3Generator_matrix]
  exact y422Orthogonal3Q_scalar

/-- The actual projective image of each original source reflection. -/
def y422Orthogonal3ProjectiveGenerator (i : Fin 9) : Matrix.ProjGenLinGroup (Fin 8) (ZMod 3) :=
  Matrix.ProjGenLinGroup.mk (y422Orthogonal3Generator i)

/-- Lifting an original word and projectivizing gives its literal projective source value. -/
theorem y422Orthogonal3ProjectiveLift :
    FreeGroup.lift y422Orthogonal3ProjectiveGenerator =
      Matrix.ProjGenLinGroup.mk.comp (FreeGroup.lift y422Orthogonal3Generator) := by
  apply FreeGroup.ext_hom
  intro i
  simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply]
  rfl

/-- All original C422/S/Q relations hold in the concrete projective group. -/
theorem y422Orthogonal3ProjectiveRelations_valid (r : FreeGroup (Fin 9))
    (hr : r ∈ y422Relations) : FreeGroup.lift y422Orthogonal3ProjectiveGenerator r = 1 := by
  rw [y422Orthogonal3ProjectiveLift, MonoidHom.comp_apply]
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl | rfl
  · simp only [map_pow, FreeGroup.lift_apply_of, y422Orthogonal3Generator_square, map_one]
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of,
      y422Orthogonal3Generator_coxeter u v huv, map_one]
  · have hs : FreeGroup.lift y422Orthogonal3Generator (y422Spider ^ 10) = 1 := by
      rw [map_pow]
      apply Units.ext
      change (FreeGroup.lift y422Orthogonal3Generator y422Spider).val ^ 10 = 1
      rw [y422Orthogonal3Spider_matrix]
      exact y422Orthogonal3Spider_tenth
    rw [hs, map_one]
  · rw [y422Orthogonal3Cubic_scalar]
    exact Matrix.ProjGenLinGroup.mk_scalar _

/-- The genuine homomorphism from original C422/S/Q to explicit projective matrices over F3. -/
def y422Orthogonal3ProjectiveHom : Y422Presentation →*
    Matrix.ProjGenLinGroup (Fin 8) (ZMod 3) :=
  PresentedGroup.toGroup y422Orthogonal3ProjectiveRelations_valid

/-- Each original source generator keeps its exact declared projective matrix image. -/
@[simp] theorem y422Orthogonal3ProjectiveHom_generator (i : Fin 9) :
    y422Orthogonal3ProjectiveHom (PresentedGroup.of i) = y422Orthogonal3ProjectiveGenerator i :=
  PresentedGroup.toGroup.of y422Orthogonal3ProjectiveRelations_valid

/-- The concrete projective matrix subgroup generated by the original source images. -/
def y422Orthogonal3ProjectiveImage : Subgroup (Matrix.ProjGenLinGroup (Fin 8) (ZMod 3)) :=
  y422Orthogonal3ProjectiveHom.range

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
