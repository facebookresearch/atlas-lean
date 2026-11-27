/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Category bar objects with coefficients

For M : C → A, the degree-n bar object is the coproduct of M(F.left) over
length-n composable-arrow chains F in C. Its face and degeneracy maps apply
the coefficient functor to the corresponding endpoint arrows. Coproduct
injections characterize these maps. The coefficient category requires sized
coproducts; the simplicial identities are proved in the companion modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

/-- The family of coefficient objects indexed by degree-`n` chains. -/
def coefficientBarFamily (n : ℕ) : ComposableArrows C n → A :=
  fun F ↦ M.obj F.left

/-- Degree-`n` coefficient bar object. -/
noncomputable abbrev coefficientBarObj (n : ℕ) : A :=
  ∐ coefficientBarFamily M n

/-- Inclusion of the summand indexed by a composable-arrow diagram. -/
noncomputable abbrev coefficientBarι {n : ℕ} (F : ComposableArrows C n) :
    M.obj F.left ⟶ coefficientBarObj M n :=
  Sigma.ι (coefficientBarFamily M n) F

/-- Morphisms out of a coefficient bar object are determined on its summands. -/
theorem coefficientBar_hom_ext {n : ℕ} {Z : A}
    (f g : coefficientBarObj M n ⟶ Z)
    (h : ∀ F, coefficientBarι M F ≫ f = coefficientBarι M F ≫ g) :
    f = g :=
  Sigma.hom_ext f g h

/-- The zeroth face changes the left endpoint to the old second object. -/
theorem face_left_zero {n : ℕ} (F : ComposableArrows C (n + 1)) :
    ((nerve C).δ (0 : Fin (n + 2)) F).left = F.obj' 1 := rfl

/-- A nonzero face preserves the left endpoint. -/
theorem face_left_eq_of_ne_zero {n : ℕ} {i : Fin (n + 2)}
    (hi : i.val ≠ 0) (F : ComposableArrows C (n + 1)) :
    F.left = ((nerve C).δ i F).left := by
  have hi0 : i ≠ 0 := by
    intro h
    apply hi
    rw [h]
    rfl
  change F.obj ⟨0, by omega⟩ = ((nerve C).δ i F).obj (0 : Fin _)
  rw [CategoryTheory.nerve.δ_obj]
  congr 1
  exact (Fin.succAbove_ne_zero_zero hi0).symm

/-- Canonical arrow from the old left endpoint to the left endpoint after a face. It is the image
under the chain functor of the unique order arrow from zero to the new zeroth index. -/
noncomputable def faceLeftHom {n : ℕ} (i : Fin (n + 2))
    (F : ComposableArrows C (n + 1)) :
    F.left ⟶ ((nerve C).δ i F).left :=
  F.map (homOfLE (Fin.zero_le (i.succAbove 0)))

/-- The endpoint arrow for the first face is the first arrow of the given composable-arrow chain. -/
@[simp]
theorem faceLeftHom_zero {n : ℕ} (F : ComposableArrows C (n + 1)) :
    faceLeftHom (0 : Fin (n + 2)) F = F.map' 0 1 := rfl

/-- Coefficient morphism on a face summand. -/
noncomputable def coefficientFaceHom {n : ℕ} (i : Fin (n + 2))
    (F : ComposableArrows C (n + 1)) :
    M.obj F.left ⟶ M.obj ((nerve C).δ i F).left :=
  M.map (faceLeftHom i F)

/-- Face map of coefficient bar objects. -/
noncomputable def coefficientBarFace {n : ℕ} (i : Fin (n + 2)) :
    coefficientBarObj M (n + 1) ⟶ coefficientBarObj M n :=
  Sigma.map' (f := coefficientBarFamily M n)
    (g := coefficientBarFamily M (n + 1))
    (fun F ↦ (nerve C).δ i F) (coefficientFaceHom M i)

/-- Formula for a coefficient bar face on a coproduct summand. -/
@[reassoc (attr := simp)]
theorem coefficientBarι_face {n : ℕ} (i : Fin (n + 2))
    (F : ComposableArrows C (n + 1)) :
    coefficientBarι M F ≫ coefficientBarFace M i =
      coefficientFaceHom M i F ≫
        coefficientBarι M ((nerve C).δ i F) := by
  dsimp [coefficientBarFace, coefficientBarι, Sigma.map']
  exact Sigma.ι_comp_desc _ F

omit [HasCoproducts.{max u₁ v₁} A] in
/-- The coefficient morphism of the zeroth face is the image of the first arrow. -/
@[simp]
theorem coefficientFaceHom_zero {n : ℕ} (F : ComposableArrows C (n + 1)) :
    coefficientFaceHom M (0 : Fin (n + 2)) F =
      M.map (F.map' 0 1) := rfl

/-- Formula for the zeroth face on a coproduct summand. -/
@[reassoc (attr := simp)]
theorem coefficientBarι_face_zero {n : ℕ}
    (F : ComposableArrows C (n + 1)) :
    coefficientBarι M F ≫ coefficientBarFace M (0 : Fin (n + 2)) =
      M.map (F.map' 0 1) ≫
        coefficientBarι M ((nerve C).δ 0 F) := by
  rw [coefficientBarι_face, coefficientFaceHom_zero]
  rfl

/-- Degeneracies preserve the left endpoint. -/
theorem degeneracy_left_eq {n : ℕ} {i : Fin (n + 1)}
    (F : ComposableArrows C n) :
    F.left = ((nerve C).σ i F).left := by
  change F.obj ⟨0, by omega⟩ = ((nerve C).σ i F).obj (0 : Fin _)
  rw [CategoryTheory.nerve.σ_obj]
  have h : (⟨0, by omega⟩ : Fin _) = i.predAbove (0 : Fin _) :=
    Fin.predAbove_right_zero.symm
  exact congrArg _ h

/-- Canonical arrow from the old left endpoint to the left endpoint after a degeneracy. -/
noncomputable def degeneracyLeftHom {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    F.left ⟶ ((nerve C).σ i F).left :=
  F.map (homOfLE (Fin.zero_le (i.predAbove 0)))

/-- Coefficient morphism on a degeneracy summand. -/
noncomputable def coefficientDegeneracyHom {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    M.obj F.left ⟶ M.obj ((nerve C).σ i F).left :=
  M.map (degeneracyLeftHom i F)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- The coefficient morphism on a degeneracy summand is the coefficient functor applied to its
endpoint arrow. -/
@[simp]
theorem coefficientDegeneracyHom_eq {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    coefficientDegeneracyHom M i F =
      M.map (degeneracyLeftHom i F) := rfl

/-- Degeneracy map of coefficient bar objects. -/
noncomputable def coefficientBarDegeneracy {n : ℕ} (i : Fin (n + 1)) :
    coefficientBarObj M n ⟶ coefficientBarObj M (n + 1) :=
  Sigma.map' (f := coefficientBarFamily M (n + 1))
    (g := coefficientBarFamily M n)
    (fun F ↦ (nerve C).σ i F) (coefficientDegeneracyHom M i)

/-- Formula for a coefficient bar degeneracy on a coproduct summand. -/
@[reassoc (attr := simp)]
theorem coefficientBarι_degeneracy {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    coefficientBarι M F ≫ coefficientBarDegeneracy M i =
      coefficientDegeneracyHom M i F ≫
        coefficientBarι M ((nerve C).σ i F) := by
  dsimp [coefficientBarDegeneracy, coefficientBarι, Sigma.map']
  exact Sigma.ι_comp_desc _ F

end CategoryTheory.CategoryHomology

end
