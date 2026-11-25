/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRightExtraDegeneracy
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Augmented simplicial diagrams as diagrams over a fixed target

For an actual augmented simplicial object `X` and an actual map from its
augmentation point to `A`, every degree is an object over `A`. The degreewise
augmentation is a morphism to the given point object over `A`. A genuine right
extra degeneracy lifts to this augmented diagram by its augmentation identities.

This construction is valid in an arbitrary category. It supplies no acyclicity
or resolution-comparison certificate. The later polynomial application constructs
the extra degeneracy from the actual polynomial generators.

Candidate source; UNEXECUTED.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] {A : C}

/-- The actual augmented diagram in the slice, with its prescribed point map. -/
def overPoint (X : SimplicialObject.Augmented C) (a : X.right ⟶ A) :
    SimplicialObject.Augmented (Over A) where
  left := Over.lift X.left (X.hom ≫ (SimplicialObject.const C).map a)
  right := Over.mk a
  hom :=
    { app i := Over.homMk (X.hom.app i) rfl
      naturality {i j} f := by
        apply Over.OverMorphism.ext
        exact X.hom.naturality f }

@[simp]
theorem overPoint_hom_app_left (X : SimplicialObject.Augmented C)
    (a : X.right ⟶ A) (i : SimplexCategoryᵒᵖ) :
    ((overPoint X a).hom.app i).left = X.hom.app i := rfl

/-- An actual augmented map preserving the point map induces the actual slice map. -/
def overPointMap {X Y : SimplicialObject.Augmented C}
    {a : X.right ⟶ A} {b : Y.right ⟶ A}
    (f : X ⟶ Y) (hf : f.right ≫ b = a) : overPoint X a ⟶ overPoint Y b where
  left :=
    { app i := Over.homMk (f.left.app i) (by
        change f.left.app i ≫ (Y.hom.app i ≫ b) = X.hom.app i ≫ a
        have h := NatTrans.congr_app f.w i
        change f.left.app i ≫ Y.hom.app i = X.hom.app i ≫ f.right at h
        rw [← Category.assoc, h, Category.assoc, hf])
      naturality {i j} g := by
        apply Over.OverMorphism.ext
        exact f.left.naturality g }
  right := Over.homMk f.right hf
  w := by
    apply NatTrans.ext
    funext i
    apply Over.OverMorphism.ext
    exact NatTrans.congr_app f.w i

@[simp]
theorem overPointMap_id (X : SimplicialObject.Augmented C) (a : X.right ⟶ A) :
    overPointMap (𝟙 X) (by exact Category.id_comp a) = 𝟙 (overPoint X a) := by
  apply SimplicialObject.Augmented.hom_ext
  · apply NatTrans.ext
    funext i
    apply Over.OverMorphism.ext
    rfl
  · apply Over.OverMorphism.ext
    rfl

theorem overPointMap_comp {X Y Z : SimplicialObject.Augmented C}
    {a : X.right ⟶ A} {b : Y.right ⟶ A} {c : Z.right ⟶ A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.right ≫ b = a) (hg : g.right ≫ c = b) :
    overPointMap (f ≫ g) (by
      change (f.right ≫ g.right) ≫ c = a
      rw [Category.assoc, hg, hf]) =
        overPointMap f hf ≫ overPointMap g hg := by
  apply SimplicialObject.Augmented.hom_ext
  · apply NatTrans.ext
    funext i
    apply Over.OverMorphism.ext
    rfl
  · apply Over.OverMorphism.ext
    rfl

namespace RightExtraDegeneracy

variable {X : SimplicialObject.Augmented C} (ed : RightExtraDegeneracy X)

/-- The terminal-face identity and the actual augmentation naturality give
compatibility with the entire augmentation in every degree. -/
@[reassoc]
theorem s_comp_augmentation (n : ℕ) :
    ed.s n ≫ X.hom.app (op ⦋n + 1⦌) = X.hom.app (op ⦋n⦌) := by
  have h := X.hom.naturality
    (SimplexCategory.δ (Fin.last (n + 1) : Fin (n + 2))).op
  change X.left.δ (Fin.last (n + 1)) ≫ X.hom.app (op ⦋n⦌) =
    X.hom.app (op ⦋n + 1⦌) ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  rw [← h, ← Category.assoc, ed.s_comp_δ_last, Category.id_comp]

/-- Lift the actual right extra degeneracy to the actual slice diagram. -/
def overPoint (a : X.right ⟶ A) : RightExtraDegeneracy (Augmented.overPoint X a) where
  s' := Over.homMk ed.s' (by
    change ed.s' ≫ (X.hom.app (op ⦋0⦌) ≫ a) = a
    rw [← Category.assoc, ed.s'_comp_ε, Category.id_comp])
  s n := Over.homMk (ed.s n) (by
    change ed.s n ≫ (X.hom.app (op ⦋n + 1⦌) ≫ a) = X.hom.app (op ⦋n⦌) ≫ a
    rw [← Category.assoc, ed.s_comp_augmentation])
  s'_comp_ε := by
    apply Over.OverMorphism.ext
    exact ed.s'_comp_ε
  s₀_comp_δ₀ := by
    apply Over.OverMorphism.ext
    exact ed.s₀_comp_δ₀
  s_comp_δ_last n := by
    apply Over.OverMorphism.ext
    exact ed.s_comp_δ_last n
  s_comp_δ n i := by
    apply Over.OverMorphism.ext
    exact ed.s_comp_δ n i
  s_comp_σ n i := by
    apply Over.OverMorphism.ext
    exact ed.s_comp_σ n i

end RightExtraDegeneracy

end CategoryTheory.SimplicialObject.Augmented

end
