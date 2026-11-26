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
# Augmented simplicial objects over a fixed target

Let X be an augmented simplicial object in a category C, with augmentation ε : X.left →
const(B), and let a : B → A. Each degree becomes an object of Over A through ε_n ≫ a : X_n →
A, while the augmentation point is the object a : B → A. The maps ε_n define an augmented
simplicial object in this slice.

An augmented morphism f : X → Y with f.right ≫ b = a induces a slice morphism with the same
degree and point maps. This construction respects identities and composition. A right extra
degeneracy lifts as well because s_n ≫ ε_{n+1} = ε_n and s' ≫ ε₀ = id_B. The category's object
and morphism universes are independent.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] {A : C}

/-- Augmented simplicial diagram in a slice category.

For ε : X.left → const(B) and a : B → A, form an augmented object of Over A with degree-n
structural map ε_n ≫ a, point object B →ᵃ A and degreewise augmentation ε_n. The underlying
simplicial diagram remains X.left. -/
def overPoint (X : SimplicialObject.Augmented C) (a : X.right ⟶ A) :
    SimplicialObject.Augmented (Over A) where
  left := Over.lift X.left (X.hom ≫ (SimplicialObject.const C).map a)
  right := Over.mk a
  hom :=
    { app i := Over.homMk (X.hom.app i) rfl
      naturality {i j} f := by
        apply Over.OverMorphism.ext
        exact X.hom.naturality f }

/-- Underlying augmentation component in the slice.

For the slice object overPoint X a and any simplex-category object i, the underlying arrow of
its augmentation component is X.hom.app i, the original augmentation map ε_i. -/
@[simp]
theorem overPoint_hom_app_left (X : SimplicialObject.Augmented C)
    (a : X.right ⟶ A) (i : SimplexCategoryᵒᵖ) :
    ((overPoint X a).hom.app i).left = X.hom.app i := rfl

/-- Slice map induced by a point-compatible augmented morphism.

Let f : X → Y be augmented, with point maps a : X.right → A and b : Y.right → A satisfying
f.right ≫ b = a. Its degree maps and point map define overPoint X a → overPoint Y b in the
augmented slice category. -/
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

/-- Identity law for augmented slice transport.

For an augmented X and a : X.right → A, overPointMap applied to id_X with its point
compatibility is the identity of overPoint X a. -/
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

/-- Composition law for augmented slice transport.

For augmented maps f : X → Y and g : Y → Z whose point maps preserve a,b,c to A, the slice map
of f ≫ g equals overPointMap f followed by overPointMap g. The composite point compatibility
is f.right ≫ g.right ≫ c = a. -/
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

/-- Augmentation equation for a right extra degeneracy.

For a right extra degeneracy on X, each s_n : X_n → X_{n+1} satisfies s_n ≫ ε_{n+1} = ε_n.
Naturality of ε along the last face and s_n ≫ d_{n+1} = id give this equality. -/
@[reassoc]
theorem s_comp_augmentation (n : ℕ) :
    ed.s n ≫ X.hom.app (op ⦋n + 1⦌) = X.hom.app (op ⦋n⦌) := by
  have h := X.hom.naturality
    (SimplexCategory.δ (Fin.last (n + 1) : Fin (n + 2))).op
  change X.left.δ (Fin.last (n + 1)) ≫ X.hom.app (op ⦋n⦌) =
    X.hom.app (op ⦋n + 1⦌) ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  rw [← h, ← Category.assoc, ed.s_comp_δ_last, Category.id_comp]

/-- Right extra degeneracy lifted to the augmentation slice.

For a right extra degeneracy of X and a : X.right → A, use the same arrows s' and s_n in Over
A. The equations s' ≫ ε₀ = id and s_n ≫ ε_{n+1} = ε_n make them slice morphisms, and their
face and degeneracy identities are retained. -/
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
