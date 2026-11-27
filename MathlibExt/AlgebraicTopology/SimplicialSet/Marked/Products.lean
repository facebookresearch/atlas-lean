/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The original Cartesian product of marked simplicial sets

The native simplicial product is marked precisely when both original
projected edges are marked. The original projections and simultaneous
lift give the full marked Hom universal property. The same product maps
retain their whole underlying tensor maps, identities and composition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original simplicial product with the intersection of its two projection markings. -/
def prod (X Y : Marked.{u}) : Marked.{u} where
  toSSet := X.toSSet ⊗ Y.toSSet
  marking := {a | a.1 ∈ X.marking ∧ a.2 ∈ Y.marking}
  degenerate_mem a := ⟨X.degenerate_mem a.1, Y.degenerate_mem a.2⟩

/-- The first marked projection is the original first simplicial projection. -/
def prodFst (X Y : Marked.{u}) : prod X Y ⟶ X :=
  ⟨CartesianMonoidalCategory.fst _ _, fun h => h.1⟩

/-- The second marked projection retains the original second map. -/
def prodSnd (X Y : Marked.{u}) : prod X Y ⟶ Y :=
  ⟨CartesianMonoidalCategory.snd _ _, fun h => h.2⟩

/-- The actual simultaneous simplicial lift preserves both original markings. -/
def prodLift {T X Y : Marked.{u}} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ prod X Y :=
  ⟨CartesianMonoidalCategory.lift f.hom g.hom, fun h => ⟨f.preserve h, g.preserve h⟩⟩

/-- The full marked product universal property is given by these same original maps. -/
def prodHomEquiv (T X Y : Marked.{u}) : (T ⟶ prod X Y) ≃ (T ⟶ X) × (T ⟶ Y) where
  toFun f := ⟨f ≫ prodFst X Y, f ≫ prodSnd X Y⟩
  invFun fg := prodLift fg.1 fg.2
  left_inv f := by
    apply Hom.ext
    ext n a
    exact Prod.eta _
  right_inv fg := by
    apply Prod.ext <;> apply Hom.ext <;> rfl

/-- Pairing the original marked maps gives the same native product map. -/
def prodMap {X X' Y Y' : Marked.{u}} (f : X ⟶ X') (g : Y ⟶ Y') : prod X Y ⟶ prod X' Y' :=
  ⟨f.hom ⊗ₘ g.hom, fun h => ⟨f.preserve h.1, g.preserve h.2⟩⟩

/-- The whole underlying product map is literally the native simplicial tensor map. -/
@[simp] theorem prodMap_hom {X X' Y Y' : Marked.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (prodMap f g).hom = f.hom ⊗ₘ g.hom := rfl

/-- Original product maps retain strict identity. -/
@[simp] theorem prodMap_id (X Y : Marked.{u}) : prodMap (𝟙 X) (𝟙 Y) = 𝟙 (prod X Y) := by
  apply Hom.ext
  ext n a
  rfl

/-- Original product maps retain the actual componentwise composition. -/
theorem prodMap_comp {X X' X'' Y Y' Y'' : Marked.{u}}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    prodMap (f ≫ f') (g ≫ g') = prodMap f g ≫ prodMap f' g' := by
  apply Hom.ext
  ext n a
  rfl

end SSet.Marked
