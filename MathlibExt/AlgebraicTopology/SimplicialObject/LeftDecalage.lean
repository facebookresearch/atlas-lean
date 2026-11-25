/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The whole original one-sided simplicial decalage and both projections

Adjoin one original first vertex to every simplex ordinal. The original
ordinal-sum maps retain all original simplex operators. Restriction to
the right block maps the whole decalage to the original diagram, while
restriction to the first vertex augments it to the original zero degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section

noncomputable section
universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.LeftDecalage

/-- The whole original ordinal map with its distinguished new first vertex retained. -/
def shiftMap {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.mk (n.len + 1) ⟶ SimplexCategory.mk (m.len + 1) :=
  SimplexCategory.Hom.mk
    { toFun := Fin.cases 0 (fun j => (f.toOrderHom j).succ)
      monotone' := by
        intro i j hij
        cases i using Fin.cases with
        | zero => exact Fin.zero_le _
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            have hi : i.val + 1 ≤ 0 := hij
            omega
          | succ j =>
            exact Fin.succ_le_succ_iff.mpr (f.toOrderHom.monotone
              (Fin.succ_le_succ_iff.mp hij)) }

/-- The same original ordinal with one distinguished first vertex adjoined. -/
def ordinal : SimplexCategory ⥤ SimplexCategory where
  obj n := SimplexCategory.mk (n.len + 1)
  map f := shiftMap f
  map_id n := by
    ext i
    cases i using Fin.cases <;> rfl
  map_comp f g := by
    ext i
    cases i using Fin.cases <;> rfl

/-- The entire right block of the original ordinal enters the shifted ordinal. -/
def rightBlock : 𝟭 SimplexCategory ⟶ ordinal where
  app n := SimplexCategory.Hom.mk
    { toFun := Fin.succ
      monotone' := fun _ _ h => Fin.succ_le_succ_iff.mpr h }
  naturality {n m} f := by ext i; rfl

/-- The original first vertex enters every entire shifted ordinal. -/
def firstVertex : (Functor.const SimplexCategory).obj (SimplexCategory.mk 0) ⟶ ordinal where
  app n := SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (n.len + 1)) 0
  naturality {n m} f := by ext i; fin_cases i; rfl

variable {C : Type u} [Category.{v} C]

/-- The whole original shifted simplicial diagram, retaining its original coefficients and
operators. -/
def diagram (W : SimplicialObject C) : SimplicialObject C := ordinal.op ⋙ W

/-- Restriction to the whole original right block projects decalage to the same original diagram. -/
def projection (W : SimplicialObject C) : diagram W ⟶ W where
  app n := W.map (rightBlock.app n.unop).op
  naturality {n m} f := by
    change W.map (ordinal.map f.unop).op ≫ W.map (rightBlock.app m.unop).op =
      W.map (rightBlock.app n.unop).op ≫ W.map f
    rw [← W.map_comp, ← W.map_comp]
    apply congrArg W.map
    apply Quiver.Hom.unop_inj
    exact (rightBlock.naturality f.unop).symm

/-- The whole shifted diagram is augmented by its actual original first vertex. -/
def augmentation (W : SimplicialObject C) : diagram W ⟶
    (SimplicialObject.const C).obj (W.obj (op (SimplexCategory.mk 0))) where
  app n := W.map (firstVertex.app n.unop).op
  naturality {n m} f := by
    change W.map (ordinal.map f.unop).op ≫ W.map (firstVertex.app m.unop).op =
      W.map (firstVertex.app n.unop).op ≫ 𝟙 _
    rw [Category.comp_id, ← W.map_comp]
    apply congrArg W.map
    apply Quiver.Hom.unop_inj
    have h := firstVertex.naturality f.unop
    change 𝟙 (SimplexCategory.mk 0) ≫ firstVertex.app n.unop =
      firstVertex.app m.unop ≫ ordinal.map f.unop at h
    change firstVertex.app m.unop ≫ ordinal.map f.unop = firstVertex.app n.unop
    simpa only [Category.id_comp] using h.symm

/-- The original augmented decalage retains all coefficients and its whole first-vertex
augmentation. -/
def augmented (W : SimplicialObject C) : SimplicialObject.Augmented C where
  left := diagram W
  right := W.obj (op (SimplexCategory.mk 0))
  hom := augmentation W

end CategoryTheory.SimplicialObject.LeftDecalage
