/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeSectionExtra

/-!
# The original section is fixed by every actual contraction homotopy face

The canonical extra-degeneracy section remains fixed under all original
face iterates, the actual extra map, and all original degeneracy iterates.
This gives the complete face equations for the original contraction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- Every original outer operator retains the same actual complete section. -/
theorem nativeSection_operator (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) {a b : SimplexCategoryᵒᵖ} (q : a ⟶ b) :
    (nativeSection W x).app a ≫ (diagram W x).map q = (nativeSection W x).app b := by
  exact ((nativeSection W x).naturality q).symm.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- Each actual original combinatorial contraction face fixes the entire same section. -/
theorem nativeSection_homotopyFace (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (i : Fin (n + 1)) :
    (nativeSection W x).app (op (SimplexCategory.mk n)) ≫
        (extraDegeneracy W x).homotopy.h i =
      (nativeSection W x).app (op (SimplexCategory.mk (n + 1))) := by
  rw [SimplicialObject.Augmented.ExtraDegeneracy.homotopy_h]
  simp only [SimplicialObject.Augmented.ExtraDegeneracy.homotopy.h,
    SimplicialObject.δ₀Iter, SimplicialObject.σ₀Iter]
  change (nativeSection W x).app (op (SimplexCategory.mk n)) ≫
    ((diagram W x).map (SimplexCategory.δ₀Iter i.val (by simp [Fin.val_rev]; omega)).op ≫
      (extraDegeneracy W x).s i.rev.val ≫
      (diagram W x).map (SimplexCategory.σ₀Iter i.val (by simp [Fin.val_rev]; omega)).op) = _
  rw [← Category.assoc, nativeSection_operator]
  let e : (diagram W x).obj (op (SimplexCategory.mk i.rev.val)) ⟶
      (diagram W x).obj (op (SimplexCategory.mk (i.rev.val + 1))) := (extraDegeneracy W x).s i.rev.val
  have he : (nativeSection W x).app (op (SimplexCategory.mk i.rev.val)) ≫ e =
      (nativeSection W x).app (op (SimplexCategory.mk (i.rev.val + 1))) :=
    nativeSection_extra W x i.rev.val
  change (nativeSection W x).app (op (SimplexCategory.mk i.rev.val)) ≫
    (e ≫ (diagram W x).map (SimplexCategory.σ₀Iter i.val (by simp [Fin.val_rev]; omega)).op) = _
  rw [← Category.assoc, he, nativeSection_operator]

end SimplicialSpace.LeftDecalageObject
