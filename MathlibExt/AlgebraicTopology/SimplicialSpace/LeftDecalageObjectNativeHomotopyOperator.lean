/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeHomotopyFaces

/-!
# Original ordinal operators of the native contraction homotopy faces

Every native homotopy face retains the original shifted face iterate,
actual original first degeneracy and original shifted degeneracy iterate.
This is a whole original map equality on the first pullback leg.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original ordinal operator underlying one whole contraction homotopy face. -/
def nativeHomotopyOrdinal (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.mk (n + 2) ⟶ SimplexCategory.mk (n + 1) :=
  SimplicialObject.LeftDecalage.ordinal.map
      (SimplexCategory.σ₀Iter i.val (by simp; omega)) ≫
    SimplexCategory.σ (0 : Fin (i.rev.val + 2)) ≫
      SimplicialObject.LeftDecalage.ordinal.map
        (SimplexCategory.δ₀Iter i.val (by simp; omega))

set_option backward.isDefEq.respectTransparency false in
/-- The whole original native homotopy face retains its literal original ordinal operator. -/
theorem nativeHomotopyFace_fst (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (i : Fin (n + 1)) :
    (extraDegeneracy W x).homotopy.h i ≫
        (toDecalage W x).app (op (SimplexCategory.mk (n + 1))) =
      (toDecalage W x).app (op (SimplexCategory.mk n)) ≫ W.diagram.map (nativeHomotopyOrdinal n i).op := by
  rw [SimplicialObject.Augmented.ExtraDegeneracy.homotopy_h]
  simp only [SimplicialObject.Augmented.ExtraDegeneracy.homotopy.h,
    SimplicialObject.δ₀Iter, SimplicialObject.σ₀Iter]
  have he := SimplicialObject.Augmented.ExtraDegeneracy.baseChangeExtraMap_fst
    (ed := SimplicialObject.LeftDecalage.extraDegeneracy W.diagram)
    (p := SSet.yonedaEquiv.symm x) i.rev.val
  change (extraDegeneracy W x).s i.rev.val ≫
      (toDecalage W x).app (op (SimplexCategory.mk (i.rev.val + 1))) =
    (toDecalage W x).app (op (SimplexCategory.mk i.rev.val)) ≫
      W.diagram.map (SimplexCategory.σ (0 : Fin (i.rev.val + 2))).op at he
  change (diagram W x).map (SimplexCategory.δ₀Iter i.val (by simp [Fin.val_rev]; omega)).op ≫
    (extraDegeneracy W x).s i.rev.val ≫
      (diagram W x).map (SimplexCategory.σ₀Iter i.val (by simp [Fin.val_rev]; omega)).op ≫
        (toDecalage W x).app (op (SimplexCategory.mk (n + 1))) = _
  let s : (diagram W x).obj (op (SimplexCategory.mk i.rev.val)) ⟶
      (diagram W x).obj (op (SimplexCategory.mk (i.rev.val + 1))) := (extraDegeneracy W x).s i.rev.val
  change s ≫ (toDecalage W x).app (op (SimplexCategory.mk (i.rev.val + 1))) =
    (toDecalage W x).app (op (SimplexCategory.mk i.rev.val)) ≫
      W.diagram.map (SimplexCategory.σ (0 : Fin (i.rev.val + 2))).op at he
  change (diagram W x).map (SimplexCategory.δ₀Iter i.val (by simp [Fin.val_rev]; omega)).op ≫
    s ≫ (diagram W x).map (SimplexCategory.σ₀Iter i.val (by simp [Fin.val_rev]; omega)).op ≫
      (toDecalage W x).app (op (SimplexCategory.mk (n + 1))) = _
  rw [(toDecalage W x).naturality]
  dsimp only [nativeHomotopyOrdinal]
  have hex := congrArg (fun q => (diagram W x).map
      (SimplexCategory.δ₀Iter i.val (n := i.rev.val) (m := n) (by simp [Fin.val_rev]; omega)).op ≫ q ≫
      (SimplicialObject.LeftDecalage.diagram W.diagram).map
        (SimplexCategory.σ₀Iter i.val (n := i.rev.val + 1) (m := n + 1)
          (by simp [Fin.val_rev]; omega)).op) he
  simp only [Category.assoc] at hex
  rw [hex]
  rw [← Category.assoc, (toDecalage W x).naturality]
  change (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
    W.diagram.map (SimplicialObject.LeftDecalage.ordinal.map
      (SimplexCategory.δ₀Iter i.val (n := i.rev.val) (m := n) (by simp [Fin.val_rev]; omega))).op ≫
      W.diagram.map (SimplexCategory.σ (0 : Fin (i.rev.val + 2))).op ≫
      W.diagram.map (SimplicialObject.LeftDecalage.ordinal.map
        (SimplexCategory.σ₀Iter i.val (n := i.rev.val + 1) (m := n + 1)
          (by simp [Fin.val_rev]; omega))).op = _
  rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp]
  congr 2

end SimplicialSpace.LeftDecalageObject
