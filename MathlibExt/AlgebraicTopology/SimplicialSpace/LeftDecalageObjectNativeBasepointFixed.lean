/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContractionFixed

/-!
# The original native contraction fixes the retained diagonal basepoint

The complete section fixedness equation restricts through the original
constant-diagonal isomorphism. It gives the literal basepoint-times-interval
fixed equation for the actual native contraction cylinder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- The actual original native contraction fixes the complete retained basepoint interval. -/
theorem nativeDiagonalContraction_fixed_basepoint (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (diagonalBasepointMap W x ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ (nativeDiagonalContraction W x).h =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ diagonalBasepointMap W x := by
  have h := nativeDiagonalContraction_fixed_section W x
  have hc := congrArg (fun q =>
    ((SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ q) h
  rw [diagonal_nativeSection] at hc
  have ht : ((SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
      (((SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom ≫ diagonalBasepointMap W x) ⊗ₘ
        𝟙 (Δ[1] : SSet.{u})) = diagonalBasepointMap W x ⊗ₘ 𝟙 (Δ[1] : SSet.{u}) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    have he := types_congr_hom
      (congrArg (fun q => q.app n) (SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv_hom_id) z.1
    change ((SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom).app n
      (((SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv).app n z.1) = z.1 at he
    change ((diagonalBasepointMap W x).app n
      (((SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom).app n
        (((SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv).app n z.1)), z.2) = _
    rw [he]
    rfl
  have hp : ((SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
      CartesianMonoidalCategory.fst
        (SSet.simplicialDiagonalFunctor.obj ((SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u})))
        (Δ[1] : SSet.{u}) =
    CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      (SSet.diagonalConstIso (Δ[0] : SSet.{u})).inv := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  have hr := congrArg (fun q => q ≫ (SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom ≫
    diagonalBasepointMap W x) hp
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hr
  have hl := congrArg (fun q => q ≫ (nativeDiagonalContraction W x).h) ht
  simp only [Category.assoc] at hl
  exact hl.symm.trans (hc.trans hr)

end SimplicialSpace.LeftDecalageObject
