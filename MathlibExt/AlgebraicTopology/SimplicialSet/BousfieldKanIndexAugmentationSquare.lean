/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexMapULift
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsAugmentation

/-!
# The actual full BK index map and original augmentation square

Every full native elements chain augments by its original first
coefficient. The original coefficient triangle therefore gives the
same entire BK augmentation square after the canonical universe lift.
All original index arrows and scalar operators are retained.
-/

noncomputable section

universe u w vJ vK

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type u} {K : Type (max u w)} [Category.{vJ} J] [Category.{max vJ vK} K]
variable {D : J ⥤ SSet.{max u vJ}} {E : K ⥤ SSet.{max u w vJ vK}}
variable {Z : SSet.{max u vJ}} {T : SSet.{max u w vJ vK}}

/-- The same full original coefficient triangles give the entire actual original BK augmentation square. -/
theorem bkHocolimIndexMapULift_augmentationSquare (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E)
    (τ : D ⟶ (CategoryTheory.Functor.const J).obj Z)
    (υ : E ⟶ (CategoryTheory.Functor.const K).obj T)
    (f : uliftFunctor.{max u w vJ vK,max u vJ}.obj Z ⟶ T)
    (h : ∀ j : J, α.app j ≫ υ.app (Φ.obj j) = uliftFunctor.map (τ.app j) ≫ f) :
    bkHocolimIndexMapULift Φ α ≫ bkAugmentation υ =
      uliftFunctor.{max u w vJ vK,max u vJ}.map (bkAugmentation τ) ≫ f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨x, rfl⟩ := (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) (op ⦋n⦌)).surjective a
  let F := (bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌) x
  let G := ((bkElementsIndexFunctor Φ α (op ⦋n⦌)).mapComposableArrows n).obj F
  let y := (bkHocolimIndexMapULift Φ α).app (op ⦋n⦌)
    (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) (op ⦋n⦌) x)
  have hE := ConcreteCategory.congr_hom (C := Type (max u w vJ vK))
    (NatTrans.congr_app (bkElementsAugmentation_diagonalIso υ) (op ⦋n⦌)) y
  have hD := ConcreteCategory.congr_hom (C := Type (max u vJ))
    (NatTrans.congr_app (bkElementsAugmentation_diagonalIso τ) (op ⦋n⦌)) x
  have hMap := congrArg ((bkElementsAugmentation υ).app (op ⦋n⦌))
    (bkHocolimIndexMapULift_elements Φ α (op ⦋n⦌) x)
  have hSource := (bkElementsAugmentation_chain τ n F).symm.trans hD
  have hCoefficient : (υ.app (G.obj 0).obj).app (op ⦋n⦌) (G.obj 0).val =
      f.app (op ⦋n⦌) (uliftObjEquiv.{max u vJ,max u w vJ vK} Z (op ⦋n⦌)
        ((τ.app (F.obj 0).obj).app (op ⦋n⦌) (F.obj 0).val)) := by
    let z : (uliftFunctor.{max u w vJ vK,max u vJ}.obj (D.obj (F.obj 0).obj)).obj (op ⦋n⦌) :=
      uliftObjEquiv.{max u vJ,max u w vJ vK} (D.obj (F.obj 0).obj) (op ⦋n⦌) (F.obj 0).val
    exact ConcreteCategory.congr_hom (C := Type (max u w vJ vK))
      (NatTrans.congr_app (h (F.obj 0).obj) (op ⦋n⦌)) z
  change (bkAugmentation υ).app (op ⦋n⦌) y =
    f.app (op ⦋n⦌) (uliftObjEquiv.{max u vJ,max u w vJ vK} Z (op ⦋n⦌)
      ((bkAugmentation τ).app (op ⦋n⦌) x))
  exact hE.symm.trans (hMap.trans ((bkElementsAugmentation_chain υ n G).trans
    (hCoefficient.trans (congrArg (fun z : Z.obj (op ⦋n⦌) =>
      f.app (op ⦋n⦌) (uliftObjEquiv.{max u vJ,max u w vJ vK} Z (op ⦋n⦌) z)) hSource))))

end SSet
