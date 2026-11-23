/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentHSpace
public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentSpace
public import MathlibExt.Topology.Category.CGWH.OrdinaryHSpaceOfWeakUnits
public import MathlibExt.Topology.Homotopy.HSpacePointRelativeTransfer

/-!
# An ordinary H-space on the original additive zero component

The original native zero-component multiplication and its two coherent
weak units give a strict, point-relative operation before ordinary-product
transport. The genuine CW product inverse is derived from the actual
realized points. The canonical native-to-ordinary Iso retains the literal
zeroSpace and zeroSpacePoint. No operation, weak map, model or unit family
is supplied by the caller.
-/

noncomputable section

open CategoryTheory Limits ZeroObject HomotopicalAlgebra
open scoped Simplicial ContinuousMap TopCat.modelCategory

universe u

namespace CategoryTheory.SInverseS.ComponentTranslation

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private abbrev nativeZero : CGWH.{u, u} := zeroComponentClassifyingSpace.{u} C

private def originalZeroIso : (nativeZero C).toTop ≅ zeroSpace (C := C) :=
  classifyingSpaceCGWHToTopIso.{u, u, u}.app (Cat.of (ZeroComponent (C := C)))

private theorem originalZeroIso_point :
    (originalZeroIso C).hom (zeroComponentBasepoint.{u} C) = zeroSpacePoint (C := C) :=
  (classifyingSpaceCGWHPoint_toTop.{u, u, u}
    (zeroComponentBaseObject (C := C))).trans
      (zeroSpacePoint_eq_realizedVertex (C := C)).symm

private theorem originalZeroIso_inv_point :
    (originalZeroIso C).inv (zeroSpacePoint (C := C)) = zeroComponentBasepoint.{u} C :=
  (congrArg (originalZeroIso C).inv (originalZeroIso_point C)).symm.trans
    (ConcreteCategory.congr_hom (originalZeroIso C).hom_inv_id _)

/-- The original ordinary pair chart of the native zero-component product.
Both factor maps are the original canonical realization Iso. -/
public def ordinaryZeroProductComparison :
    C((zeroComponentClassifyingSpace.{u} C ⨯ zeroComponentClassifyingSpace.{u} C :
      CGWH.{u, u}), zeroSpace (C := C) × zeroSpace (C := C)) :=
  ((originalZeroIso C).hom.hom.prodMap (originalZeroIso C).hom.hom).comp
    (CGWH.prodComparisonToTop (nativeZero C) (nativeZero C)).hom

/-- The actual original native biproduct multiplication followed by the
same ordinary realization map. This is the source operation, not a desired
ordinary-product multiplication assumed in the H-space theorem. -/
public def ordinaryZeroOriginalNativeMul :
    C((zeroComponentClassifyingSpace.{u} C ⨯ zeroComponentClassifyingSpace.{u} C :
      CGWH.{u, u}), zeroSpace (C := C)) :=
  (originalZeroIso C).hom.hom.comp
    (CGWH.cgwhToTop.map (zeroComponentClassifyingSpaceMul.{u} C)).hom

private theorem ordinaryZeroProductComparison_recipeComputed :
    ordinaryZeroProductComparison C =
      (((classifyingSpaceCGWHToTopIso.{u, u, u}.app
          (Cat.of (ZeroComponent (C := C)))).hom.hom).prodMap
        (classifyingSpaceCGWHToTopIso.{u, u, u}.app
          (Cat.of (ZeroComponent (C := C)))).hom.hom).comp
        (CGWH.prodComparisonToTop (zeroComponentClassifyingSpace.{u} C)
          (zeroComponentClassifyingSpace.{u} C)).hom := rfl

/-- The legacy pair chart is the actual product of the canonical realization maps. -/
public theorem ordinaryZeroProductComparison_recipe :
    ordinaryZeroProductComparison C =
      (((classifyingSpaceCGWHToTopIso.{u, u, u}.app
          (Cat.of (ZeroComponent (C := C)))).hom.hom).prodMap
        (classifyingSpaceCGWHToTopIso.{u, u, u}.app
          (Cat.of (ZeroComponent (C := C)))).hom.hom).comp
        (CGWH.prodComparisonToTop (zeroComponentClassifyingSpace.{u} C)
          (zeroComponentClassifyingSpace.{u} C)).hom :=
  ordinaryZeroProductComparison_recipeComputed C

private theorem ordinaryZeroOriginalNativeMul_recipeComputed :
    ordinaryZeroOriginalNativeMul C =
      (classifyingSpaceCGWHToTopIso.{u, u, u}.app
        (Cat.of (ZeroComponent (C := C)))).hom.hom.comp
        (CGWH.cgwhToTop.map (zeroComponentClassifyingSpaceMul.{u} C)).hom := rfl

/-- The legacy source operation follows the same canonical zero realization map. -/
public theorem ordinaryZeroOriginalNativeMul_recipe :
    ordinaryZeroOriginalNativeMul C =
      (classifyingSpaceCGWHToTopIso.{u, u, u}.app
        (Cat.of (ZeroComponent (C := C)))).hom.hom.comp
        (CGWH.cgwhToTop.map (zeroComponentClassifyingSpaceMul.{u} C)).hom :=
  ordinaryZeroOriginalNativeMul_recipeComputed C

private theorem ordinaryZeroProductComparisonHomotopyEquiv_exists :
    ∃ E : ContinuousMap.HomotopyEquiv
        (zeroComponentClassifyingSpace.{u} C ⨯ zeroComponentClassifyingSpace.{u} C : CGWH.{u, u})
        (zeroSpace (C := C) × zeroSpace (C := C)),
      E.toFun = ordinaryZeroProductComparison C := by
  let M := nativeZero C
  let z := zeroSpacePoint (C := C)
  let e := zeroComponentBasepoint.{u} C
  let K : SSet.{u} := nerve (ZeroComponent (C := C))
  let v := ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))
  let d := originalZeroIso C
  letI : Cofibration (TopCat.const z : TopCat.of PUnit.{u + 1} ⟶ zeroSpace (C := C)) := by
    have hz : z = SSet.realizedVertex v := zeroSpacePoint_eq_realizedVertex (C := C)
    rw [hz]
    exact SSet.realizedVertex_pointMap_cofibration K v
  letI : Cofibration (TopCat.const e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) := by
    have hi : (TopCat.const e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) =
        TopCat.const z ≫ d.inv := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      exact (originalZeroIso_inv_point C).symm
    rw [hi]
    infer_instance
  obtain ⟨E, hE, _, _, _⟩ :=
    CGWH.prodComparisonToTop_homotopyEquiv_of_cofibrant_points M M e e
  let h := TopCat.homeoOfIso d
  refine ⟨E.trans (h.prodCongr h).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  intro p
  change (h (E.toFun p).1, h (E.toFun p).2) = ordinaryZeroProductComparison C p
  rw [hE]
  rfl

/-- Actual point cofibrations give the legacy pair chart its genuine homotopy inverse. -/
public def ordinaryZeroProductComparisonHomotopyEquiv :
    { E : ContinuousMap.HomotopyEquiv
        (zeroComponentClassifyingSpace.{u} C ⨯ zeroComponentClassifyingSpace.{u} C : CGWH.{u, u})
        (zeroSpace (C := C) × zeroSpace (C := C)) //
      E.toFun = ordinaryZeroProductComparison C } :=
  ⟨Classical.choose (ordinaryZeroProductComparisonHomotopyEquiv_exists C),
    Classical.choose_spec (ordinaryZeroProductComparisonHomotopyEquiv_exists C)⟩

/-- The SAME ordinary zero component has a derived H-space whose unit is
its literal zeroSpacePoint. Both whole unit families are singleton-relative,
and the operation retains the complete original native source homotopy. -/
public theorem ordinaryZeroHSpace_exists :
    ∃ D : HSpace (zeroSpace (C := C)), D.e = zeroSpacePoint (C := C) ∧
      Nonempty (ContinuousMap.Homotopy
        (D.hmul.comp (ordinaryZeroProductComparison C))
        (ordinaryZeroOriginalNativeMul C)) := by
  let M := nativeZero C
  let z := zeroSpacePoint (C := C)
  let e := zeroComponentBasepoint.{u} C
  let K : SSet.{u} := nerve (ZeroComponent (C := C))
  let v := ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))
  let d := originalZeroIso C
  letI : Cofibration (TopCat.const z : TopCat.of PUnit.{u + 1} ⟶ zeroSpace (C := C)) := by
    have hz : z = SSet.realizedVertex v := zeroSpacePoint_eq_realizedVertex (C := C)
    rw [hz]
    exact SSet.realizedVertex_pointMap_cofibration K v
  letI : Cofibration (TopCat.const e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) := by
    have hi : (TopCat.const e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) =
        TopCat.const z ≫ d.inv := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      exact (originalZeroIso_inv_point C).symm
    rw [hi]
    infer_instance
  letI : Cofibration (TopCat.const (CGWH.prodPoint M M e e) :
      TopCat.of PUnit.{u + 1} ⟶ (M ⨯ M).toTop) := by
    change Cofibration (TopCat.const
      (CGWH.prodPoint (SSet.toCGWH.{u, u}.obj K) (SSet.toCGWH.{u, u}.obj K)
        (SSet.realizedVertex v) (SSet.realizedVertex v)) :
      TopCat.of PUnit.{u + 1} ⟶
        ((SSet.toCGWH.{u, u}.obj K) ⨯ (SSet.toCGWH.{u, u}.obj K)).toTop)
    exact CGWH.realizedProductPoint_cofibration K K v v
  let W := zeroComponentClassifyingSpaceWeakHSpaceData.{u} C
  letI : Cofibration (TopCat.const W.e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) := by
    rw [zeroComponentClassifyingSpaceWeakHSpaceData_e]
    infer_instance
  letI : Cofibration (TopCat.const (CGWH.prodPoint M M W.e W.e) :
      TopCat.of PUnit.{u + 1} ⟶ (M ⨯ M).toTop) := by
    rw [zeroComponentClassifyingSpaceWeakHSpaceData_e]
    infer_instance
  obtain ⟨H, hH, ⟨T⟩⟩ := CGWH.WeakHSpaceData.exists_ordinaryHSpace_of_cofibrant_points M W
  have hHe : H.e = e := hH.trans (zeroComponentClassifyingSpaceWeakHSpaceData_e C)
  let h : M ≃ₜ zeroSpace (C := C) := TopCat.homeoOfIso d
  let E := h.toHomotopyEquiv
  have hp : E.toFun H.e = z :=
    (congrArg h hHe).trans (originalZeroIso_point C)
  have hL : E.invFun.comp E.toFun = ContinuousMap.id M := by
    apply ContinuousMap.ext
    intro a
    exact h.symm_apply_apply a
  have hR : E.toFun.comp E.invFun = ContinuousMap.id (zeroSpace (C := C)) := by
    apply ContinuousMap.ext
    intro a
    exact h.apply_symm_apply a
  let LX : ContinuousMap.HomotopyRel (E.invFun.comp E.toFun)
      (ContinuousMap.id M) {H.e} := (ContinuousMap.HomotopyRel.refl _ _).cast hL.symm rfl
  let RY : ContinuousMap.HomotopyRel (E.toFun.comp E.invFun)
      (ContinuousMap.id (zeroSpace (C := C))) {z} :=
    (ContinuousMap.HomotopyRel.refl _ _).cast hR.symm rfl
  let D := E.pointRelativeHSpaceTransfer H z hp LX RY
  have hD : D.val.hmul.comp (ordinaryZeroProductComparison C) =
      E.toFun.comp (H.hmul.comp (CGWH.prodComparisonToTop M M).hom) := by
    rw [D.property.2]
    apply ContinuousMap.ext
    intro a
    apply congrArg E.toFun
    apply congrArg H.hmul
    exact Prod.ext (h.symm_apply_apply ((CGWH.prodComparisonToTop M M) a).1)
      (h.symm_apply_apply ((CGWH.prodComparisonToTop M M) a).2)
  have hμ : E.toFun.comp (CGWH.cgwhToTop.map W.mul).hom =
      ordinaryZeroOriginalNativeMul C :=
    congrArg (fun m => E.toFun.comp (CGWH.cgwhToTop.map m).hom)
      (zeroComponentClassifyingSpaceWeakHSpaceData_mul C)
  let TO := ((ContinuousMap.Homotopy.refl E.toFun).comp T).cast hD.symm hμ
  exact ⟨D.val, D.property.1, ⟨TO⟩⟩

/-- A chosen derived ordinary H-space on the original zero component.
Its subtype property is the literal original unit equation. -/
public def ordinaryZeroHSpace :
    { D : HSpace (zeroSpace (C := C)) // D.e = zeroSpacePoint (C := C) } :=
  ⟨Classical.choose (ordinaryZeroHSpace_exists C),
    (Classical.choose_spec (ordinaryZeroHSpace_exists C)).1⟩

/-- The chosen operation retains the same original native multiplication
up to the complete continuous source homotopy. -/
public theorem ordinaryZeroHSpace_native_source_homotopy :
    Nonempty (ContinuousMap.Homotopy
      ((ordinaryZeroHSpace C).val.hmul.comp (ordinaryZeroProductComparison C))
      (ordinaryZeroOriginalNativeMul C)) :=
  (Classical.choose_spec (ordinaryZeroHSpace_exists C)).2

end CategoryTheory.SInverseS.ComponentTranslation

end
