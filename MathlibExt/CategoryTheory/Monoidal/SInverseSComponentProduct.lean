/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentSpace
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentRealization

/-!
# The full native component product of additive S⁻¹S

The maps are the computed ordinary component translations, transported by
the canonical underlying-Top isomorphisms of the existing CGWH realization.
Every original Grothendieck class is retained. Both inverse homotopies are
relative to the specified original zero pair and (0,zero-pair) product point.
The existing zero-component realization isomorphism identifies the same zero
space with the selected simplicial connected-component realization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Algebra
open scoped Simplicial

universe u v w

public section

namespace CategoryTheory.SInverseS.ComponentTranslation

private def conjugateHomotopyRel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {f₀ f₁ : C(X, X)} {x : X}
    (H : ContinuousMap.HomotopyRel f₀ f₁ {x}) :
    ContinuousMap.HomotopyRel
      ((⟨e, e.continuous⟩ : C(X, Y)).comp
        (f₀.comp (⟨e.symm, e.symm.continuous⟩ : C(Y, X))))
      ((⟨e, e.continuous⟩ : C(X, Y)).comp
        (f₁.comp (⟨e.symm, e.symm.continuous⟩ : C(Y, X)))) {e x} where
  toHomotopy := (ContinuousMap.Homotopy.refl (⟨e, e.continuous⟩ : C(X, Y))).comp
    (H.toHomotopy.compContinuousMap (⟨e.symm, e.symm.continuous⟩ : C(Y, X)))
  prop' t y hy := by
    obtain rfl := Set.mem_singleton_iff.mp hy
    change e (H (t, e.symm (e x))) = e (f₀ (e.symm (e x)))
    rw [e.symm_apply_apply]
    exact congrArg e (H.prop t x (by simp))

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Native class labels retain the ordinary Grothendieck discrete-space topology. -/
local instance nativeGrothendieckTopology :
    TopologicalSpace (GrothendieckAddGroup (Skeleton C)) :=
  (grothendieckDiscreteSpace (C := C)).str

/-- The existing canonical native classifying space, with no replacement model. -/
abbrev nativeOriginalSpace := CGWH.cgwhToTop.{w, max u v}.obj (classifyingSpace.{w} C)

/-- The existing canonical native zero-component classifying space. -/
abbrev nativeZeroSpace := CGWH.cgwhToTop.{w, max u v}.obj (zeroComponentClassifyingSpace.{w} C)

/-- The full original Grothendieck-discrete product with the same native zero component. -/
abbrev nativeProductSpace : TopCat.{max u v} :=
  TopCat.of (GrothendieckAddGroup (Skeleton C) × (nativeZeroSpace.{u, v, w} (C := C)))

/-- The actual native point represented by the original pair (0,0). -/
def nativeOriginalPoint : (nativeOriginalSpace.{u, v, w} (C := C)) :=
  classifyingSpaceCGWHPoint.{w} (⟨0, 0⟩ : Pair C)

/-- The actual native zero-component point represented by that same zero pair. -/
def nativeZeroPoint : (nativeZeroSpace.{u, v, w} (C := C)) :=
  classifyingSpaceCGWHPoint.{w} (zeroComponentBaseObject (C := C))

private theorem nativeOriginalPoint_classifyingSpaceCGWHPoint_computed :
    nativeOriginalPoint.{u, v, w} (C := C) =
      classifyingSpaceCGWHPoint.{w} (⟨0, 0⟩ : Pair C) := rfl

/-- The specified native whole-space point is the literal classifying zero-pair vertex. -/
theorem nativeOriginalPoint_eq_classifyingSpaceCGWHPoint :
    nativeOriginalPoint.{u, v, w} (C := C) =
      classifyingSpaceCGWHPoint.{w} (⟨0, 0⟩ : Pair C) :=
  nativeOriginalPoint_classifyingSpaceCGWHPoint_computed

private theorem nativeZeroPoint_classifyingSpaceCGWHPoint_computed :
    nativeZeroPoint.{u, v, w} (C := C) =
      classifyingSpaceCGWHPoint.{w} (zeroComponentBaseObject (C := C)) := rfl

/-- The specified native zero-component point is the same literal classifying vertex. -/
theorem nativeZeroPoint_eq_classifyingSpaceCGWHPoint :
    nativeZeroPoint.{u, v, w} (C := C) =
      classifyingSpaceCGWHPoint.{w} (zeroComponentBaseObject (C := C)) :=
  nativeZeroPoint_classifyingSpaceCGWHPoint_computed

/-- The specified (0,zero-pair) point of the complete native product. -/
def nativeProductPoint : (nativeProductSpace.{u, v, w} (C := C)) :=
    ⟨0, (nativeZeroPoint.{u, v, w} (C := C))⟩

/-- The existing native-to-ordinary isomorphism on the original whole classifying space. -/
def nativeOriginalRealizationIso : (nativeOriginalSpace.{u, v, w} (C := C)) ≅
    originalSpace (C := C) :=
  classifyingSpaceCGWHToTopIso.{w, max v u, u}.app (Cat.of (Pair C))

/-- The same canonical isomorphism on the original categorical zero component. -/
def nativeZeroRealizationIso : (nativeZeroSpace.{u, v, w} (C := C)) ≅ zeroSpace (C := C) :=
  classifyingSpaceCGWHToTopIso.{w, max v u, u}.app (Cat.of (ZeroComponent (C := C)))

/-- The canonical whole-space comparison preserves the original zero pair. -/
theorem nativeOriginalRealizationIso_point :
    (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
        ((nativeOriginalPoint.{u, v, w} (C := C))) = (originalSpacePoint (C := C)) := by
  have h : (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
      (nativeOriginalPoint.{u, v, w} (C := C)) =
    SSet.realizedVertex (X := CategoryTheory.nerve (Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : Pair C)) :=
    classifyingSpaceCGWHPoint_toTop.{w, max v u, u} (⟨0, 0⟩ : Pair C)
  exact h.trans (originalSpacePoint_eq_realizedVertex (C := C)).symm

/-- Its inverse returns that same actual native point. -/
theorem nativeOriginalRealizationIso_inv_point :
    (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv (originalSpacePoint (C := C)) =
        (nativeOriginalPoint.{u, v, w} (C := C)) := by
  have h := congrArg (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
    ((nativeOriginalRealizationIso_point.{u, v, w} (C := C)))
  exact h.symm.trans (ConcreteCategory.congr_hom
      (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom_inv_id _)

/-- The canonical zero-space comparison preserves the same original unit. -/
theorem nativeZeroRealizationIso_point :
    (nativeZeroRealizationIso.{u, v, w} (C := C)).hom ((nativeZeroPoint.{u, v, w} (C := C))) =
        (zeroSpacePoint (C := C)) := by
  have h : (nativeZeroRealizationIso.{u, v, w} (C := C)).hom
      (nativeZeroPoint.{u, v, w} (C := C)) =
    SSet.realizedVertex (X := CategoryTheory.nerve (ZeroComponent (C := C)))
      (ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))) :=
    classifyingSpaceCGWHPoint_toTop.{w, max v u, u} (zeroComponentBaseObject (C := C))
  exact h.trans (zeroSpacePoint_eq_realizedVertex (C := C)).symm

/-- Its inverse returns the literal original native zero point. -/
theorem nativeZeroRealizationIso_inv_point :
    (nativeZeroRealizationIso.{u, v, w} (C := C)).inv (zeroSpacePoint (C := C)) =
        (nativeZeroPoint.{u, v, w} (C := C)) := by
  have h := congrArg (nativeZeroRealizationIso.{u, v, w} (C := C)).inv
    ((nativeZeroRealizationIso_point.{u, v, w} (C := C)))
  exact h.symm.trans (ConcreteCategory.congr_hom
      (nativeZeroRealizationIso.{u, v, w} (C := C)).hom_inv_id _)

private theorem nativeOriginalRealizationIso_hom_inv_apply (z : originalSpace (C := C)) :
    (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
      ((nativeOriginalRealizationIso.{u, v, w} (C := C)).inv z) = z := by
  have h := ConcreteCategory.congr_hom
    (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv_hom_id z
  change (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
    ((nativeOriginalRealizationIso.{u, v, w} (C := C)).inv z) = z at h
  exact h

private theorem nativeOriginalRealizationIso_inv_hom_apply
    (z : nativeOriginalSpace.{u, v, w} (C := C)) :
    (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
      ((nativeOriginalRealizationIso.{u, v, w} (C := C)).hom z) = z := by
  have h := ConcreteCategory.congr_hom
    (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom_inv_id z
  change (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
    ((nativeOriginalRealizationIso.{u, v, w} (C := C)).hom z) = z at h
  exact h

/-- Only the zero-space factor is changed by its actual canonical native comparison. -/
def nativeProductRealizationHomeomorph :
    componentProductSpace (C := C) ≃ₜ (nativeProductSpace.{u, v, w} (C := C)) :=
  (Homeomorph.refl (GrothendieckAddGroup (Skeleton C))).prodCongr
    (TopCat.homeoOfIso ((nativeZeroRealizationIso.{u, v, w} (C := C)))).symm

private theorem nativeProductRealizationHomeomorph_apply_computation
    (g : GrothendieckAddGroup (Skeleton C)) (z : zeroSpace (C := C)) :
    nativeProductRealizationHomeomorph.{u, v, w} (C := C) (g, z) =
      (g, (nativeZeroRealizationIso.{u, v, w} (C := C)).inv z) := rfl

private theorem nativeProductRealizationHomeomorph_symm_apply_computation
    (g : GrothendieckAddGroup (Skeleton C)) (z : nativeZeroSpace.{u, v, w} (C := C)) :
    (nativeProductRealizationHomeomorph.{u, v, w} (C := C)).symm (g, z) =
      (g, (nativeZeroRealizationIso.{u, v, w} (C := C)).hom z) := rfl

/-- This target comparison fixes the entire group coordinate. -/
theorem nativeProductRealizationHomeomorph_apply
    (g : GrothendieckAddGroup (Skeleton C)) (z : zeroSpace (C := C)) :
    (nativeProductRealizationHomeomorph.{u, v, w} (C := C)) (g, z) =
        (g, (nativeZeroRealizationIso.{u, v, w} (C := C)).inv z) :=
  (nativeProductRealizationHomeomorph_apply_computation.{u, v, w} (C := C)) g z

/-- The same actual comparison preserves the specified product unit. -/
theorem nativeProductRealizationHomeomorph_point :
    (nativeProductRealizationHomeomorph.{u, v, w} (C := C)) (componentProductPoint (C := C)) =
        (nativeProductPoint.{u, v, w} (C := C)) := by
  rw [componentProductPoint_eq_zeroPair (C := C),
    nativeProductRealizationHomeomorph_apply.{u, v, w} (C := C)]
  change ((0 : GrothendieckAddGroup (Skeleton C)),
      (nativeZeroRealizationIso.{u, v, w} (C := C)).inv (zeroSpacePoint (C := C))) =
    ((0 : GrothendieckAddGroup (Skeleton C)), nativeZeroPoint.{u, v, w} (C := C))
  rw [(nativeZeroRealizationIso_inv_point.{u, v, w} (C := C))]

/-- The whole native forward map uses the same original component translations. -/
def nativeProductForward : C((nativeOriginalSpace.{u, v, w} (C := C)),
    (nativeProductSpace.{u, v, w} (C := C))) :=
  (⟨nativeProductRealizationHomeomorph.{u, v, w} (C := C),
    (nativeProductRealizationHomeomorph.{u, v, w} (C := C)).continuous⟩ :
      C(componentProductSpace (C := C), nativeProductSpace.{u, v, w} (C := C))).comp
    ((originalProductForward (C := C)).comp
        (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom.hom)

/-- The whole native inverse retains the same computed inverse translations and original
inclusions. -/
def nativeProductInverse : C((nativeProductSpace.{u, v, w} (C := C)),
    (nativeOriginalSpace.{u, v, w} (C := C))) :=
  (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv.hom.comp
    ((originalProductInverse (C := C)).comp
      (⟨(nativeProductRealizationHomeomorph.{u, v, w} (C := C)).symm,
        (nativeProductRealizationHomeomorph.{u, v, w} (C := C)).symm.continuous⟩ :
          C(nativeProductSpace.{u, v, w} (C := C), componentProductSpace (C := C))))

/-- The native forward map is strictly based at the specified original zero pair. -/
theorem nativeProductForward_point :
    (nativeProductForward.{u, v, w} (C := C)) ((nativeOriginalPoint.{u, v, w} (C := C))) =
        (nativeProductPoint.{u, v, w} (C := C)) := by
  change (nativeProductRealizationHomeomorph.{u, v, w} (C := C))
    ((originalProductForward (C := C)) ((nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
        (nativeOriginalPoint.{u, v, w} (C := C)))) = _
  rw [(nativeOriginalRealizationIso_point.{u, v, w} (C := C)),
      (originalProductForward_point (C := C)),
    (nativeProductRealizationHomeomorph_point.{u, v, w} (C := C))]

/-- The native inverse returns the literal original zero pair. -/
theorem nativeProductInverse_point :
    (nativeProductInverse.{u, v, w} (C := C)) ((nativeProductPoint.{u, v, w} (C := C))) =
        (nativeOriginalPoint.{u, v, w} (C := C)) := by
  have hPoint : (nativeProductRealizationHomeomorph.{u, v, w} (C := C)).symm
      (nativeProductPoint.{u, v, w} (C := C)) =
      componentProductPoint (C := C) := by
    rw [← (nativeProductRealizationHomeomorph_point.{u, v, w} (C := C)),
        Homeomorph.symm_apply_apply]
  change (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
    ((originalProductInverse (C := C)) ((nativeProductRealizationHomeomorph.{u, v, w} (C := C)).symm
        (nativeProductPoint.{u, v, w} (C := C)))) = _
  rw [hPoint, (originalProductInverse_point (C := C)),
      (nativeOriginalRealizationIso_inv_point.{u, v, w} (C := C))]

/-- The first complete native inverse family is relative to the same original zero pair. -/
def nativeProductLeftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((nativeProductInverse.{u, v, w} (C := C)).comp (nativeProductForward.{u, v, w} (C := C)))
      (ContinuousMap.id (nativeOriginalSpace.{u, v, w} (C := C)))
      {nativeOriginalPoint.{u, v, w} (C := C)} := by
  let a := TopCat.homeoOfIso (nativeOriginalRealizationIso.{u, v, w} (C := C))
  let b := nativeProductRealizationHomeomorph.{u, v, w} (C := C)
  let A : C(nativeOriginalSpace.{u, v, w} (C := C), originalSpace (C := C)) :=
    ⟨a, a.continuous⟩
  let Ai : C(originalSpace (C := C), nativeOriginalSpace.{u, v, w} (C := C)) :=
    ⟨a.symm, a.symm.continuous⟩
  let h := conjugateHomotopyRel a.symm (originalProductLeftHomotopyRel (C := C))
  have h₀ : Ai.comp
      (((originalProductInverse (C := C)).comp (originalProductForward (C := C))).comp A) =
        (nativeProductInverse.{u, v, w} (C := C)).comp
          (nativeProductForward.{u, v, w} (C := C)) := by
    apply ContinuousMap.ext
    intro x
    change a.symm (originalProductInverse (C := C) (originalProductForward (C := C) (a x))) =
      a.symm (originalProductInverse (C := C)
        (b.symm (b (originalProductForward (C := C) (a x)))))
    rw [b.symm_apply_apply]
  have h₁ : Ai.comp ((ContinuousMap.id (originalSpace (C := C))).comp A) =
      ContinuousMap.id (nativeOriginalSpace.{u, v, w} (C := C)) := by
    apply ContinuousMap.ext
    intro x
    exact a.symm_apply_apply x
  have hPoint : a.symm (originalSpacePoint (C := C)) =
      nativeOriginalPoint.{u, v, w} (C := C) := by
    change (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
      (originalSpacePoint (C := C)) = _
    exact nativeOriginalRealizationIso_inv_point.{u, v, w} (C := C)
  simpa only [hPoint] using h.cast h₀ h₁

/-- The other complete native inverse family is relative to the specified (0,zero-pair) point. -/
def nativeProductRightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((nativeProductForward.{u, v, w} (C := C)).comp (nativeProductInverse.{u, v, w} (C := C)))
      (ContinuousMap.id (nativeProductSpace.{u, v, w} (C := C)))
      {nativeProductPoint.{u, v, w} (C := C)} := by
  let a := TopCat.homeoOfIso (nativeOriginalRealizationIso.{u, v, w} (C := C))
  let b := nativeProductRealizationHomeomorph.{u, v, w} (C := C)
  let B : C(componentProductSpace (C := C), nativeProductSpace.{u, v, w} (C := C)) :=
    ⟨b, b.continuous⟩
  let Bi : C(nativeProductSpace.{u, v, w} (C := C), componentProductSpace (C := C)) :=
    ⟨b.symm, b.symm.continuous⟩
  let h := conjugateHomotopyRel b (originalProductRightHomotopyRel (C := C))
  have h₀ : B.comp
      (((originalProductForward (C := C)).comp (originalProductInverse (C := C))).comp Bi) =
        (nativeProductForward.{u, v, w} (C := C)).comp
          (nativeProductInverse.{u, v, w} (C := C)) := by
    apply ContinuousMap.ext
    intro x
    change b (originalProductForward (C := C) (originalProductInverse (C := C) (b.symm x))) =
      b (originalProductForward (C := C)
        (a (a.symm (originalProductInverse (C := C) (b.symm x)))))
    rw [a.apply_symm_apply]
  have h₁ : B.comp ((ContinuousMap.id (componentProductSpace (C := C))).comp Bi) =
      ContinuousMap.id (nativeProductSpace.{u, v, w} (C := C)) := by
    apply ContinuousMap.ext
    intro x
    exact b.apply_symm_apply x
  have hPoint : b (componentProductPoint (C := C)) =
      nativeProductPoint.{u, v, w} (C := C) :=
    nativeProductRealizationHomeomorph_point.{u, v, w} (C := C)
  simpa only [hPoint] using h.cast h₀ h₁

/-- The entire canonical native space has the full discrete-group product with both based
families. -/
def nativeProductHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ((nativeOriginalSpace.{u, v, w} (C := C)))
        ((nativeProductSpace.{u, v, w} (C := C))) where
  toFun := (nativeProductForward.{u, v, w} (C := C))
  invFun := (nativeProductInverse.{u, v, w} (C := C))
  left_inv := ⟨(nativeProductLeftHomotopyRel.{u, v, w} (C := C)).toHomotopy⟩
  right_inv := ⟨(nativeProductRightHomotopyRel.{u, v, w} (C := C)).toHomotopy⟩

/-- On every entire original class, the native map has the original class coordinate and
translation. -/
theorem nativeProductForward_class (g : GrothendieckAddGroup (Skeleton C)) (z : componentSpace g) :
    (nativeProductForward.{u, v, w} (C := C))
      ((nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
        (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) z)) =
          (g,
              (nativeZeroRealizationIso.{u, v, w} (C := C)).inv
              ((componentForward (C := C)) g z)) := by
  change (nativeProductRealizationHomeomorph.{u, v, w} (C := C))
    ((originalProductForward (C := C)) ((nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
      ((nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
        (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) z)))) = _
  rw [(nativeOriginalRealizationIso_hom_inv_apply.{u, v, w} (C := C))]
  rw [(originalProductForward_class (C := C)),
      (nativeProductRealizationHomeomorph_apply.{u, v, w} (C := C))]

/-- On every original group label, the native inverse is the same realized original class
inclusion. -/
theorem nativeProductInverse_class (g : GrothendieckAddGroup (Skeleton C))
    (z : (nativeZeroSpace.{u, v, w} (C := C))) :
    (nativeProductInverse.{u, v, w} (C := C)) (g, z) =
        (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι)
        ((componentInverse (C := C)) g ((nativeZeroRealizationIso.{u, v, w} (C := C)).hom z))) := by
  change (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
    (originalProductInverse (C := C)
      ((nativeProductRealizationHomeomorph.{u, v, w} (C := C)).symm (g, z))) = _
  rw [(nativeProductRealizationHomeomorph_symm_apply_computation.{u, v, w} (C := C)),
    originalProductInverse_class (C := C)]

/-- The zero factor is the existing selected connected-component realization. -/
def nativeZeroSelectedComponentIso : (nativeZeroSpace.{u, v, w} (C := C)) ≅
    SSet.toTop.obj (zeroComponentNerveComponent C : SSet) :=
  zeroComponentClassifyingSpaceComponentRealizationTopIso.{w} C

/-- The original native zero-component inclusion, with its actual underlying map. -/
def nativeZeroInclusion : C((nativeZeroSpace.{u, v, w} (C := C)),
    (nativeOriginalSpace.{u, v, w} (C := C))) :=
  (CGWH.cgwhToTop.{w, max u v}.map (zeroComponentClassifyingSpaceInclusion.{w} C)).hom

private theorem nativeZeroInclusionValueComputed :
    (nativeZeroInclusion.{u, v, w} (C := C)) =
      (CGWH.cgwhToTop.{w, max u v}.map
        (zeroComponentClassifyingSpaceInclusion.{w} C)).hom := rfl

/-- The whole original native inclusion is the underlying map of its canonical forgetful image. -/
theorem nativeZeroInclusion_value :
    (nativeZeroInclusion.{u, v, w} (C := C)) =
      (CGWH.cgwhToTop.{w, max u v}.map
        (zeroComponentClassifyingSpaceInclusion.{w} C)).hom :=
  nativeZeroInclusionValueComputed

/-- Canonical native realization retains the entire original zero-inclusion square. -/
theorem nativeZeroInclusion_realization :
    CGWH.cgwhToTop.{w, max u v}.map (zeroComponentClassifyingSpaceInclusion.{w} C) ≫
        (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom =
      (nativeZeroRealizationIso.{u, v, w} (C := C)).hom ≫
        SSet.toTop.map (CategoryTheory.nerveMap (zeroComponentProperty (C := C)).ι) := by
  exact (classifyingSpaceCGWHToTopIso.{w, max v u, u}).hom.naturality
    ((zeroComponentProperty (C := C)).ι).toCatHom

private theorem nativeZeroInclusion_eq :
    (nativeZeroInclusion.{u, v, w} (C := C)) =
        (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv.hom.comp
      (((SSet.toTop.map (CategoryTheory.nerveMap (zeroComponentProperty (C := C)).ι)).hom).comp
        (nativeZeroRealizationIso.{u, v, w} (C := C)).hom.hom) := by
  apply ContinuousMap.ext
  intro z
  have h := ConcreteCategory.congr_hom ((nativeZeroInclusion_realization.{u, v, w} (C := C))) z
  change (nativeOriginalRealizationIso.{u, v, w} (C := C)).hom
      (nativeZeroInclusion.{u, v, w} (C := C) z) =
    SSet.toTop.map (CategoryTheory.nerveMap (zeroComponentProperty (C := C)).ι)
      ((nativeZeroRealizationIso.{u, v, w} (C := C)).hom z) at h
  have h' := congrArg (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv h
  exact ((nativeOriginalRealizationIso_inv_hom_apply.{u, v, w} (C := C))
    (nativeZeroInclusion.{u, v, w} (C := C) z)).symm.trans h'

/-- The original native zero inclusion is an embedding, derived from the same actual canonical
square. -/
theorem nativeZeroInclusion_isEmbedding :
    Topology.IsEmbedding ((nativeZeroInclusion.{u, v, w} (C := C))) := by
  let a := TopCat.homeoOfIso ((nativeOriginalRealizationIso.{u, v, w} (C := C)))
  let b := TopCat.homeoOfIso ((nativeZeroRealizationIso.{u, v, w} (C := C)))
  have h := a.symm.isEmbedding.comp
    ((originalClassInclusion_isEmbedding (C := C) 0).comp b.isEmbedding)
  change Topology.IsEmbedding ((nativeOriginalRealizationIso.{u, v, w} (C := C)).inv.hom.comp
    (((SSet.toTop.map (CategoryTheory.nerveMap (zeroComponentProperty (C := C)).ι)).hom).comp
      (nativeZeroRealizationIso.{u, v, w} (C := C)).hom.hom)) at h
  rw [← (nativeZeroInclusion_eq.{u, v, w} (C := C))] at h
  exact h

/-- The original native zero space has exactly the actual path-component range of the original
unit. -/
theorem nativeZeroInclusion_range_eq_pathComponent :
    Set.range ((nativeZeroInclusion.{u, v, w} (C := C))) =
        pathComponent (nativeOriginalPoint.{u, v, w} (C := C)) := by
  let a := TopCat.homeoOfIso ((nativeOriginalRealizationIso.{u, v, w} (C := C)))
  let b := TopCat.homeoOfIso ((nativeZeroRealizationIso.{u, v, w} (C := C)))
  let F := (SSet.toTop.map (CategoryTheory.nerveMap (zeroComponentProperty (C := C)).ι)).hom
  have hRange : Set.range ((nativeZeroInclusion.{u, v, w} (C := C))) = a.symm '' Set.range F := by
    rw [(nativeZeroInclusion_eq.{u, v, w} (C := C))]
    change Set.range ((a.symm ∘ F) ∘ b) = a.symm '' Set.range F
    rw [Set.range_comp, b.surjective.range_eq, Set.image_univ, Set.range_comp]
  have hPoint : a.symm (originalSpacePoint (C := C)) =
      nativeOriginalPoint.{u, v, w} (C := C) := by
    change (nativeOriginalRealizationIso.{u, v, w} (C := C)).inv
      (originalSpacePoint (C := C)) = _
    exact nativeOriginalRealizationIso_inv_point.{u, v, w} (C := C)
  rw [hRange, (originalZeroClass_range_eq_pathComponent (C := C)),
    a.symm.image_pathComponent, hPoint]

/-- The literal native zero component is homeomorphic to the actual ambient path component. -/
def nativeZeroPathComponentHomeomorph :
    (nativeZeroSpace.{u, v, w} (C := C)) ≃ₜ
        pathComponent ((nativeOriginalPoint.{u, v, w} (C := C))) :=
  (nativeZeroInclusion_isEmbedding.{u, v, w} (C := C)).toHomeomorph.trans
    (Homeomorph.setCongr (nativeZeroInclusion_range_eq_pathComponent.{u, v, w} (C := C)))

private theorem nativeZeroPathComponentHomeomorph_apply_computation
    (z : nativeZeroSpace.{u, v, w} (C := C)) :
    (nativeZeroPathComponentHomeomorph.{u, v, w} (C := C) z :
      nativeOriginalSpace.{u, v, w} (C := C)) = nativeZeroInclusion.{u, v, w} (C := C) z := rfl

/-- This native zero-path-component homeomorphism retains the actual original inclusion. -/
theorem nativeZeroPathComponentHomeomorph_apply (z : (nativeZeroSpace.{u, v, w} (C := C))) :
    ((nativeZeroPathComponentHomeomorph.{u, v, w} (C := C))
        z : (nativeOriginalSpace.{u, v, w} (C := C))) =
      (nativeZeroInclusion.{u, v, w} (C := C)) z :=
  (nativeZeroPathComponentHomeomorph_apply_computation.{u, v, w} (C := C)) z

private theorem nativeZeroInclusion_obj_base :
    (zeroComponentProperty (C := C)).ι.obj (zeroComponentBaseObject (C := C)) =
      (⟨0, 0⟩ : Pair C) := rfl

/-- The native zero inclusion preserves the specified original zero pair. -/
theorem nativeZeroInclusion_point :
    (nativeZeroInclusion.{u, v, w} (C := C)) ((nativeZeroPoint.{u, v, w} (C := C))) =
        (nativeOriginalPoint.{u, v, w} (C := C)) := by
  change (classifyingSpaceCGWH.{w, max v u, u}.map
    ((zeroComponentProperty (C := C)).ι).toCatHom)
      (classifyingSpaceCGWHPoint.{w} (zeroComponentBaseObject (C := C))) =
        classifyingSpaceCGWHPoint.{w} (⟨0, 0⟩ : Pair C)
  exact (classifyingSpaceCGWH_map_point.{w, max v u, u}
    ((zeroComponentProperty (C := C)).ι) (zeroComponentBaseObject (C := C))).trans
      (congrArg (classifyingSpaceCGWHPoint.{w, max v u, u}) (nativeZeroInclusion_obj_base (C := C)))

/-- Its selected path-component point is literally the original (0,0) native point. -/
theorem nativeZeroPathComponentHomeomorph_point :
    (nativeZeroPathComponentHomeomorph.{u, v, w} (C := C)) ((nativeZeroPoint.{u, v, w} (C := C))) =
      ⟨(nativeOriginalPoint.{u, v, w} (C := C)),
          mem_pathComponent_self (nativeOriginalPoint.{u, v, w} (C := C))⟩ := by
  apply Subtype.ext
  rw [(nativeZeroPathComponentHomeomorph_apply.{u, v, w} (C := C)),
      (nativeZeroInclusion_point.{u, v, w} (C := C))]

end CategoryTheory.SInverseS.ComponentTranslation
