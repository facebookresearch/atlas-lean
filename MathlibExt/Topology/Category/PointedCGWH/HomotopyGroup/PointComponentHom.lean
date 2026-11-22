/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHomotopyGroupInvariance
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
import MathlibExt.CategoryTheory.Monoidal.Pointed.Free
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup
import MathlibExt.Topology.Category.CGWH.Point
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHTimeEndpoint
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHornIntervalAction

/-!
# Path components and actual localized point morphisms

The original path-component functor descends to the native CGWH homotopy
category. A real path factors the two original point maps through the
native interval. Its weak projection identifies those maps after localization.
The fundamental lemma and evaluation on the point give both inverse functions,
naturally in the original target map. The original free-point Quillen
adjunction supplies the pointed version on the same underlying path classes.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory CGWH.limits

namespace PointedCGWH.PointComponentHom

attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant
  CGWH.modelCategory.allObjectsFibrant

/-- The original path-component functor inverts every native weak equivalence. -/
theorem piZero_inverts :
    (weakEquivalences CGWH.{u, v}).IsInvertedBy CGWH.piZeroFunctor := by
  intro X Y f hf
  apply (isIso_iff_bijective _).mpr
  exact (CGWH.piZeroEquivOfWeakEquivalence f
    ((HomotopicalAlgebra.weakEquivalence_iff f).mpr hf)).bijective

/-- Its actual lift retains all path-component functions. -/
def piZeroHo : HomotopyCategory CGWH.{u, v} ⥤ Type v :=
  Localization.Construction.lift CGWH.piZeroFunctor piZero_inverts

/-- Every projected original map remains its exact path-component map. -/
theorem piZeroHo_map {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    piZeroHo.map ((toHomotopyCategory CGWH.{u, v}).map f) = ↾(CGWH.piZeroMap f) := by
  have h := Functor.congr_hom
    (Localization.Construction.fac CGWH.piZeroFunctor piZero_inverts) f
  apply ConcreteCategory.hom_ext
  intro x
  have hx := ConcreteCategory.congr_hom h x
  exact hx

/-- Free pointing and its actual Quillen adjunction give the original Ho Hom functions. -/
def freePointHoHom (Y : PointedCGWH.{u, v}) :
    ((toHomotopyCategory PointedCGWH.{u, v}).obj
       ((Under.costar CGWH.point).obj CGWH.point) ⟶
      (toHomotopyCategory PointedCGWH.{u, v}).obj Y) ≃
    ((toHomotopyCategory CGWH.{u, v}).obj CGWH.point ⟶
      (toHomotopyCategory CGWH.{u, v}).obj Y.right) := by
  letI : IsCofibrant CGWH.point.{u, v} := CGWH.point_isCofibrant
  letI : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  exact QuillenOrdinaryHoHom.homEquiv (Under.costarAdjForget CGWH.point)
    CGWH.point Y


private abbrev H := toHomotopyCategory CGWH.{u, v}

/-- The actual native point map associated with a point. -/
def pointMap (X : CGWH.{u, v}) (x : X) : CGWH.point ⟶ X :=
  (CGWH.pointHomEquiv X).symm x

/-- A real path identifies its two original point maps after localization. -/
theorem pointMap_eq_of_joined (X : CGWH.{u, v}) {x y : X} (h : Joined x y) :
    H.map (pointMap X x) = H.map (pointMap X y) := by
  obtain ⟨p⟩ := h
  let hP : IsTerminal (𝟙_ CGWH.{u, v}) := CartesianMonoidalCategory.isTerminalTensorUnit
  let e : CGWH.point.{u, v} ≅ 𝟙_ CGWH := CGWH.point_isTerminal.uniqueUpToIso hP
  let e₀ : CGWH.point.{u, v} ⟶ CGWH.homotopyInterval :=
    e.hom ≫ CGWH.homotopyIntervalEndpoint 0
  let e₁ : CGWH.point.{u, v} ⟶ CGWH.homotopyInterval :=
    e.hom ≫ CGWH.homotopyIntervalEndpoint 1
  let r : CGWH.homotopyInterval.{u, v} ⟶ CGWH.point := CGWH.point_isTerminal.from _
  have h₀ : e₀ ≫ r = 𝟙 CGWH.point := CGWH.point_isTerminal.hom_ext _ _
  have h₁ : e₁ ≫ r = 𝟙 CGWH.point := CGWH.point_isTerminal.hom_ext _ _
  have he₀ : weakEquivalences CGWH.{u, v} e₀ :=
    (weakEquivalences CGWH.{u, v}).comp_mem _ _ (mem_weakEquivalences e.hom)
      CGWH.TimeEndpoint.endpoint_zero_trivialCofibration.2
  have hr : weakEquivalences CGWH.{u, v} r :=
    (weakEquivalences CGWH.{u, v}).of_precomp e₀ r he₀
      (h₀.symm ▸ mem_weakEquivalences (𝟙 CGWH.point))
  let _ : IsIso (H.map r) := Localization.inverts H (weakEquivalences CGWH) r hr
  have he : H.map e₀ = H.map e₁ := by
    apply (cancel_mono (H.map r)).mp
    rw [← H.map_comp, ← H.map_comp, h₀, h₁]
  let raw : CGWH.cgwhToTop.obj CGWH.homotopyInterval.{u, v} ⟶ CGWH.cgwhToTop.obj X :=
    TopCat.ofHom
      ⟨fun t => p (TopCat.I.homeomorph t), p.continuous.comp TopCat.I.homeomorph.continuous⟩
  let a : CGWH.homotopyInterval.{u, v} ⟶ X :=
    CGWH.fullyFaithfulCgwhToTop.preimage raw
  have ha : CGWH.cgwhToTop.map a = raw :=
    CGWH.fullyFaithfulCgwhToTop.map_preimage raw
  have ha₀ : e₀ ≫ a = pointMap X x := by
    apply CGWH.fullyFaithfulCgwhToTop.map_injective
    rw [Functor.map_comp]
    rw [ha]
    apply TopCat.ext
    intro z
    change p (TopCat.I.homeomorph ((CGWH.cgwhToTop.map e₀) z)) = x
    have hz : TopCat.I.homeomorph ((CGWH.cgwhToTop.map e₀) z) = 0 := by
      rfl
    rw [hz, p.source]
  have ha₁ : e₁ ≫ a = pointMap X y := by
    apply CGWH.fullyFaithfulCgwhToTop.map_injective
    rw [Functor.map_comp]
    rw [ha]
    apply TopCat.ext
    intro z
    change p (TopCat.I.homeomorph ((CGWH.cgwhToTop.map e₁) z)) = y
    have hz : TopCat.I.homeomorph ((CGWH.cgwhToTop.map e₁) z) = 1 := by
      rfl
    rw [hz, p.target]
  calc
    H.map (pointMap X x) = H.map e₀ ≫ H.map a :=
      (H.congr_map ha₀.symm).trans (H.map_comp e₀ a)
    _ = H.map e₁ ≫ H.map a := congrArg (fun f => f ≫ H.map a) he
    _ = H.map (pointMap X y) :=
      (H.map_comp e₁ a).symm.trans (H.congr_map ha₁)


/-- Actual path classes map to their localized original point functions. -/
def pointClassToHom (X : CGWH.{u, v}) :
    CGWH.piZero X → (H.obj CGWH.point ⟶ H.obj X) :=
  ZerothHomotopy.lift (fun x => H.map (pointMap X x))
    (fun _ _ h => pointMap_eq_of_joined X ⟨h⟩)

/-- The actual inverse evaluates the lifted component functor at the unique point class. -/
def homToPointClass (X : CGWH.{u, v}) (f : H.obj CGWH.point ⟶ H.obj X) :
    CGWH.piZero X :=
  piZeroHo.map f (ZerothHomotopy.mk (PUnit.unit : CGWH.point.{u, v}))

/-- Each literal original point function evaluates to its original path class. -/
theorem homToPointClass_map (X : CGWH.{u, v}) (f : CGWH.point ⟶ X) :
    homToPointClass X (H.map f) = ZerothHomotopy.mk (CGWH.pointHomEquiv X f) := by
  rw [homToPointClass, piZeroHo_map]
  rfl

/-- The actual two functions return every original path class. -/
theorem homToPointClass_pointClassToHom (X : CGWH.{u, v}) (x : CGWH.piZero X) :
    homToPointClass X (pointClassToHom X x) = x := by
  induction x using ZerothHomotopy.rec with
  | _ x =>
    change homToPointClass X (H.map (pointMap X x)) = ZerothHomotopy.mk x
    rw [homToPointClass_map]
    rfl

/-- The original fundamental lemma and point evaluation return every localized point arrow. -/
theorem pointClassToHom_homToPointClass (X : CGWH.{u, v})
    (f : H.obj CGWH.point ⟶ H.obj X) :
    pointClassToHom X (homToPointClass X f) = f := by
  let _ : IsCofibrant CGWH.point.{u, v} := CGWH.point_isCofibrant
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization H CGWH.point X f
  rw [homToPointClass_map]
  change H.map (pointMap X (CGWH.pointHomEquiv X f)) = H.map f
  exact H.congr_map ((CGWH.pointHomEquiv X).symm_apply_apply f)

/-- The full original path-component and localized point-Hom correspondence. -/
def pointClassHomEquiv (X : CGWH.{u, v}) :
    CGWH.piZero X ≃ (H.obj CGWH.point ⟶ H.obj X) where
  toFun := pointClassToHom X
  invFun := homToPointClass X
  left_inv := homToPointClass_pointClassToHom X
  right_inv := pointClassToHom_homToPointClass X


/-- The entire correspondence is natural in each original target map. -/
theorem pointClassHomEquiv_naturality {X Y : CGWH.{u, v}} (f : X ⟶ Y)
    (x : CGWH.piZero X) :
    pointClassHomEquiv Y (CGWH.piZeroMap f x) =
      pointClassHomEquiv X x ≫ H.map f := by
  induction x using ZerothHomotopy.rec with
  | _ x =>
    change H.map (pointMap Y (f x)) = H.map (pointMap X x) ≫ H.map f
    rw [← H.map_comp]
    apply H.congr_map
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- Both complete inverse functions retain the original target map. -/
theorem pointClassHomEquiv_inverse_naturality {X Y : CGWH.{u, v}} (f : X ⟶ Y)
    (g : H.obj CGWH.point ⟶ H.obj X) :
    (pointClassHomEquiv Y).symm (g ≫ H.map f) =
      CGWH.piZeroMap f ((pointClassHomEquiv X).symm g) := by
  apply (pointClassHomEquiv Y).injective
  rw [Equiv.apply_symm_apply, pointClassHomEquiv_naturality, Equiv.apply_symm_apply]

/-- The original freely based point is the source of the complete pointed component Hom. -/
def pointedPointClassHomEquiv (Y : PointedCGWH.{u, v}) :
    CGWH.piZero Y.right ≃
    ((toHomotopyCategory PointedCGWH.{u, v}).obj
       ((Under.costar CGWH.point).obj CGWH.point) ⟶
      (toHomotopyCategory PointedCGWH.{u, v}).obj Y) :=
  (pointClassHomEquiv Y.right).trans (freePointHoHom Y).symm

/-- Both full pointed correspondence functions retain every original target map. -/
theorem pointedPointClassHomEquiv_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (x : CGWH.piZero X.right) :
    pointedPointClassHomEquiv Y (CGWH.piZeroMap f.right x) =
      pointedPointClassHomEquiv X x ≫ (toHomotopyCategory PointedCGWH).map f := by
  let _ : IsCofibrant CGWH.point.{u, v} := CGWH.point_isCofibrant
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  change (freePointHoHom Y).symm
      (pointClassHomEquiv Y.right (CGWH.piZeroMap f.right x)) =
    (freePointHoHom X).symm (pointClassHomEquiv X.right x) ≫
      (toHomotopyCategory PointedCGWH).map f
  rw [pointClassHomEquiv_naturality]
  exact QuillenOrdinaryHoHom.homEquiv_symm_naturality_right
    (Under.costarAdjForget CGWH.point) CGWH.point (pointClassHomEquiv X.right x) f

/-- The entire pointed inverse commutes with every original map. -/
theorem pointedPointClassHomEquiv_inverse_naturality {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y)
    (g : (toHomotopyCategory PointedCGWH).obj ((Under.costar CGWH.point).obj CGWH.point) ⟶
      (toHomotopyCategory PointedCGWH).obj X) :
    (pointedPointClassHomEquiv Y).symm
        (g ≫ (toHomotopyCategory PointedCGWH).map f) =
      CGWH.piZeroMap f.right ((pointedPointClassHomEquiv X).symm g) := by
  apply (pointedPointClassHomEquiv Y).injective
  rw [Equiv.apply_symm_apply, pointedPointClassHomEquiv_naturality, Equiv.apply_symm_apply]

end PointedCGWH.PointComponentHom
