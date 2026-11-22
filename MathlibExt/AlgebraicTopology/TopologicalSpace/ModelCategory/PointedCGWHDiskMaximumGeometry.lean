/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
import MathlibExt.Topology.Category.CGWH.PathLanding

/-!
# Maximum on the actual pointed CGWH disk

The interval maximum descends through the original pointed smash presentation.
The disk keeps its selected time-one point, while the freely pointed time-zero
endpoint gives both complete unit equations. These constructions do not depend
on an enriched diagram index or a sequential spectrum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.DiskMaximumGeometry

open MonoidalCategory CartesianMonoidalCategory Topology
open scoped CGWH.limits MonoidalClosed

private instance nativeCartesianBraiding : BraidedCategory CGWH.{u, v} :=
  BraidedCategory.ofCartesianMonoidalCategory
private instance nativeCartesianSymmetry : SymmetricCategory CGWH.{u, v} := inferInstance
private instance nativeInclusionFull : CGWH.cgwhToTop.{u, v}.Full :=
  CGWH.fullyFaithfulCgwhToTop.{u, v}.full
private abbrev I := CGWH.interval.{u, v}

/-- The unchanged realized native interval retains its full ordinary interval coordinate. -/
def intervalCoordinate : C(I.{u, v}, unitInterval) where
  toFun x := TopCat.I.homeomorph.{v} (CGWH.intervalToTopIso.{u, v}.hom x)
  continuous_toFun := TopCat.I.homeomorph.{v}.continuous.comp
    (ConcreteCategory.hom CGWH.intervalToTopIso.{u, v}.hom).continuous

/-- The same original native interval is recovered through both original interval inverse maps. -/
def intervalDecode : C(unitInterval, I.{u, v}) where
  toFun s := CGWH.intervalToTopIso.{u, v}.inv (TopCat.I.homeomorph.{v}.symm s)
  continuous_toFun := (ConcreteCategory.hom CGWH.intervalToTopIso.{u, v}.inv).continuous.comp
    TopCat.I.homeomorph.{v}.symm.continuous

theorem intervalCoordinate_decode (s : unitInterval) :
    intervalCoordinate.{u, v} (intervalDecode.{u, v} s) = s := by
  change TopCat.I.homeomorph.{v} (CGWH.intervalToTopIso.{u, v}.hom
    (CGWH.intervalToTopIso.{u, v}.inv (TopCat.I.homeomorph.{v}.symm s))) = s
  exact (congrArg TopCat.I.homeomorph.{v}
    (ConcreteCategory.congr_hom CGWH.intervalToTopIso.{u, v}.inv_hom_id
      (TopCat.I.homeomorph.{v}.symm s))).trans (TopCat.I.homeomorph.{v}.apply_symm_apply s)

theorem intervalDecode_coordinate (x : I.{u, v}) :
    intervalDecode.{u, v} (intervalCoordinate.{u, v} x) = x := by
  change CGWH.intervalToTopIso.{u, v}.inv (TopCat.I.homeomorph.{v}.symm
    (TopCat.I.homeomorph.{v} (CGWH.intervalToTopIso.{u, v}.hom x))) = x
  rw [Homeomorph.symm_apply_apply]
  exact ConcreteCategory.congr_hom CGWH.intervalToTopIso.{u, v}.hom_inv_id x

theorem intervalCoordinate_injective : Function.Injective intervalCoordinate.{u, v} :=
  (show Function.LeftInverse intervalDecode.{u, v} intervalCoordinate.{u, v} from
    intervalDecode_coordinate.{u, v}).injective

theorem intervalCoordinate_zero (p : CGWH.point.{u, v}) :
    intervalCoordinate.{u, v} (CGWH.intervalZero.{u, v} p) = 0 := by
  have h := ConcreteCategory.congr_hom CGWH.intervalToTopIso_zero.{u, v} p
  exact congrArg TopCat.I.homeomorph.{v} h

theorem intervalCoordinate_one (p : CGWH.point.{u, v}) :
    intervalCoordinate.{u, v} (CGWH.intervalOne.{u, v} p) = 1 := by
  have h := ConcreteCategory.congr_hom CGWH.intervalToTopIso_one.{u, v} p
  exact congrArg TopCat.I.homeomorph.{v} h

/-- The actual native Cartesian interval map is the continuous maximum of its two coordinates. -/
def intervalMaximumMap : C((I.{u, v} ⊗ I.{u, v} : CGWH.{u, v}), I.{u, v}) where
  toFun z := intervalDecode.{u, v} (max
    (intervalCoordinate.{u, v} ((CartesianMonoidalCategory.fst I.{u, v} I.{u, v}) z))
    (intervalCoordinate.{u, v} ((CartesianMonoidalCategory.snd I.{u, v} I.{u, v}) z)))
  continuous_toFun := intervalDecode.{u, v}.continuous.comp
    ((intervalCoordinate.{u, v}.continuous.comp
      (ConcreteCategory.hom (CartesianMonoidalCategory.fst I.{u, v} I.{u, v})).continuous).max
      (intervalCoordinate.{u, v}.continuous.comp
        (ConcreteCategory.hom (CartesianMonoidalCategory.snd I.{u, v} I.{u, v})).continuous))

/-- Full inclusion constructs the same entire maximum map on the original native CGWH carrier. -/
def intervalMaximum : I.{u, v} ⊗ I.{u, v} ⟶ I.{u, v} :=
  CGWH.cgwhToTop.{u, v}.preimage (X := I.{u, v} ⊗ I.{u, v}) (Y := I.{u, v})
    (TopCat.ofHom intervalMaximumMap.{u, v})

theorem intervalMaximum_apply (z : (I.{u, v} ⊗ I.{u, v} : CGWH.{u, v})) :
    intervalMaximum.{u, v} z = intervalMaximumMap.{u, v} z :=
  ConcreteCategory.congr_hom
    (CGWH.cgwhToTop.{u, v}.map_preimage (X := I.{u, v} ⊗ I.{u, v}) (Y := I.{u, v})
      (TopCat.ofHom intervalMaximumMap.{u, v})) z

/-- Both original Cartesian coordinates are retained by the full native maximum. -/
theorem intervalMaximum_coordinate (z : (I.{u, v} ⊗ I.{u, v} : CGWH.{u, v})) :
    intervalCoordinate.{u, v} (intervalMaximum.{u, v} z) = max
      (intervalCoordinate.{u, v} ((CartesianMonoidalCategory.fst I.{u, v} I.{u, v}) z))
      (intervalCoordinate.{u, v} ((CartesianMonoidalCategory.snd I.{u, v} I.{u, v}) z)) := by
  rw [intervalMaximum_apply.{u, v}]
  exact intervalCoordinate_decode.{u, v} _

/-- Every actual Cartesian pair keeps its full original coordinate maximum formula. -/
theorem intervalMaximum_lift_coordinate (X : CGWH.{u, v}) (f g : X ⟶ I.{u, v}) (x : X) :
    intervalCoordinate.{u, v} ((CartesianMonoidalCategory.lift f g ≫ intervalMaximum.{u, v}) x) =
      max (intervalCoordinate.{u, v} (f x)) (intervalCoordinate.{u, v} (g x)) := by
  change intervalCoordinate.{u, v}
    (intervalMaximum.{u, v} (CartesianMonoidalCategory.lift f g x)) = _
  rw [intervalMaximum_coordinate.{u, v}]
  exact congrArg₂ (fun a b => max (intervalCoordinate.{u, v} a) (intervalCoordinate.{u, v} b))
    (ConcreteCategory.congr_hom (CartesianMonoidalCategory.lift_fst f g) x)
    (ConcreteCategory.congr_hom (CartesianMonoidalCategory.lift_snd f g) x)

/-- The original time-zero source is a left unit of the actual native interval maximum. -/
theorem intervalMaximum_zero_left :
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalZero.{u, v})
        (𝟙 I.{u, v}) ≫ intervalMaximum.{u, v} = 𝟙 I.{u, v} := by
  apply ConcreteCategory.hom_ext
  intro x
  apply intervalCoordinate_injective.{u, v}
  rw [intervalMaximum_lift_coordinate.{u, v}]
  have h : intervalCoordinate.{u, v}
      ((CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalZero.{u, v}) x) = 0 :=
    intervalCoordinate_zero.{u, v} (CGWH.point_isTerminal.{u, v}.from I.{u, v} x)
  rw [h]
  simp

/-- The same unchanged time-zero endpoint is the full right unit. -/
theorem intervalMaximum_zero_right :
    CartesianMonoidalCategory.lift (𝟙 I.{u, v})
        (CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalZero.{u, v}) ≫
      intervalMaximum.{u, v} = 𝟙 I.{u, v} := by
  apply ConcreteCategory.hom_ext
  intro x
  apply intervalCoordinate_injective.{u, v}
  rw [intervalMaximum_lift_coordinate.{u, v}]
  have h : intervalCoordinate.{u, v}
      ((CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalZero.{u, v}) x) = 0 :=
    intervalCoordinate_zero.{u, v} (CGWH.point_isTerminal.{u, v}.from I.{u, v} x)
  rw [h]
  simp

/-- The native disk's actual selected endpoint is absorbed on the full left face. -/
theorem intervalMaximum_one_left :
    CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalOne.{u, v})
        (𝟙 I.{u, v}) ≫ intervalMaximum.{u, v} =
      CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalOne.{u, v} := by
  apply ConcreteCategory.hom_ext
  intro x
  apply intervalCoordinate_injective.{u, v}
  rw [intervalMaximum_lift_coordinate.{u, v}]
  have h : intervalCoordinate.{u, v}
      ((CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalOne.{u, v}) x) = 1 :=
    intervalCoordinate_one.{u, v} (CGWH.point_isTerminal.{u, v}.from I.{u, v} x)
  rw [h]
  simp [unitInterval.le_one']

/-- The same selected disk endpoint is absorbed on the complete right face. -/
theorem intervalMaximum_one_right :
    CartesianMonoidalCategory.lift (𝟙 I.{u, v})
        (CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalOne.{u, v}) ≫
      intervalMaximum.{u, v} =
      CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalOne.{u, v} := by
  apply ConcreteCategory.hom_ext
  intro x
  apply intervalCoordinate_injective.{u, v}
  rw [intervalMaximum_lift_coordinate.{u, v}]
  have h : intervalCoordinate.{u, v}
      ((CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalOne.{u, v}) x) = 1 :=
    intervalCoordinate_one.{u, v} (CGWH.point_isTerminal.{u, v}.from I.{u, v} x)
  rw [h]
  simp [unitInterval.le_one']

private abbrev disk := PointedCGWH.diskOne.{u, v}
private abbrev diskSmash := CategoryTheory.Pointed.smashPresentation
  CGWH.point.{u, v} CGWH.point_isTerminal.{u, v} disk.{u, v} disk.{u, v}

/-- The full native maximum sends both actual disk wedge faces to the same selected endpoint. -/
theorem diskMaximum_wedge : diskSmash.{u, v}.1.right ≫ intervalMaximum.{u, v} =
    CGWH.point_isTerminal.{u, v}.from
      (((CategoryTheory.Pointed.wedge CGWH.point.{u, v}).obj disk.{u, v}).obj disk.{u, v}).right ≫
      disk.{u, v}.hom := by
  apply pushout.hom_ext
  · rw [← Category.assoc, CategoryTheory.Pointed.smashPresentation_wedge_inl]
    have h : pushout.inl disk.{u, v}.hom disk.{u, v}.hom ≫
      CGWH.point_isTerminal.{u, v}.from
        (((CategoryTheory.Pointed.wedge CGWH.point.{u, v}).obj disk.{u, v}).obj disk.{u, v}).right =
        CGWH.point_isTerminal.{u, v}.from I.{u, v} := CGWH.point_isTerminal.{u, v}.hom_ext _ _
    exact intervalMaximum_one_right.{u, v}.trans (congrArg (fun f => f ≫ disk.{u, v}.hom) h.symm)
  · rw [← Category.assoc, CategoryTheory.Pointed.smashPresentation_wedge_inr]
    have h : pushout.inr disk.{u, v}.hom disk.{u, v}.hom ≫
      CGWH.point_isTerminal.{u, v}.from
        (((CategoryTheory.Pointed.wedge CGWH.point.{u, v}).obj disk.{u, v}).obj disk.{u, v}).right =
        CGWH.point_isTerminal.{u, v}.from I.{u, v} := CGWH.point_isTerminal.{u, v}.hom_ext _ _
    exact intervalMaximum_one_left.{u, v}.trans (congrArg (fun f => f ≫ disk.{u, v}.hom) h.symm)

/-- The original pointed disk maximum is the actual native smash-pushout descent. -/
def diskMaximum : disk.{u, v} ⊗ disk.{u, v} ⟶ disk.{u, v} :=
  Under.homMk (diskSmash.{u, v}.2.2.desc
    (PushoutCocone.mk intervalMaximum.{u, v} disk.{u, v}.hom diskMaximum_wedge.{u, v}))
    (diskSmash.{u, v}.2.2.fac _ WalkingSpan.right)

/-- The native disk multiplication retains its full actual Cartesian product generator. -/
theorem diskMaximum_product :
    diskSmash.{u, v}.2.1.inl ≫ diskMaximum.right = intervalMaximum.{u, v} :=
  diskSmash.{u, v}.2.2.fac _ WalkingSpan.left

/-- The same actual disk maximum retains its original selected-point generator. -/
theorem diskMaximum_point : diskSmash.{u, v}.2.1.inr ≫ diskMaximum.right = disk.{u, v}.hom :=
  diskSmash.{u, v}.2.2.fac _ WalkingSpan.right

private abbrev pointUnitIso : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
  CGWH.point_isTerminal.{u, v}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit

/-- The original ordered disk boundary retains its actual freely pointed unit source. -/
def diskBoundarySourceIso : (𝟙_ PointedCGWH.{u, v}) ≅
    (Arrow.mk PointedCGWH.diskBoundary.{u, v}).left := by
  change PointedCGWH.sphereZero.{u, v} ≅
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  exact Under.isoMk (Iso.refl _) (by
    dsimp [PointedCGWH.sphereZero, CategoryTheory.Pointed.smashUnit]
    simp [Under.costar_obj_hom])

/-- The actual native time-zero disk map keeps the full original boundary source isomorphism. -/
def diskFreeEndpoint : (𝟙_ PointedCGWH.{u, v}) ⟶ disk.{u, v} :=
  diskBoundarySourceIso.hom ≫ PointedCGWH.diskBoundary

/-- The original free summand is the unchanged realized time-zero endpoint. -/
theorem diskFreeEndpoint_free :
    (coprod.inr : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right) ≫
      diskFreeEndpoint.right = CGWH.intervalZero.{u, v} := by
  change coprod.inr ≫
    (𝟙 _ ≫ coprod.desc disk.{u, v}.hom CGWH.intervalZero.{u, v}) = _
  rw [Category.id_comp, coprod.inr_desc]

/-- The same original pointed summand retains the selected time-one endpoint. -/
theorem diskFreeEndpoint_base :
    (coprod.inl : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right) ≫
      diskFreeEndpoint.right = CGWH.intervalOne.{u, v} := by
  change coprod.inl ≫
    (𝟙 _ ≫ coprod.desc disk.{u, v}.hom CGWH.intervalZero.{u, v}) = _
  rw [Category.id_comp, coprod.inl_desc]
  rfl

/-- The actual time-zero boundary map is a native cofibration through its original unit Iso. -/
theorem diskFreeEndpoint_cofibration : Cofibration diskFreeEndpoint.{u, v} := by
  let _ : Cofibration PointedCGWH.diskBoundary.{u, v} :=
    PointedCGWH.modelCategory.diskBoundary_cofibration
  change Cofibration (diskBoundarySourceIso.hom ≫ PointedCGWH.diskBoundary)
  infer_instance

/-- The original native disk is cofibrant through the actual freely pointed unit boundary. -/
theorem diskOne_cofibrant : IsCofibrant disk.{u, v} := by
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  let _ : Cofibration diskFreeEndpoint.{u, v} := diskFreeEndpoint_cofibration
  exact isCofibrant_of_cofibration diskFreeEndpoint.{u, v}

/-- Left free-endpoint insertion uses the actual native Cartesian unit and point isomorphism. -/
def intervalFreeLeftInsertion : I.{u, v} ⟶ I.{u, v} ⊗ I.{u, v} :=
  (λ_ I.{u, v}).inv ≫ (pointUnitIso.{u, v}.inv ▷ I.{u, v}) ≫
    (CGWH.intervalZero.{u, v} ▷ I.{u, v})

/-- Both projections retain the original complete time-zero left face. -/
theorem intervalFreeLeftInsertion_eq : intervalFreeLeftInsertion.{u, v} =
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalZero.{u, v})
      (𝟙 I.{u, v}) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [intervalFreeLeftInsertion, Category.assoc,
      CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.whiskerRight_fst_assoc, CartesianMonoidalCategory.lift_fst]
    have h : (λ_ I.{u, v}).inv ≫
        CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) I.{u, v} ≫
          pointUnitIso.{u, v}.inv = CGWH.point_isTerminal.{u, v}.from I.{u, v} :=
      CGWH.point_isTerminal.{u, v}.hom_ext _ _
    simpa only [Category.assoc] using congrArg (· ≫ CGWH.intervalZero.{u, v}) h
  · simp only [intervalFreeLeftInsertion, Category.assoc,
      CartesianMonoidalCategory.whiskerRight_snd,
      CartesianMonoidalCategory.leftUnitor_inv_snd, CartesianMonoidalCategory.lift_snd]

/-- Right free-endpoint insertion uses the same original native Cartesian unit isomorphism. -/
def intervalFreeRightInsertion : I.{u, v} ⟶ I.{u, v} ⊗ I.{u, v} :=
  (ρ_ I.{u, v}).inv ≫ (I.{u, v} ◁ pointUnitIso.{u, v}.inv) ≫
    (I.{u, v} ◁ CGWH.intervalZero.{u, v})

/-- Both original projections retain the actual complete time-zero right face. -/
theorem intervalFreeRightInsertion_eq : intervalFreeRightInsertion.{u, v} =
    CartesianMonoidalCategory.lift (𝟙 I.{u, v})
      (CGWH.point_isTerminal.{u, v}.from I.{u, v} ≫ CGWH.intervalZero.{u, v}) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [intervalFreeRightInsertion, Category.assoc,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_inv_fst, CartesianMonoidalCategory.lift_fst]
  · simp only [intervalFreeRightInsertion, Category.assoc,
      CartesianMonoidalCategory.whiskerLeft_snd,
      CartesianMonoidalCategory.whiskerLeft_snd_assoc, CartesianMonoidalCategory.lift_snd]
    have h : (ρ_ I.{u, v}).inv ≫
        CartesianMonoidalCategory.snd I.{u, v} (𝟙_ CGWH.{u, v}) ≫
          pointUnitIso.{u, v}.inv = CGWH.point_isTerminal.{u, v}.from I.{u, v} :=
      CGWH.point_isTerminal.{u, v}.hom_ext _ _
    simpa only [Category.assoc] using congrArg (· ≫ CGWH.intervalZero.{u, v}) h

private def diskUnderlyingZero : CGWH.point.{u, v} ⟶ disk.{u, v}.right :=
  CGWH.intervalZero.{u, v}

/-- The actual maximum retains the original disk's complete underlying native carrier. -/
def diskUnderlyingMaximum : disk.{u, v}.right ⊗ disk.{u, v}.right ⟶ disk.{u, v}.right :=
  intervalMaximum.{u, v}

/-- Its native product leg is the same actual pointed smash descent. -/
theorem diskUnderlyingMaximum_product :
    diskSmash.{u, v}.2.1.inl ≫ diskMaximum.{u, v}.right = diskUnderlyingMaximum.{u, v} :=
  diskMaximum_product.{u, v}

private theorem diskFreeEndpoint_free_underlying :
    (coprod.inr : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right) ≫
      diskFreeEndpoint.{u, v}.right = diskUnderlyingZero.{u, v} :=
  diskFreeEndpoint_free.{u, v}

private theorem diskUnderlyingMaximum_left_unit :
    ((λ_ disk.{u, v}.right).inv ≫ (pointUnitIso.{u, v}.inv ▷ disk.{u, v}.right) ≫
      (diskUnderlyingZero.{u, v} ▷ disk.{u, v}.right)) ≫ diskUnderlyingMaximum.{u, v} =
        𝟙 disk.{u, v}.right := by
  have h : intervalFreeLeftInsertion.{u, v} ≫ intervalMaximum.{u, v} = 𝟙 I.{u, v} := by
    rw [intervalFreeLeftInsertion_eq]
    exact intervalMaximum_zero_left.{u, v}
  exact h

private theorem diskUnderlyingMaximum_right_unit :
    ((ρ_ disk.{u, v}.right).inv ≫ (disk.{u, v}.right ◁ pointUnitIso.{u, v}.inv) ≫
      (disk.{u, v}.right ◁ diskUnderlyingZero.{u, v})) ≫ diskUnderlyingMaximum.{u, v} =
        𝟙 disk.{u, v}.right := by
  have h : intervalFreeRightInsertion.{u, v} ≫ intervalMaximum.{u, v} = 𝟙 I.{u, v} := by
    rw [intervalFreeRightInsertion_eq]
    exact intervalMaximum_zero_right.{u, v}
  exact h

/-- The actual pointed disk maximum has the complete original time-zero left unit. -/
theorem diskMaximum_left_unit :
    (λ_ disk.{u, v}).inv ≫ (diskFreeEndpoint.{u, v} ▷ disk.{u, v}) ≫
      diskMaximum.{u, v} = 𝟙 disk.{u, v} := by
  apply Under.UnderMorphism.ext
  let q : (𝟙_ PointedCGWH.{u, v}).right ⊗ disk.{u, v}.right ⟶
      ((𝟙_ PointedCGWH.{u, v}) ⊗ disk.{u, v}).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point.{u, v}
      CGWH.point_isTerminal.{u, v} (𝟙_ PointedCGWH.{u, v}) disk.{u, v}).2.1.inl
  have hq : q ≫ (diskFreeEndpoint.{u, v} ▷ disk.{u, v}).right =
      (diskFreeEndpoint.{u, v}.right ▷ disk.{u, v}.right) ≫ diskSmash.{u, v}.2.1.inl := by
    simpa only [tensorHom_id, Under.id_right] using
      (CategoryTheory.Pointed.smashQuotient_naturality CGWH.point.{u, v}
        CGWH.point_isTerminal.{u, v} diskFreeEndpoint.{u, v} (𝟙 disk.{u, v}))
  have hu : (λ_ disk.{u, v}).inv.right =
      (λ_ disk.{u, v}.right).inv ≫ (pointUnitIso.{u, v}.inv ▷ disk.{u, v}.right) ≫
        ((coprod.inr : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right) ▷
          disk.{u, v}.right) ≫
          q := CategoryTheory.Pointed.smashLeftUnitor_inv_free CGWH.point.{u, v}
            CGWH.point_isTerminal.{u, v} disk.{u, v}
  change (λ_ disk.{u, v}).inv.right ≫
    (diskFreeEndpoint.{u, v} ▷ disk.{u, v}).right ≫ diskMaximum.{u, v}.right =
      𝟙 disk.{u, v}.right
  rw [hu]
  simp only [Category.assoc]
  rw [reassoc_of% hq, diskUnderlyingMaximum_product]
  slice_lhs 3 4 => rw [← MonoidalCategory.comp_whiskerRight]
  rw [diskFreeEndpoint_free_underlying]
  simpa only [Category.assoc] using diskUnderlyingMaximum_left_unit.{u, v}

/-- The actual pointed disk maximum retains the complete original time-zero right unit. -/
theorem diskMaximum_right_unit :
    (ρ_ disk.{u, v}).inv ≫ (disk.{u, v} ◁ diskFreeEndpoint.{u, v}) ≫
      diskMaximum.{u, v} = 𝟙 disk.{u, v} := by
  apply Under.UnderMorphism.ext
  let q : disk.{u, v}.right ⊗ (𝟙_ PointedCGWH.{u, v}).right ⟶
      (disk.{u, v} ⊗ (𝟙_ PointedCGWH.{u, v})).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point.{u, v}
      CGWH.point_isTerminal.{u, v} disk.{u, v} (𝟙_ PointedCGWH.{u, v})).2.1.inl
  have hq : q ≫ (disk.{u, v} ◁ diskFreeEndpoint.{u, v}).right =
      (disk.{u, v}.right ◁ diskFreeEndpoint.{u, v}.right) ≫ diskSmash.{u, v}.2.1.inl := by
    simpa only [id_tensorHom, Under.id_right] using
      (CategoryTheory.Pointed.smashQuotient_naturality CGWH.point.{u, v}
        CGWH.point_isTerminal.{u, v} (𝟙 disk.{u, v}) diskFreeEndpoint.{u, v})
  have hu : (ρ_ disk.{u, v}).inv.right =
      (ρ_ disk.{u, v}.right).inv ≫ (disk.{u, v}.right ◁ pointUnitIso.{u, v}.inv) ≫
        (disk.{u, v}.right ◁
          (coprod.inr : CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right)) ≫
          q := CategoryTheory.Pointed.smashRightUnitor_inv_free CGWH.point.{u, v}
            CGWH.point_isTerminal.{u, v} disk.{u, v}
  change (ρ_ disk.{u, v}).inv.right ≫
    (disk.{u, v} ◁ diskFreeEndpoint.{u, v}).right ≫ diskMaximum.{u, v}.right =
      𝟙 disk.{u, v}.right
  rw [hu]
  simp only [Category.assoc]
  rw [reassoc_of% hq, diskUnderlyingMaximum_product]
  slice_lhs 3 4 => rw [← MonoidalCategory.whiskerLeft_comp]
  rw [diskFreeEndpoint_free_underlying]
  simpa only [Category.assoc] using diskUnderlyingMaximum_right_unit.{u, v}

end PointedCGWH.DiskMaximumGeometry
