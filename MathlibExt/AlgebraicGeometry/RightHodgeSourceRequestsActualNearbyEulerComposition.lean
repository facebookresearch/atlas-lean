/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RightVFiltrationModels

/-!
# The nearby Euler composition for actual right V-operators

The nearby nilpotent endomorphism `var ∘ can` of `grV^0` equals the graded Euler
operator at index `0`. At index `0` the Euler scalar vanishes, so the original
Euler action is `∂` followed by `t`; both sides agree on every original section
lift, hence as sheaf maps since the graded projection is epi.

Source: Saito1307.2140v5, Sections1.1--1.5,2.1,2.2 and2.4;
the coefficient-perverse source locators remain in CoefficientPerverseModels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RightHodgeSourceRequests

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.RightDifferentialModules
open MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
open MathlibExt.AlgebraicGeometry.RightVFiltrationModels
open MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves
open MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars

/-- The original Euler action at index `0` is `∂` followed by `t`. -/
private theorem euler_zero (k : Type) [CommRing k] [Algebra ℚ k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (W : Opens M) (s : N.val.obj (op W)) :
    rightEuler k M O C N W (algebraMap ℚ k 0) s =
      rightCoordinate k M O C N W (rightPartial k M O C N W s) := by
  unfold rightEuler eulerFinite
  have h0 : algebraMap ℚ k (0 : ℚ) = (0 : k) := map_zero _
  rw [h0]
  have h1 : algebraMap k (O.obj (op W)) (0 : k) = 0 := map_zero _
  rw [h1]
  have h2 : scalarFinite k M O W (0 : O.obj (op W)) = 0 := map_zero _
  rw [h2, add_zero]
  exact right_partial_coordinate k M O C N W s

/-- `can` is the graded `∂` followed by transport along `0 - 1 = -1`. -/
private theorem can_eq (k : Type) [CommRing k] [Algebra ℚ k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V)
    (h01 : (0 : ℚ) - 1 = -1) :
    can k M O C N V A = A.partialMap 0 ≫ eqToHom (congrArg (gradedV k M O C N V) h01) := by
  have hObj : gradedV k M O C N V (0 - 1) = vanishingUnipotent k M O C N V :=
    congrArg (gradedV k M O C N V) h01
  unfold can
  change cast (congrArg (fun W => gradedV k M O C N V 0 ⟶ W) hObj) (A.partialMap 0) = _
  exact CategoryTheory.congrArg_cast_hom_right _ hObj.symm

/-- `var` is the graded `t` followed by transport along `-1 + 1 = 0`. -/
private theorem var_eq (k : Type) [CommRing k] [Algebra ℚ k] (M : Type)
    [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V)
    (h11 : (-1 : ℚ) + 1 = 0) :
    var k M O C N V A = A.coordinateMap (-1) ≫ eqToHom (congrArg (gradedV k M O C N V) h11) := by
  have hObj : gradedV k M O C N V (-1 + 1) = nearbyUnipotent k M O C N V :=
    congrArg (gradedV k M O C N V) h11
  unfold var
  change cast (congrArg (fun W => gradedV k M O C N V (-1) ⟶ W) hObj) (A.coordinateMap (-1)) = _
  exact CategoryTheory.congrArg_cast_hom_right _ hObj.symm

/-- `eqToHom` acts as the identity up to heterogeneous equality. -/
private theorem eqToHom_app (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
    (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    (X Y : SheafOfModules.{0} (coefficientSheaf k M O)) (h : X = Y)
    (U : (Opens M)ᵒᵖ) (x : X.val.obj U) :
    HEq (((eqToHom h).val.app U).hom x) x := by
  cases h
  simp

/-- The graded projection commutes with transport along an index equality. -/
private theorem gradedProjection_transport (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (a b : ℚ) (h : a = b) (W : Opens M)
    (t : (V.term a).toSheafOfModules.val.obj (op W)) :
    HEq (((gradedProjection k M O C N V a).val.app (op W)).hom t)
      (((gradedProjection k M O C N V b).val.app (op W)).hom (h ▸ t)) := by
  cases h
  rfl

/-- The V-piece inclusion commutes with transport along an index equality. -/
private theorem inclusion_transport (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (a b : ℚ) (h : a = b) (W : Opens M)
    (t : (V.term a).toSheafOfModules.val.obj (op W)) :
    ((V.term b).ι.val.app (op W)).hom (h ▸ t) =
      ((V.term a).ι.val.app (op W)).hom t := by
  cases h
  rfl

/-- The nearby right Euler operator is literally the original can followed by var. -/
public theorem actual_nearby_euler_composition (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V) :
    nearbyNilpotent k M O C N V A = A.eulerMap 0 := by
  have hEpi : Epi (gradedProjection k M O C N V 0) :=
    CategoryTheory.Limits.coequalizer.π_epi
  have h01 : (0 : ℚ) - 1 = -1 := by simp
  have h11 : (-1 : ℚ) + 1 = 0 := by simp
  have hcan' := can_eq k M O C N V A h01
  have hvar' := var_eq k M O C N V A h11
  have h : gradedProjection k M O C N V 0 ≫ (nearbyNilpotent k M O C N V A).asHom =
      gradedProjection k M O C N V 0 ≫ (A.eulerMap 0).asHom := by
    ext U s
    obtain ⟨W⟩ := U
    have hx : ((V.term 0).ι.val.app (op W)).hom s ∈ (V.term 0).toSubmodule.obj (op W) := by
      have hh : ((V.term 0).ι.val.app (op W)).hom s = s.val := rfl
      rw [hh]
      exact s.property
    have hmem1 : rightPartial k M O C N W (((V.term 0).ι.val.app (op W)).hom s) ∈
        (V.term (0 - 1)).toSubmodule.obj (op W) :=
      V.partialAction 0 W _ hx
    obtain ⟨t1, ht1⟩ : ∃ t : (V.term (0-1)).toSheafOfModules.val.obj (op W),
        ((V.term (0-1)).ι.val.app (op W)).hom t =
          rightPartial k M O C N W (((V.term 0).ι.val.app (op W)).hom s) :=
      ⟨⟨_, hmem1⟩, rfl⟩
    have hpart := A.partial_normal 0 W s t1 ht1
    have hmem1' : rightPartial k M O C N W (((V.term 0).ι.val.app (op W)).hom s) ∈
        (V.term (-1)).toSubmodule.obj (op W) := h01 ▸ hmem1
    have ht1'_iota : ((V.term (-1)).ι.val.app (op W)).hom (h01 ▸ t1) =
        rightPartial k M O C N W (((V.term 0).ι.val.app (op W)).hom s) :=
      (inclusion_transport k M O C N V (0-1) (-1) h01 W t1).trans ht1
    have hmem2 : rightCoordinate k M O C N W (((V.term (-1)).ι.val.app (op W)).hom (h01 ▸ t1)) ∈
        (V.term (-1 + 1)).toSubmodule.obj (op W) := by
      apply V.coordinateAction (-1) W _ _
      rw [ht1'_iota]
      exact hmem1'
    obtain ⟨t2, ht2⟩ : ∃ t : (V.term (-1+1)).toSheafOfModules.val.obj (op W),
        ((V.term (-1+1)).ι.val.app (op W)).hom t =
          rightCoordinate k M O C N W (((V.term (-1)).ι.val.app (op W)).hom (h01 ▸ t1)) :=
      ⟨⟨_, hmem2⟩, rfl⟩
    have hcoord := A.coordinate_normal (-1) W (h01 ▸ t1) t2 ht2
    have ht2'_iota : ((V.term 0).ι.val.app (op W)).hom (h11 ▸ t2) =
        rightEuler k M O C N W (algebraMap ℚ k 0) (((V.term 0).ι.val.app (op W)).hom s) := by
      have htrans := inclusion_transport k M O C N V (-1+1) 0 h11 W t2
      rw [htrans, ht2, ht1'_iota]
      exact (euler_zero k M O C N W _).symm
    have heuler := A.euler_normal 0 W s (h11 ▸ t2) ht2'_iota
    have hnil : (nearbyNilpotent k M O C N V A).asHom =
        can k M O C N V A ≫ var k M O C N V A := rfl
    rw [hnil, hcan', hvar']
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    rw [hpart]
    have heq2a := eqToHom_app k M O _ _ (congrArg (gradedV k M O C N V) h01) (op W)
      (((gradedProjection k M O C N V (0-1)).val.app (op W)).hom t1)
    have heq2b := gradedProjection_transport k M O C N V (0-1) (-1) h01 W t1
    have heq2 := heq2a.trans heq2b
    have heq2_eq := eq_of_heq heq2
    rw [heq2_eq, hcoord]
    have heq4a := eqToHom_app k M O _ _ (congrArg (gradedV k M O C N V) h11) (op W)
      (((gradedProjection k M O C N V (-1+1)).val.app (op W)).hom t2)
    have heq4b := gradedProjection_transport k M O C N V (-1+1) 0 h11 W t2
    have heq4 := heq4a.trans heq4b
    have heq4_eq := eq_of_heq heq4
    rw [heq4_eq, heuler]
  have h' : (nearbyNilpotent k M O C N V A).asHom = (A.eulerMap 0).asHom :=
    hEpi.left_cancellation _ _ h
  exact End.ext h'

end WantedExt.AlgebraicGeometry.RightHodgeSourceRequests
