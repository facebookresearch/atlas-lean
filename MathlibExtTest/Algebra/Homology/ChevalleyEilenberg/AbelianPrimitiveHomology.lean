/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.HomologyCoalgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# A positive abelian CE primitive/homology (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ)
  ℚ 1)

The rational line has the actual commutator Lie structure, hence zero
bracket. The actual ambient exterior boundary and the actual CE
differentials vanish. In degree one the canonical primitive/homology
(ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) is an isomorphism. Its value on the
  original scalar 3 is
detected as 3 through the ordinary CE homology/object and exterior
degree-one coordinates, independently of the (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k :=
  ℚ) ℚ 1)'s inverse.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ChevalleyEilenbergTest.AbelianPrimitiveHomology

local instance rationalLieRing : LieRing ℚ := LieRing.ofAssociativeRing

local instance actualChainComon : ComonObj
    ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex) :=
  (ChevalleyEilenberg.HomologyCoalgebra.UnitComparison.chainCoalgebra ℚ ℚ).comon

local instance actualFieldTensorator (n : ℕ) : IsIso
    (HomologicalComplex.kunnethHomologyTensorMap
      ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex)
      ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex) n) :=
  HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field _ _ n


theorem bracket_zero (x y : ℚ) : ⁅x, y⁆ = 0 := by
  change x * y - y * x = 0
  rw [mul_comm, sub_self]

theorem adjointAction_zero (x : ℚ) (a : ExteriorAlgebra ℚ ℚ) :
    ChevalleyEilenberg.adjointAction ℚ ℚ x a = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => exact ChevalleyEilenberg.adjointAction_algebraMap ℚ ℚ x r
  | add a b ha hb => simp only [map_add, ha, hb, zero_add]
  | ι_mul a y ha =>
      rw [ChevalleyEilenberg.adjointAction_ι_mul, bracket_zero, map_zero,
        zero_mul, ha, mul_zero, add_zero]

theorem boundary_zero (a : ExteriorAlgebra ℚ ℚ) : ChevalleyEilenberg.boundary ℚ ℚ a = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => exact ChevalleyEilenberg.boundary_algebraMap ℚ ℚ r
  | add a b ha hb => simp only [map_add, ha, hb, zero_add]
  | ι_mul a x ha =>
      rw [ChevalleyEilenberg.boundary_ι_mul, adjointAction_zero, ha, mul_zero,
        neg_zero, sub_zero]

theorem differential_zero (n : ℕ) : ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).d (n + 1) n = 0 := by
  rw [ChevalleyEilenberg.ChainData.complex_d_succ]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (ChevalleyEilenberg.differential ℚ ℚ n a : ExteriorAlgebra ℚ ℚ) = 0
  rw [ChevalleyEilenberg.differential_coe]
  exact boundary_zero _

local instance cyclesC_isIso : IsIso (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1) :=
  ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).isIso_iCycles 1 0 (by simp) (differential_zero 0)

local instance cyclesP_isIso : IsIso ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1) :=
  (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).isIso_iCycles 1 0 (by simp)
    (ChevalleyEilenberg.nativePrimitiveComplex_d_one_zero ℚ ℚ)

local instance homologyπC_isIso : IsIso (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).homologyπ 1) :=
  ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).isIso_homologyπ 2 1 (by simp) (differential_zero 1)

local instance homologyπP_isIso : IsIso ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1) :=
  (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).isIso_homologyπ 2 1 (by simp)
    (ChevalleyEilenberg.nativePrimitiveComplex_d_eq_zero ℚ ℚ 2 1)

local instance inclusion_one_isIso : IsIso ((ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1) := by
  have h : (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 = (ChevalleyEilenberg.nativePrimitiveDegreeOneEquiv ℚ
    ℚ).toModuleIso.hom ≫
      (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact ChevalleyEilenberg.HomologyCoalgebra.primitiveOne_inclusion ℚ ℚ a
  let e := (ChevalleyEilenberg.nativePrimitiveDegreeOneEquiv ℚ ℚ).toModuleIso ≪≫
    (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.symm
  have he : (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 = e.hom := h
  exact he.symm ▸ e.isIso_hom

local instance cyclesMap_isIso : IsIso (HomologicalComplex.cyclesMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ)
  1) := by
  have h : HomologicalComplex.cyclesMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 =
      (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1 ≫ (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f
        1 ≫ inv (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1) := by
    apply (cancel_mono (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1)).1
    rw [HomologicalComplex.cyclesMap_i]
    exact ((Category.assoc
      ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1)
      ((ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1)
      (inv (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1) ≫
        ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1)).trans
      (congrArg (fun z => (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1 ≫
        (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 ≫ z)
        (IsIso.inv_hom_id (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1)))).symm
  rw [h]
  infer_instance

local instance homologyMap_isIso : IsIso (HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion
  ℚ ℚ) 1) := by
  have h : HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 =
      inv ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1) ≫ HomologicalComplex.cyclesMap
        (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 ≫ ((ChevalleyEilenberg.canonicalChainData ℚ
          ℚ).complex).homologyπ 1 := by
    apply (cancel_epi ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1)).1
    rw [HomologicalComplex.homologyπ_naturality]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [h]
  infer_instance

/-- The (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) is actually an isomorphism
  here because both actual
differentials vanish and the degree-one inclusion is an actual isomorphism. -/
theorem comparison_isIso : IsIso (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) := by
  let j := ChevalleyEilenberg.HomologyCoalgebra.homologyPrimitivesOneIso (k := ℚ) ℚ
  have h : (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) =
    HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 ≫ j.inv := by
    apply (cancel_mono j.hom).1
    have hi := congrFun
      (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison_inclusion (k := ℚ) ℚ) 1
    change (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) ≫
      (kernel.ι (HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation
        ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex)
        (ChevalleyEilenberg.HomologyCoalgebra.UnitComparison.chainCoaug ℚ ℚ))) 1 = _ at hi
    rw [← ChevalleyEilenberg.HomologyCoalgebra.homologyPrimitivesOneIso_hom (k := ℚ) ℚ] at hi
    have hi' : (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) ≫
        j.hom = HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 := hi
    exact hi'.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun z => HomologicalComplex.homologyMap
        (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 ≫ z) j.inv_hom_id).trans
        (Category.comp_id _))).symm
  let e := asIso (HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1) ≪≫ j.symm
  have he : (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) = e.hom := h
  exact he.symm ▸ e.isIso_hom

def primitiveVectorThree : (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).X 1 :=
  (ChevalleyEilenberg.nativePrimitiveDegreeOneEquiv ℚ ℚ).symm (3 : ℚ)

def primitiveCycleThree : (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).cycles 1 :=
  ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCyclesIso 1 0 (by simp)
    (ChevalleyEilenberg.nativePrimitiveComplex_d_one_zero ℚ ℚ)).inv
    primitiveVectorThree

def primitiveClassThree : (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homology 1 :=
  (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1 primitiveCycleThree

def homologyObjectIso : ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).homology 1 ≅
  ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).X 1 :=
  (((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).isoHomologyπ 2 1 (by simp) (differential_zero 1)).symm ≪≫
    ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCyclesIso 1 0 (by simp) (differential_zero 0)

/-- The output detector uses the ordinary CE homology coordinate and the
native exterior degree-one coordinate. It does not use the
  (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) inverse. -/
def outputCoordinate :
    (ChevalleyEilenberg.HomologyCoalgebra.homologyPrimitiveObject (k := ℚ) ℚ) 1 ⟶
      ModuleCat.of ℚ ℚ :=
  (ChevalleyEilenberg.HomologyCoalgebra.homologyPrimitivesOneIso (k := ℚ) ℚ).hom ≫
    homologyObjectIso.hom ≫ (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom

theorem comparison_three_coordinate : outputCoordinate
  ((ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) primitiveClassThree) = 3 := by
  have hi := congrFun
    (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison_inclusion (k := ℚ) ℚ) 1
  change (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) ≫
    (kernel.ι (HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation
      ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex)
      (ChevalleyEilenberg.HomologyCoalgebra.UnitComparison.chainCoaug ℚ ℚ))) 1 = _ at hi
  rw [← ChevalleyEilenberg.HomologyCoalgebra.homologyPrimitivesOneIso_hom (k := ℚ) ℚ] at hi
  have hπ : ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).homologyπ 1 ≫ homologyObjectIso.hom =
    ((ChevalleyEilenberg.canonicalChainData ℚ ℚ).complex).iCycles 1 := by
    simp only [homologyObjectIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, HomologicalComplex.iCyclesIso_hom]
  have h : (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) ℚ 1) ≫ outputCoordinate =
      inv ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1) ≫ (ChevalleyEilenberg.nativePrimitiveComplex ℚ
        ℚ).iCycles 1 ≫ (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 ≫
        (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom := by
    rw [outputCoordinate]
    have hprefix := congrArg (fun z => z ≫ homologyObjectIso.hom ≫
      (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom) hi
    rw [← Category.assoc]
    apply hprefix.trans
    apply (cancel_epi ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1)).1
    have hN := HomologicalComplex.homologyπ_naturality
      (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1
    have hC := HomologicalComplex.cyclesMap_i (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1
    have h₁ := congrArg (fun z => z ≫ homologyObjectIso.hom ≫
      (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom) hN
    have h₂ := congrArg (fun z => HomologicalComplex.cyclesMap
      (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ) 1 ≫ z ≫
      (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom) hπ
    have h₃ := congrArg (fun z => z ≫ (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom) hC
    have hLeft := (h₁.trans h₂).trans h₃
    have hRight : ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1) ≫
        inv ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1) ≫
          (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1 ≫
          (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 ≫
          (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom =
        (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1 ≫
          (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 ≫
          (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom := by
      simp only [IsIso.hom_inv_id_assoc]
    exact hLeft.trans hRight.symm

  have hv := congrArg (fun f => f.hom primitiveClassThree) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hv
  have hπinv : (inv ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1)).hom
      primitiveClassThree = primitiveCycleThree := by
    have h := congrArg (fun f => f.hom primitiveCycleThree)
      (IsIso.hom_inv_id ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1))
    exact h
  have hcyc : (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1
      primitiveCycleThree = primitiveVectorThree := by
    exact congrArg (fun f => f.hom primitiveVectorThree)
      ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCyclesIso_inv_hom_id 1 0
        (by simp) (ChevalleyEilenberg.nativePrimitiveComplex_d_one_zero ℚ ℚ))
  have hcoord : (exteriorPower.oneEquiv ℚ ℚ)
      (((ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1).hom primitiveVectorThree) = 3 :=
    (congrArg (exteriorPower.oneEquiv ℚ ℚ)
      (ChevalleyEilenberg.HomologyCoalgebra.primitiveOne_inclusion ℚ ℚ primitiveVectorThree)).trans
        ((LinearEquiv.apply_symm_apply (exteriorPower.oneEquiv ℚ ℚ) _).trans
          ((ChevalleyEilenberg.nativePrimitiveDegreeOneEquiv ℚ ℚ).apply_symm_apply (3 : ℚ)))
  have hValue : (inv ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1) ≫
        (ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1 ≫
        (ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1 ≫
        (exteriorPower.oneEquiv ℚ ℚ).toModuleIso.hom).hom primitiveClassThree = 3 := by
    change (exteriorPower.oneEquiv ℚ ℚ)
      (((ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1).hom
        (((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1).hom
          ((inv ((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).homologyπ 1)).hom
            primitiveClassThree))) = 3
    exact (congrArg (fun a => (exteriorPower.oneEquiv ℚ ℚ)
      (((ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1).hom
        (((ChevalleyEilenberg.nativePrimitiveComplex ℚ ℚ).iCycles 1).hom a))) hπinv).trans
          ((congrArg (fun a => (exteriorPower.oneEquiv ℚ ℚ)
            (((ChevalleyEilenberg.nativePrimitiveInclusion ℚ ℚ).f 1).hom a)) hcyc).trans hcoord)
  exact hv.trans hValue

end ChevalleyEilenbergTest.AbelianPrimitiveHomology
