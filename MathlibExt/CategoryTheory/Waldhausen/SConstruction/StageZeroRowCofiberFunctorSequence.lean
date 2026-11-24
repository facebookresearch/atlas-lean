/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationCorners
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageEvaluationExactGeneral
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequenceStageExact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFirstQuotientDecomposition

/-!
# The actual zero-row cofiber sequence of exact functors

For every original pair `i ≤ j`, the evaluations `A0i`, `A0j` and `Aij`
form the original cofiber sequence. A genuine source stage cofibration
supplies the actual zero-row pair corner. Its original universal property
identifies the induced map with the stock base descent, earning the full
cofiber functor-sequence condition without gluing or a preservation input.

For a shifted suffix operator `α`, the same sequence at `i = 1` and
`j = α(0) + 1` retains the original `A01 → A0j → A1j` maps. The accepted
stage functor-sequence construction applies to these actual functors and
arrows in every prior stage direction.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe u v

namespace CategoryTheory.Waldhausen.SConstruction.StageZeroRowCofiber

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original chosen zero value on each general source stage. -/
local instance sourceStageZero (n : ℕ) : HasZeroObject (Stage C n) :=
  generalStageHasZeroObject C n

/-- The original general Waldhausen value on each source stage. -/
local instance sourceStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing (Stage C n) :=
  generalStageWaldhausenCategory C n

/-- The original relative Waldhausen value on the target cofiber category. -/
local instance targetRelativeWaldhausen : WaldhausenCategoryWithoutGluing
    (CofiberSequenceCategory C) :=
  CofiberSequenceCategory.relativeWaldhausenCategory C

/-- The actual original zero-row evaluation at column `i`. -/
def rowFunctor (n : ℕ) (i : Fin (n + 1)) : Stage C n ⥤ C :=
  eval C n (interval 0 i (Fin.zero_le _))

/-- The actual original quotient interval evaluation at `i ≤ j`. -/
def quotientFunctor (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) : Stage C n ⥤ C :=
  eval C n (interval i j hij)

/-- The whole original horizontal zero-row map between the two evaluations. -/
def inclusion (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    rowFunctor C n i ⟶ rowFunctor C n j :=
  Functor.whiskerLeft (forget C n)
    ((evaluation (Ar n) C).map (horiz (Fin.zero_le i) hij))

/-- The whole original vertical quotient map from the second evaluation. -/
def projection (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    rowFunctor C n j ⟶ quotientFunctor C n hij :=
  Functor.whiskerLeft (forget C n)
    ((evaluation (Ar n) C).map (vert (Fin.zero_le i) hij))

/-- Every original row object is the same original zero-row object. -/
theorem rowFunctor_obj (n : ℕ) (i : Fin (n + 1)) (A : Stage C n) :
    (rowFunctor C n i).obj A = A.zeroRowObj i := rfl

/-- Every whole original row map is the same original zero-row component. -/
theorem rowFunctor_map (n : ℕ) (i : Fin (n + 1)) {A B : Stage C n} (φ : A ⟶ B) :
    (rowFunctor C n i).map φ = Stage.zeroRowApp φ i := rfl

/-- The actual quotient retains the entire original interval coefficient. -/
theorem quotientFunctor_obj (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) (A : Stage C n) :
    (quotientFunctor C n hij).obj A = A.obj.obj (interval i j hij) := rfl

/-- The quotient map is the actual original interval component of the whole flag map. -/
theorem quotientFunctor_map (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j)
    {A B : Stage C n} (φ : A ⟶ B) :
    (quotientFunctor C n hij).map φ = φ.hom.app (interval i j hij) := rfl

/-- The whole first arrow is the actual original zero-row pair map. -/
theorem inclusion_app (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) (A : Stage C n) :
    (inclusion C n hij).app A = A.zeroRowPairMap hij :=
  (Stage.zeroRowPairMap_eq A hij).symm

/-- The whole quotient arrow is the actual original vertical cofiber map. -/
theorem projection_app (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) (A : Stage C n) :
    (projection C n hij).app A = A.obj.map (vert (Fin.zero_le i) hij) := rfl

/-- Each original object has the original zero-row cofiber triangle. -/
theorem objectwise (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) (A : Stage C n) :
    IsCofiberSequence ((inclusion C n hij).app A) ((projection C n hij).app A) :=
  A.property.cofiber_triple (Fin.zero_le i) hij

private theorem baseCofibration_of_corner (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j)
    {A B : Stage C n} (φ : A ⟶ B) (hφ : IsCofibration φ)
    [HasPushout ((inclusion C n hij).app A) ((rowFunctor C n i).map φ)] :
    IsCofibration (pushout.desc ((rowFunctor C n j).map φ) ((inclusion C n hij).app B)
      ((inclusion C n hij).naturality φ).symm) := by
  obtain ⟨P, inl, inr, d, hP, hl, hr, hd⟩ := Stage.zeroRowPair_corner C φ
    ((isCofibration_generalStageWaldhausenCategory_iff C n φ).mp hφ) hij
  let l : (rowFunctor C n j).obj A ⟶ P := inl
  let r : (rowFunctor C n i).obj B ⟶ P := inr
  let dn : P ⟶ (rowFunctor C n j).obj B := d
  have hP' : IsPushout ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) l r := by
    rw [inclusion_app, rowFunctor_map]
    exact hP
  let e := hP'.isoPushout
  let δ := pushout.desc ((rowFunctor C n j).map φ) ((inclusion C n hij).app B)
    ((inclusion C n hij).naturality φ).symm
  have heL : pushout.inl ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) ≫
      e.inv = l := hP'.inl_isoPushout_inv
  have heR : pushout.inr ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) ≫
      e.inv = r := hP'.inr_isoPushout_inv
  have hl' : l ≫ dn = (rowFunctor C n j).map φ :=
    hl.trans (rowFunctor_map C n j φ).symm
  have hr' : r ≫ dn = (inclusion C n hij).app B :=
    hr.trans (inclusion_app C n hij B).symm
  have hδ : δ = e.inv ≫ dn := by
    apply pushout.hom_ext
    · calc
        _ = (rowFunctor C n j).map φ := pushout.inl_desc _ _ _
        _ = l ≫ dn := hl'.symm
        _ = (pushout.inl ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) ≫
            e.inv) ≫ dn := congrArg (fun k : (rowFunctor C n j).obj A ⟶ P => k ≫ dn) heL.symm
        _ = _ := Category.assoc _ _ _
    · calc
        _ = (inclusion C n hij).app B := pushout.inr_desc _ _ _
        _ = r ≫ dn := hr'.symm
        _ = (pushout.inr ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) ≫
            e.inv) ≫ dn := congrArg (fun k : (rowFunctor C n i).obj B ⟶ P => k ≫ dn) heR.symm
        _ = _ := Category.assoc _ _ _
  have he : IsCofibration e.inv := (WaldhausenCategoryWithoutGluing.cofibrations (C :=
    C)).of_isIso e.inv
  have hdn : IsCofibration dn := hd
  have hcomp : IsCofibration (e.inv ≫ dn) :=
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem e.inv dn he hdn
  change IsCofibration δ
  exact hδ.symm ▸ hcomp

/-- The original evaluations and both original arrows satisfy the FULL
cofiber functor-sequence condition, including the actual stock base map. -/
theorem certificate (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsWaldhausenCofiberFunctorSequence (rowFunctor C n i) (rowFunctor C n j)
      (quotientFunctor C n hij) (inclusion C n hij) (projection C n hij) := by
  refine ⟨evalIsGeneralStageWaldhausenExact C n (interval 0 i (Fin.zero_le _)),
    evalIsGeneralStageWaldhausenExact C n (interval 0 j (Fin.zero_le _)),
    evalIsGeneralStageWaldhausenExact C n (interval i j hij), objectwise C n hij, ?_⟩
  intro A B φ hφ
  let : HasPushout ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) := by
    obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
      (C := C) ((inclusion C n hij).app A) (objectwise C n hij A).1
      ((rowFunctor C n i).obj B) ((rowFunctor C n i).map φ)
    exact hP.flip.hasPushout
  exact baseCofibration_of_corner C n hij φ hφ

/-- The SAME stock base descent is a genuine cofibration, with its
pushout existence earned from the original objectwise first arrow. -/
theorem baseCofibration (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j)
    {A B : Stage C n} (φ : A ⟶ B) (hφ : IsCofibration φ) :
    letI : HasPushout ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) := by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
        (C := C) ((inclusion C n hij).app A) (objectwise C n hij A).1
        ((rowFunctor C n i).obj B) ((rowFunctor C n i).map φ)
      exact hP.flip.hasPushout
    IsCofibration (pushout.desc ((rowFunctor C n j).map φ) ((inclusion C n hij).app B)
      ((inclusion C n hij).naturality φ).symm) :=
  (certificate C n hij).baseCofibration φ hφ

/-- The entire original triangle in the stock relative cofiber category. -/
def lift (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    Stage C n ⥤ CofiberSequenceCategory C :=
  cofiberFunctorSequenceLift (rowFunctor C n i) (rowFunctor C n j)
    (quotientFunctor C n hij) (inclusion C n hij) (projection C n hij)
    (certificate C n hij).objectwise

/-- Exactness of the actual full lift is earned from the original full certificate. -/
theorem lift_isWaldhausenExact (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    (lift C n hij).IsWaldhausenExact :=
  (certificate C n hij).lift_isWaldhausenExact

/-- The actual shifted operator selects the original successor of `α(0)`. -/
def shiftedIndex {a b : SimplexCategory} (α : a ⟶ b) : Fin (b.len + 2) :=
  (α.toOrderHom (0 : Fin (a.len + 1))).succ

/-- The original first positive vertex lies below the actual selected successor. -/
theorem first_le_shiftedIndex {a b : SimplexCategory} (α : a ⟶ b) :
    StageFirstQuotient.firstIndex b.len ≤ shiftedIndex α :=
  Fin.succ_le_succ_iff.mpr (Fin.zero_le _)

/-- Every shifted operator retains the actual original three-functor
`A01 → A0j → A1j` sequence with its entire earned base condition. -/
theorem shiftedCertificate {a b : SimplexCategory} (α : a ⟶ b) :
    IsWaldhausenCofiberFunctorSequence
      (rowFunctor C (b.len + 1) (StageFirstQuotient.firstIndex b.len))
      (rowFunctor C (b.len + 1) (shiftedIndex α))
      (quotientFunctor C (b.len + 1) (first_le_shiftedIndex α))
      (inclusion C (b.len + 1) (first_le_shiftedIndex α))
      (projection C (b.len + 1) (first_le_shiftedIndex α)) :=
  certificate C (b.len + 1) (first_le_shiftedIndex α)

/-- Equal endpoints retain their original actual diagonal quotient. -/
theorem equalEndpoints (n : ℕ) (i : Fin (n + 1)) :
    IsWaldhausenCofiberFunctorSequence (rowFunctor C n i) (rowFunctor C n i)
      (quotientFunctor C n (le_refl i)) (inclusion C n (le_refl i))
      (projection C n (le_refl i)) :=
  certificate C n (le_refl i)

/-- Degree zero retains the original zero-stage carrier and its actual diagonal interval. -/
theorem degreeZero :
    IsWaldhausenCofiberFunctorSequence (rowFunctor C 0 0) (rowFunctor C 0 0)
      (quotientFunctor C 0 (le_refl (0 : Fin 1)))
      (inclusion C 0 (le_refl (0 : Fin 1))) (projection C 0 (le_refl (0 : Fin 1))) :=
  certificate C 0 (le_refl (0 : Fin 1))

end CategoryTheory.Waldhausen.SConstruction.StageZeroRowCofiber

end
