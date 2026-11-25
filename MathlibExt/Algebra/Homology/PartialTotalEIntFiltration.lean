/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalFunctor
public import MathlibExt.Algebra.Homology.SpectralSequence.IncreasingHomologicalCore
public import MathlibExt.CategoryTheory.Functor.NonnegativeEIntExtension

/-!
# The extended-integer partial-total filtration

The natural partial-total filtration extends to the extended integers.
It is zero below filtration degree zero, agrees with partial totals
in nonnegative finite degrees and equals the full total at ⊤.
Its interval coordinates agree with `coreE₁IncreasingHomologicalNat`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The first-coordinate partial-total filtration, extended by zero below
degree zero and completed by the full total complex at `⊤`. -/
noncomputable def partialTotalEIntFiltration :
    EInt ⥤ ChainComplex C ℕ :=
  CategoryTheory.Functor.nonnegativeEIntExtension
    B.partialTotalFunctor (B.total (ComplexShape.down ℕ))
      B.partialTotalToTotal

@[simp]
theorem partialTotalEIntFiltration_obj_bot :
    B.partialTotalEIntFiltration.obj ⊥ = 0 :=
  rfl

@[simp]
theorem partialTotalEIntFiltration_obj_top :
    B.partialTotalEIntFiltration.obj ⊤ =
      B.total (ComplexShape.down ℕ) :=
  rfl

/-- The canonical coordinate isomorphism at a nonnegative finite filtration
index. -/
noncomputable def partialTotalEIntFiltrationObjIso (p : ℕ) :
    B.partialTotalEIntFiltration.obj ((p : ℤ) : EInt) ≅
      B.partialTotal p :=
  CategoryTheory.Functor.nonnegativeIntObjIso
    B.partialTotalFunctor (p : ℤ) (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- In nonnegative finite degrees, a filtration map is the partial-total inclusion. -/
theorem partialTotalEIntFiltrationObjIso_inv_comp_map
    {p p' : ℕ} (h : p ≤ p') :
    (B.partialTotalEIntFiltrationObjIso p).inv ≫
        B.partialTotalEIntFiltration.map
          (homOfLE (show ((p : ℤ) : EInt) ≤ ((p' : ℤ) : EInt) by
            simpa using h)) ≫
        (B.partialTotalEIntFiltrationObjIso p').hom =
      B.partialTotalMap h := by
  have hInt : (p : ℤ) ≤ (p' : ℤ) := by exact_mod_cast h
  have hraw :
      (CategoryTheory.Functor.nonnegativeIntObjIso
          B.partialTotalFunctor (p : ℤ) (by omega)).inv ≫
        CategoryTheory.Functor.nonnegativeIntMap
          B.partialTotalFunctor hInt ≫
        (CategoryTheory.Functor.nonnegativeIntObjIso
          B.partialTotalFunctor (p' : ℤ) (by omega)).hom =
      B.partialTotalFunctor.map
        (homOfLE (Int.toNat_le_toNat hInt)) := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (CategoryTheory.Functor.nonnegativeIntObjIso_inv_comp_nonnegativeIntMap_assoc
          B.partialTotalFunctor hInt (by omega)
            (CategoryTheory.Functor.nonnegativeIntObjIso
              B.partialTotalFunctor (p' : ℤ) (by omega)).hom)
  have hpNat : Int.toNat (p : ℤ) = p := by omega
  have hpNat' : Int.toNat (p' : ℤ) = p' := by omega
  change
    (CategoryTheory.Functor.nonnegativeIntObjIso
        B.partialTotalFunctor (p : ℤ) (by omega)).inv ≫
      CategoryTheory.Functor.nonnegativeIntMap
        B.partialTotalFunctor hInt ≫
      (CategoryTheory.Functor.nonnegativeIntObjIso
        B.partialTotalFunctor (p' : ℤ) (by omega)).hom =
      B.partialTotalMap h
  simpa only [hpNat, hpNat', B.partialTotalFunctor_map] using hraw

set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage map to `⊤`, in partial-total coordinates, is the
canonical inclusion into the full total complex. -/
theorem partialTotalEIntFiltrationObjIso_inv_comp_toTop (p : ℕ) :
    (B.partialTotalEIntFiltrationObjIso p).inv ≫
        B.partialTotalEIntFiltration.map
          (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp)) =
      B.partialTotalι p := by
  change
    (CategoryTheory.Functor.nonnegativeIntObjIso
        B.partialTotalFunctor (p : ℤ) (by omega)).inv ≫
      CategoryTheory.Functor.nonnegativeIntToTopMap
        B.partialTotalFunctor (B.total (ComplexShape.down ℕ))
          B.partialTotalToTotal (p : ℤ) = B.partialTotalι p
  have hraw :
      (CategoryTheory.Functor.nonnegativeIntObjIso
          B.partialTotalFunctor (p : ℤ) (by omega)).inv ≫
        CategoryTheory.Functor.nonnegativeIntToTopMap
          B.partialTotalFunctor (B.total (ComplexShape.down ℕ))
            B.partialTotalToTotal (p : ℤ) =
      B.partialTotalι (Int.toNat (p : ℤ)) := by
    rw [CategoryTheory.Functor.nonnegativeIntToTopMap_of_nonneg
      B.partialTotalFunctor (B.total (ComplexShape.down ℕ))
        B.partialTotalToTotal (p : ℤ) (by omega)]
    simp only [Iso.inv_hom_id_assoc, B.partialTotalToTotal_app]
  simpa only [Int.toNat_natCast] using hraw

/-- The upper endpoint selected by the increasing page-one core is the
`p`th partial total. -/
noncomputable def partialTotalE₁UpperIso (p q : ℕ) :
    B.partialTotalEIntFiltration.obj
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
          (p, q)) ≅
      B.partialTotal p :=
  eqToIso (congrArg B.partialTotalEIntFiltration.obj (by simp)) ≪≫
    B.partialTotalEIntFiltrationObjIso p

/-- At positive filtration degree `m+1`, the lower endpoint selected by the
increasing page-one core is the `m`th partial total. -/
noncomputable def partialTotalE₁LowerSuccIso (m q : ℕ) :
    B.partialTotalEIntFiltration.obj
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₁
          (m + 1, q)) ≅
      B.partialTotal m :=
  eqToIso (congrArg B.partialTotalEIntFiltration.obj (by simp)) ≪≫
    B.partialTotalEIntFiltrationObjIso m

/-- At filtration degree zero, the lower endpoint of the page-one interval
is the zero object at index `-1`. -/
theorem isZero_partialTotalE₁LowerZero (q : ℕ) :
    IsZero (B.partialTotalEIntFiltration.obj
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₁
        (0, q))) := by
  change IsZero (CategoryTheory.Functor.nonnegativeIntObj
    B.partialTotalFunctor (-1))
  exact CategoryTheory.Functor.isZero_nonnegativeIntObj_of_neg
    B.partialTotalFunctor (-1) (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- At positive filtration degree, the map selected by the page-one core is
the successor partial-total inclusion. -/
theorem partialTotalE₁IntervalMap_succ (m q : ℕ) :
    (B.partialTotalE₁LowerSuccIso m q).inv ≫
        B.partialTotalEIntFiltration.map
          (homOfLE
            (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.le₁₂
              (m + 1, q))) ≫
        (B.partialTotalE₁UpperIso (m + 1) q).hom =
      B.partialTotalMap (Nat.le_succ m) := by
  let core :=
    CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
  have hLower : core.i₁ (m + 1, q) = ((m : ℤ) : EInt) := by simp [core]
  have hUpper : core.i₂ (m + 1, q) = (((m + 1 : ℕ) : ℤ) : EInt) := by
    simp [core]
  let lowerTransport :
      B.partialTotalEIntFiltration.obj (core.i₁ (m + 1, q)) ≅
        B.partialTotalEIntFiltration.obj ((m : ℤ) : EInt) :=
    eqToIso (congrArg B.partialTotalEIntFiltration.obj hLower)
  let upperTransport :
      B.partialTotalEIntFiltration.obj (core.i₂ (m + 1, q)) ≅
        B.partialTotalEIntFiltration.obj (((m + 1 : ℕ) : ℤ) : EInt) :=
    eqToIso (congrArg B.partialTotalEIntFiltration.obj hUpper)
  let coreMap := homOfLE (core.le₁₂ (m + 1, q))
  let successorMap :=
    homOfLE (show ((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt) by simp)
  have hIndex :
      eqToHom hLower.symm ≫ coreMap ≫ eqToHom hUpper = successorMap := by
    subsingleton
  have hTransport :
      lowerTransport.inv ≫ B.partialTotalEIntFiltration.map coreMap ≫
          upperTransport.hom =
        B.partialTotalEIntFiltration.map successorMap := by
    change
      eqToHom (congrArg B.partialTotalEIntFiltration.obj hLower).symm ≫
          B.partialTotalEIntFiltration.map coreMap ≫
          eqToHom (congrArg B.partialTotalEIntFiltration.obj hUpper) =
        B.partialTotalEIntFiltration.map successorMap
    rw [← eqToHom_map B.partialTotalEIntFiltration hLower.symm,
      ← eqToHom_map B.partialTotalEIntFiltration hUpper,
      ← B.partialTotalEIntFiltration.map_comp,
      ← B.partialTotalEIntFiltration.map_comp, hIndex]
  change
    ((lowerTransport ≪≫ B.partialTotalEIntFiltrationObjIso m).inv ≫
      B.partialTotalEIntFiltration.map coreMap ≫
      (upperTransport ≪≫
        B.partialTotalEIntFiltrationObjIso (m + 1)).hom) = _
  calc
    _ = (B.partialTotalEIntFiltrationObjIso m).inv ≫
        (lowerTransport.inv ≫
          B.partialTotalEIntFiltration.map coreMap ≫ upperTransport.hom) ≫
        (B.partialTotalEIntFiltrationObjIso (m + 1)).hom := by
          simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    _ = (B.partialTotalEIntFiltrationObjIso m).inv ≫
        B.partialTotalEIntFiltration.map successorMap ≫
        (B.partialTotalEIntFiltrationObjIso (m + 1)).hom := by
          rw [hTransport]
    _ = B.partialTotalMap (Nat.le_succ m) := by
          exact B.partialTotalEIntFiltrationObjIso_inv_comp_map
            (Nat.le_succ m)

end HomologicalComplex₂

end
