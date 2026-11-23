/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedCoreZeroGradeHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra
open scoped Simplicial

universe u

#check @CategoryTheory.SInverseS.zeroCoreFraction
#print axioms CategoryTheory.SInverseS.zeroCoreFraction
#check @CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup
#check @CategoryTheory.SInverseS.zeroCoreFraction_ambient_characteristic
#print axioms CategoryTheory.SInverseS.zeroCoreFraction_ambient_characteristic
#check @CategoryTheory.SInverseS.zeroLocalizedCoreComparison
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreComparison
#check @CategoryTheory.SInverseS.zeroLocalizedCoreComparison_comp_inclusion
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreComparison_comp_inclusion
#check @CategoryTheory.SInverseS.zeroLocalizedCoreComparison_injective
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreComparison_injective
#check @CategoryTheory.SInverseS.zeroLocalizedCoreComparison_surjective
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreComparison_surjective
#check @CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso
#check @CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso_comp_inclusion
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso_comp_inclusion
#check @CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso_hom_fraction
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso_hom_fraction
#check @CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso_inv_val
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso_inv_val
#check @CategoryTheory.SInverseS.zeroLocalizedCoreSubgroupSplitMono
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreSubgroupSplitMono

#check @CategoryTheory.SInverseS.zeroCoreFraction_eq_mk
#print axioms CategoryTheory.SInverseS.zeroCoreFraction_eq_mk
#check @CategoryTheory.SInverseS.zeroCoreFractionMap
#print axioms CategoryTheory.SInverseS.zeroCoreFractionMap
#check @CategoryTheory.SInverseS.zeroCoreFractionMap_apply
#print axioms CategoryTheory.SInverseS.zeroCoreFractionMap_apply
#check @CategoryTheory.SInverseS.zeroCoreFractionMap_comp_homologyIso
#print axioms CategoryTheory.SInverseS.zeroCoreFractionMap_comp_homologyIso
#check @CategoryTheory.SInverseS.zeroCoreFractionMap_comp_canonical
#print axioms CategoryTheory.SInverseS.zeroCoreFractionMap_comp_canonical

#check @CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup_le_iff
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup_le_iff
#check @CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup_le_iff_fractionMap
#print axioms CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup_le_iff_fractionMap

namespace CategoryTheory.SInverseS.ZeroGradeHomologyTests

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example (A : AddCommGrpCat.{u}) (q : ℕ) (t : Skeleton C)
    (x : (nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))).homology (C := AddCommGrpCat.{u})
        A q) :
    (zeroLocalizedCoreHomologyIso (C := C) A q).hom
      ⟨zeroCoreFraction (C := C) A q t x, zeroCoreFraction_mem (C := C) A q t x⟩ =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (positiveZeroFractionFunctor (C := C)
          t)) A q x :=
  zeroLocalizedCoreHomologyIso_hom_fraction (C := C) A q t x

example (A : AddCommGrpCat.{u}) (q : ℕ) :
    (zeroLocalizedCoreHomologyIso (C := C) A q).hom ≫
        SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (zeroComponentProperty (C := C)).ι) A
            q =
      AddCommGrpCat.ofHom (zeroLocalizedCoreSubgroup (C := C) A q).subtype ≫
        (secondTranslationBKLocalizedCoreHomologyIso (C := C) A q ≪≫
          swapHomologyIso (C := C) A q).hom :=
  zeroLocalizedCoreHomologyIso_comp_inclusion (C := C) A q

example (A : AddCommGrpCat.{u}) (q : ℕ)
    (y : (nerve (ZeroComponent (C := C))).homology (C := AddCommGrpCat.{u}) A q) :
    ((zeroLocalizedCoreHomologyIso (C := C) A q).inv y).val =
      (secondTranslationBKLocalizedCoreHomologyIso (C := C) A q ≪≫
        swapHomologyIso (C := C) A q).inv
          (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (zeroComponentProperty (C := C)).ι)
              A q y) :=
  zeroLocalizedCoreHomologyIso_inv_val (C := C) A q y

example (A : AddCommGrpCat.{u}) (q : ℕ)
    (x : zeroLocalizedCoreSubgroup (C := C) A q)
    (y : (nerve (ZeroComponent (C := C))).homology (C := AddCommGrpCat.{u}) A q) :
    (zeroLocalizedCoreHomologyIso (C := C) A q).inv
        ((zeroLocalizedCoreHomologyIso (C := C) A q).hom x) = x ∧
      (zeroLocalizedCoreHomologyIso (C := C) A q).hom
        ((zeroLocalizedCoreHomologyIso (C := C) A q).inv y) = y :=
  by
    let e : AddCommGrpCat.of (zeroLocalizedCoreSubgroup (C := C) A q) ≅
        (nerve (ZeroComponent (C := C))).homology (C := AddCommGrpCat.{u}) A q :=
      zeroLocalizedCoreHomologyIso (C := C) A q
    exact ⟨Iso.hom_inv_id_apply (C := AddCommGrpCat.{u}) e x,
      Iso.inv_hom_id_apply (C := AddCommGrpCat.{u}) e y⟩

example (A : AddCommGrpCat.{u}) (q : ℕ)
    (x : zeroLocalizedCoreSubgroup (C := C) A q) :
    (zeroLocalizedCoreSubgroupSplitMono (C := C) A q).retraction x.val = x :=
  ConcreteCategory.congr_hom (zeroLocalizedCoreSubgroupSplitMono (C := C) A q).id x

example (A : AddCommGrpCat.{u}) :
    Nonempty (AddCommGrpCat.of (zeroLocalizedCoreSubgroup (C := C) A 0) ≅
      (nerve (ZeroComponent (C := C))).homology (C := AddCommGrpCat.{u}) A 0) ∧
    Nonempty (AddCommGrpCat.of (zeroLocalizedCoreSubgroup (C := C) A 1) ≅
      (nerve (ZeroComponent (C := C))).homology (C := AddCommGrpCat.{u}) A 1) :=
  ⟨⟨zeroLocalizedCoreHomologyIso (C := C) A 0⟩,
    ⟨zeroLocalizedCoreHomologyIso (C := C) A 1⟩⟩

example (A : AddCommGrpCat.{u}) (q : ℕ) (t : Skeleton C)
    (x : (nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))).homology (C := AddCommGrpCat.{u})
        A q) :
    (zeroCoreFraction (C := C) A q t x :
      LocalizedModule (coreTranslationDenominators C) (coreTranslationHomologyModule C A q)) =
      LocalizedModule.mk (R := coreTranslationRing C) (S := coreTranslationDenominators C)
          (M := coreTranslationHomologyModule C A q)
        (((coreTranslationHomologyModuleAddCommGrpIso C A q).inv
          (SSet.homologyMap (C := AddCommGrpCat.{u})
            (nerveMap (coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι) A q x)) :
                coreTranslationHomologyModuleCat C A q)
        (coreTranslationDenominator C t) :=
  zeroCoreFraction_eq_mk (C := C) A q t x

example (A : AddCommGrpCat.{u}) (q : ℕ) (t : Skeleton C)
    (x : (nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))).homology (C := AddCommGrpCat.{u})
        A q) :
    (zeroCoreFractionMap (C := C) A q t x).val = zeroCoreFraction (C := C) A q t x :=
  zeroCoreFractionMap_apply (C := C) A q t x

example (A : AddCommGrpCat.{u}) (q : ℕ) (t : Skeleton C)
    (x y : (nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))).homology (C :=
        AddCommGrpCat.{u}) A q) :
    zeroCoreFraction (C := C) A q t (x + y) =
      zeroCoreFraction (C := C) A q t x + zeroCoreFraction (C := C) A q t y := by
  let m := zeroCoreFractionMap (C := C) A q t
  calc
    zeroCoreFraction (C := C) A q t (x + y) = (m (x + y)).val :=
      (zeroCoreFractionMap_apply (C := C) A q t (x + y)).symm
    _ = (m x).val + (m y).val := congrArg Subtype.val (map_add m.hom x y)
    _ = zeroCoreFraction (C := C) A q t x + zeroCoreFraction (C := C) A q t y :=
      congrArg₂ (fun a b => a + b)
        (zeroCoreFractionMap_apply (C := C) A q t x)
        (zeroCoreFractionMap_apply (C := C) A q t y)

example {J : Type u} [Category.{u} J]
    (A : AddCommGrpCat.{u}) (q : ℕ) (t : Skeleton C)
    (F : J ⥤ CoreGrade (C := C) (GrothendieckAddGroup.of t)) :
    (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap F) A q ≫ zeroCoreFractionMap (C := C) A q
        t) ≫
        (zeroLocalizedCoreHomologyIso (C := C) A q).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (F ⋙ positiveZeroFractionFunctor (C :=
          C) t)) A q := by
  let P : CoreGrade (C := C) (GrothendieckAddGroup.of t) ⥤ ZeroComponent (C := C) :=
    positiveZeroFractionFunctor (C := C) t
  let Xj : SSet.{u} := nerve J
  let Xg : SSet.{u} := nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))
  let Xz : SSet.{u} := nerve (ZeroComponent (C := C))
  let nF : Xj ⟶ Xg := nerveMap F
  let nP : Xg ⟶ Xz := nerveMap P
  let nFP : Xj ⟶ Xz := nerveMap (F ⋙ P)
  let H : SSet.{u} ⥤ AddCommGrpCat.{u} :=
    SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q
  let a : H.obj Xj ⟶ H.obj Xg := H.map nF
  have h := zeroCoreFractionMap_comp_homologyIso (C := C) A q t
  have hNerve : nF ≫ nP = nFP := nerveMap_comp F P
  have hComp : H.map nFP = a ≫ H.map nP :=
    (congrArg (fun arrow : Xj ⟶ Xz => H.map arrow) hNerve).symm.trans (H.map_comp nF nP)
  exact (Category.assoc a (zeroCoreFractionMap (C := C) A q t)
    (zeroLocalizedCoreHomologyIso (C := C) A q).hom).trans
      ((congrArg (fun k => a ≫ k) h).trans hComp.symm)


example (A : AddCommGrpCat.{u}) (q : ℕ) (t : Skeleton C) :
    (zeroCoreFractionMap (C := C) A q t ≫
        AddCommGrpCat.ofHom (zeroLocalizedCoreSubgroup (C := C) A q).subtype) ≫
          (secondTranslationBKLocalizedCoreHomologyIso (C := C) A q ≪≫
            swapHomologyIso (C := C) A q).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (positiveZeroFractionFunctor (C := C)
          t)) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (zeroComponentProperty (C := C)).ι) A
            q :=
  zeroCoreFractionMap_comp_canonical (C := C) A q t

example (A : AddCommGrpCat.{u}) (q : ℕ) (M : AddCommGrpCat.{u})
    (s : M →+ localizedWholeCoreHomologyGroup (C := C) A q)
    (h : ∀ (t : Skeleton C)
      (x : (nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))).homology (C :=
          AddCommGrpCat.{u}) A q),
      ∃ m : M, s m = (zeroCoreFractionMap (C := C) A q t x).val) :
    zeroLocalizedCoreSubgroup (C := C) A q ≤ s.range :=
  (zeroLocalizedCoreSubgroup_le_iff_fractionMap (C := C) A q s.range).mpr h

end CategoryTheory.SInverseS.ZeroGradeHomologyTests

example {C : Type 1} [Category.{1} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (A : AddCommGrpCat.{1}) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup (C := C) A q) ≅
      (nerve (CategoryTheory.SInverseS.ZeroComponent (C := C))).homology (C := AddCommGrpCat.{1}) A
          q) :=
  ⟨CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso (C := C) A q⟩

example {C : Type 2} [Category.{2} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (A : AddCommGrpCat.{2}) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (CategoryTheory.SInverseS.zeroLocalizedCoreSubgroup (C := C) A q) ≅
      (nerve (CategoryTheory.SInverseS.ZeroComponent (C := C))).homology (C := AddCommGrpCat.{2}) A
          q) :=
  ⟨CategoryTheory.SInverseS.zeroLocalizedCoreHomologyIso (C := C) A q⟩

end
