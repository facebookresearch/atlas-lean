/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanChains
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslation

/-! # Tests for right-comma Bousfield--Kan chain comparison -/

@[expose] public section

#check SSet.rightCommaTotalToSource_quasiIso_chainComplexMap
#check SSet.rightCommaTotalToSource_quasiIso_chainComplexMap_addCommGrp
#check SSet.rightCommaBKTotalSourceHomologyIso
#check SSet.rightCommaBKTotalSourceHomologyIso_addCommGrp

#print axioms SSet.rightCommaTotalToSource_quasiIso_chainComplexMap
#print axioms SSet.rightCommaTotalToSource_quasiIso_chainComplexMap_addCommGrp
#print axioms SSet.rightCommaBKTotalSourceHomologyIso
#print axioms SSet.rightCommaBKTotalSourceHomologyIso_addCommGrp

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

/-- Module chains keep their original source with object universe zero and Hom universe one. -/
example {C D : Type} [Category.{1} C] [Category.{1} D]
    {R : Type 1} [Ring R] (A : ModuleCat.{1} R) (F : C ⥤ D) :
    QuasiIso (SSet.chainComplexMap (SSet.rightCommaTotalToSource F) A) :=
  SSet.rightCommaTotalToSource_quasiIso_chainComplexMap A F

/-- The same positive-Hom source comparison accepts an arbitrary abelian group. -/
example {C D : Type} [Category.{1} C] [Category.{1} D]
    (A : AddCommGrpCat.{1}) (F : C ⥤ D) :
    QuasiIso (SSet.chainComplexMap (SSet.rightCommaTotalToSource F) A) :=
  SSet.rightCommaTotalToSource_quasiIso_chainComplexMap_addCommGrp A F

/-- The signed total and original source remain the endpoints in every module-homology degree. -/
example {C D : Type} [Category.{1} C] [Category.{1} D]
    {R : Type 1} [Ring R] (A : ModuleCat.{1} R) (F : C ⥤ D) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex (ModuleCat.{1} R) A
      (SSet.rightCommaNerveDiagram F)).homology n ≅
        ((CategoryTheory.nerve C).chainComplex A).homology n :=
  SSet.rightCommaBKTotalSourceHomologyIso A F n

/-- Abelian-group homology retains all degrees at the same positive-Hom boundary. -/
example {C D : Type} [Category.{1} C] [Category.{1} D]
    (A : AddCommGrpCat.{1}) (F : C ⥤ D) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex AddCommGrpCat.{1} A
      (SSet.rightCommaNerveDiagram F)).homology n ≅
        ((CategoryTheory.nerve C).chainComplex A).homology n :=
  SSet.rightCommaBKTotalSourceHomologyIso_addCommGrp A F n

/-- The actual stabilized-pair projection uses its original larger Hom universe. -/
example (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (A : AddCommGrpCat.{max u v}) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex AddCommGrpCat.{max u v} A
      (SSet.rightCommaNerveDiagram
        (CategoryTheory.SInverseS.translationProjection (C := C)))).homology n ≅
      ((CategoryTheory.nerve (CategoryTheory.SInverseS.Pair C)).chainComplex A).homology n :=
  SSet.rightCommaBKTotalSourceHomologyIso_addCommGrp A _ n

end

end
