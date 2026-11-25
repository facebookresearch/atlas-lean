/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWaldhausenExact
public import MathlibExt.CategoryTheory.Waldhausen.WeakFunctor

/-!
# The original degree-one weak-stage equivalence

The exact original S1 insertion and evaluation restrict to their original
weak wide categories. The actual categorical S1 unit and counit are
pointwise isomorphisms, hence original weak maps. They construct an
actual equivalence of the original weak categories, preserving the
original unique interval object and morphism readouts.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Original S1 insertion restricted through the canonical exact weak-functor API. -/
def stageOneGeneralWeak : WeakCategory C ⥤ StageWeakCategory C 1 := by
  letI : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  letI : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  exact (stageOne_general_isWaldhausenExact C).mapWeakCategory

/-- Original S1 evaluation restricted through that same canonical weak-functor API. -/
def stageOneEvalGeneralWeak : StageWeakCategory C 1 ⥤ WeakCategory C := by
  letI : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  letI : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  exact (stageOneEval_general_isWaldhausenExact C).mapWeakCategory

/-- The original weak S1 insertion retains the original stage object. -/
theorem stageOneGeneralWeak_obj (X : WeakCategory C) :
    ((stageOneGeneralWeak C).obj X).obj = (stageOne C).obj X.obj := rfl

/-- The original weak S1 evaluation retains the original unique off-diagonal object. -/
theorem stageOneEvalGeneralWeak_obj (X : StageWeakCategory C 1) :
    ((stageOneEvalGeneralWeak C).obj X).obj = (stageOneEval C).obj X.obj := rfl

/-- The actual categorical S1 unit lifts to the same original input weak maps. -/
def stageOneGeneralWeakUnit : 𝟭 (WeakCategory C) ≅
    stageOneGeneralWeak C ⋙ stageOneEvalGeneralWeak C :=
  NatIso.ofComponents (fun X => by
    let e := (stageOneEvalUnit C).app X.obj
    letI : IsIso e.hom := e.isIso_hom
    letI : IsIso e.inv := e.symm.isIso_hom
    exact WideSubcategory.isoMk e
      ((WaldhausenCategoryWithoutGluing.weakEquivalences (C :=
        C)).isomorphisms_le_of_containsIdentities e.hom e.isIso_hom)
      ((WaldhausenCategoryWithoutGluing.weakEquivalences (C :=
        C)).isomorphisms_le_of_containsIdentities e.inv e.symm.isIso_hom))
    (by intro X Y f; apply WideSubcategory.hom_ext; exact (stageOneEvalUnit C).hom.naturality f.hom)

/-- The actual categorical S1 counit lifts to the same original weak-stage maps. -/
def stageOneGeneralWeakCounit : stageOneEvalGeneralWeak C ⋙ stageOneGeneralWeak C ≅
    𝟭 (StageWeakCategory C 1) :=
  NatIso.ofComponents (fun X => by
    let e := (stageOneEvalCounit C).app X.obj
    letI : IsIso e.hom := e.isIso_hom
    letI : IsIso e.inv := e.symm.isIso_hom
    exact WideSubcategory.isoMk e
      ((stageWeak C 1).isomorphisms_le_of_containsIdentities e.hom e.isIso_hom)
      ((stageWeak C 1).isomorphisms_le_of_containsIdentities e.inv e.symm.isIso_hom))
    (by intro X Y f; apply WideSubcategory.hom_ext; exact
        (stageOneEvalCounit C).hom.naturality f.hom)

/-- The original S1 weak categories are equivalent through actual insertion and evaluation. -/
def stageOneGeneralWeakEquivalence : WeakCategory C ≌ StageWeakCategory C 1 :=
  Equivalence.mk (stageOneGeneralWeak C) (stageOneEvalGeneralWeak C)
    (stageOneGeneralWeakUnit C) (stageOneGeneralWeakCounit C)

end CategoryTheory.Waldhausen.SConstruction
