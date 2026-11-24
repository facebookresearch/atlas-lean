/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequenceStageExact

/-!
# Clients for the original four-role cofiber functor-sequence stage stability

The legitimate original source sequence gives the same three stage functors,
same postwhiskered arrows, complete base condition, whole lifted diagram and
map, and every original reindex operator. Degree zero retains the original stages.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe uD vD uC vC

namespace MathlibExtTest.KTheory.Waldhausen.CofiberFunctorSequenceStageExactTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {F₀ F₁ F₂ : D ⥤ C} {i : F₀ ⟶ F₁} {p : F₁ ⟶ F₂}
variable (H : IsWaldhausenCofiberFunctorSequence F₀ F₁ F₂ i p)

/-- The original relative Waldhausen value on the tested lifted target cofiber category. -/
local instance originalRelativeWaldhausen : WaldhausenCategoryWithoutGluing
    (CofiberSequenceCategory C) :=
  CofiberSequenceCategory.relativeWaldhausenCategory C

local instance originalSourceStageZero (n : ℕ) : HasZeroObject (Stage D n) :=
  generalStageHasZeroObject D n

/-- The original general Waldhausen value on each tested source finite stage. -/
local instance originalSourceStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing
    (Stage D n) :=
  generalStageWaldhausenCategory D n

local instance originalTargetStageZero (n : ℕ) : HasZeroObject (Stage C n) :=
  generalStageHasZeroObject C n

/-- The original general Waldhausen value on each tested target finite stage. -/
local instance originalTargetStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing
    (Stage C n) :=
  generalStageWaldhausenCategory C n

local instance originalRelativeStageZero (n : ℕ) :
    HasZeroObject (Stage (CofiberSequenceCategory C) n) :=
  generalStageHasZeroObject (CofiberSequenceCategory C) n

/-- The original general stage value over the tested lifted target relative cofiber category. -/
local instance originalRelativeStageWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (Stage (CofiberSequenceCategory C) n) :=
  generalStageWaldhausenCategory (CofiberSequenceCategory C) n

/-- The original relative cofiber value over each tested target general stage category. -/
local instance originalStageRelativeWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C n)) :=
  CofiberSequenceCategory.relativeWaldhausenCategory (Stage C n)

/-- All four original category roles give the exact original staged sequence. -/
theorem originalAllStages (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence (H.sourceExact.mapStage n)
      (H.middleExact.mapStage n) (H.quotientExact.mapStage n)
      (H.sourceExact.mapStageNatTrans H.middleExact i n)
      (H.middleExact.mapStageNatTrans H.quotientExact p n) := H.mapStage n

/-- The same original lift followed by the full relative transpose is exact. -/
theorem originalLiftExactness (n : ℕ) : (H.stageLift n).IsWaldhausenExact :=
  H.stageLift_isWaldhausenExact n

/-- The whole actual composite is the same stock lift of the earned staged sequence. -/
theorem originalLiftIdentity (n : ℕ) :
    H.stageLift n = cofiberFunctorSequenceLift (H.sourceExact.mapStage n)
      (H.middleExact.mapStage n) (H.quotientExact.mapStage n)
      (H.sourceExact.mapStageNatTrans H.middleExact i n)
      (H.middleExact.mapStageNatTrans H.quotientExact p n) (H.mapStage n).objectwise :=
  H.stageLift_eq n

/-- Every target stage cofiber sequence is internally earned from the original source sequence. -/
theorem originalObjectwiseSequence (n : ℕ) (A : Stage D n) :
    IsCofiberSequence ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
      ((H.middleExact.mapStageNatTrans H.quotientExact p n).app A) :=
  H.mapStage_objectwise n A

/-- The original stock base descent is a genuine stage cofibration in the target. -/
theorem originalBaseCofibration (n : ℕ) {A B : Stage D n} (φ : A ⟶ B)
    (hφ : IsCofibration φ) :
    letI : HasPushout ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
        ((H.sourceExact.mapStage n).map φ) := (by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
        (C := Stage C n) ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
        (H.mapStage_objectwise n A).1 ((H.sourceExact.mapStage n).obj B)
        ((H.sourceExact.mapStage n).map φ)
      exact hP.flip.hasPushout)
    IsCofibration (pushout.desc ((H.middleExact.mapStage n).map φ)
      ((H.sourceExact.mapStageNatTrans H.middleExact i n).app B)
      ((H.sourceExact.mapStageNatTrans H.middleExact i n).naturality φ).symm) :=
  H.mapStage_baseCofibration n φ hφ

/-- The whole original flag and source cofiber diagram are retained in both directions. -/
theorem originalWholeDiagram (n : ℕ) (A : Stage D n) :
    ((H.stageLift n).obj A).obj ⋙ SConstruction.forget C n =
      (A.obj ⋙ functorSequenceDiagram F₀ F₁ F₂ i p).flip := H.stageLift_obj_forget n A

/-- The original full flag morphism acts on the same full source cofiber diagram. -/
theorem originalWholeMap (n : ℕ) {A B : Stage D n} (φ : A ⟶ B) :
    HEq (Functor.whiskerRight ((H.stageLift n).map φ).hom (SConstruction.forget C n))
      ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
        (Functor.whiskerRight φ.hom (functorSequenceDiagram F₀ F₁ F₂ i p))) :=
  H.stageLift_map_forget_heq n φ

/-- Every original simplex operator commutes with the entire original stage lift. -/
theorem originalEveryReindex {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := D) f ⋙ H.stageLift a.len =
      H.stageLift b.len ⋙ CofiberSequenceCategory.mapOfWaldhausenExact
        (reindexStage (C := C) f) (reindexStage_general_isWaldhausenExact C f) :=
  H.stageLift_reindex f

/-- Every first-arrow component is the actual original source-sequence component. -/
theorem originalFirstComponent (n : ℕ) (A : Stage D n) (x : Ar n) :
    ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A).hom.app x =
      i.app (A.obj.obj x) := H.mapStage_firstArrow_app n A x

/-- Every quotient-arrow component is the actual original source-sequence component. -/
theorem originalQuotientComponent (n : ℕ) (A : Stage D n) (x : Ar n) :
    ((H.middleExact.mapStageNatTrans H.quotientExact p n).app A).hom.app x =
      p.app (A.obj.obj x) := H.mapStage_secondArrow_app n A x

/-- Degree zero uses the same original source and target zero-stage categories. -/
theorem originalDegreeZero :
    IsWaldhausenCofiberFunctorSequence (H.sourceExact.mapStage 0)
      (H.middleExact.mapStage 0) (H.quotientExact.mapStage 0)
      (H.sourceExact.mapStageNatTrans H.middleExact i 0)
      (H.middleExact.mapStageNatTrans H.quotientExact p 0) := H.mapStage_zero

end MathlibExtTest.KTheory.Waldhausen.CofiberFunctorSequenceStageExactTests

end
