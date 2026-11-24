/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStageTransposeExact

/-!
# Clients for the full original relative cofiber-stage transpose

The named relative/general stage values, complete cofiber functor sequence,
actual base map, whole flipped diagram and map, arbitrary simplex operators,
and degree-zero carriers are retained with independent object/Hom universes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.CofiberRelativeStageTransposeExactTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original relative Waldhausen value on the tested source cofiber category. -/
local instance originalRelativeWaldhausen : WaldhausenCategoryWithoutGluing
    (CofiberSequenceCategory C) :=
  relativeWaldhausenCategory C

local instance originalStageZero (n : ℕ) : HasZeroObject (Stage C n) :=
  generalStageHasZeroObject C n

/-- The original general Waldhausen value on each tested target finite stage. -/
local instance originalStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing (Stage C n) :=
  generalStageWaldhausenCategory C n

local instance originalRelativeStageZero (n : ℕ) :
    HasZeroObject (Stage (CofiberSequenceCategory C) n) :=
  generalStageHasZeroObject (CofiberSequenceCategory C) n

/-- The original general stage value over the tested source relative cofiber category. -/
local instance originalRelativeStageWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (Stage (CofiberSequenceCategory C) n) :=
  generalStageWaldhausenCategory (CofiberSequenceCategory C) n

/-- The original relative cofiber value over the tested target general stage category. -/
local instance originalTargetRelativeWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C n)) :=
  relativeWaldhausenCategory (Stage C n)

/-- The original whole relative transpose is exact in all original degrees. -/
theorem originalFullRelativeExactness (n : ℕ) :
    (relativeStageTranspose C n).IsWaldhausenExact :=
  relativeStageTranspose_isWaldhausenExact C n

/-- The entire original evaluation sequence has its genuine base condition. -/
theorem originalFullFunctorSequence (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence
      ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
      ((stageEvaluationTriangle C n).obj 2)
      (stageSourceToMiddle C n) (stageMiddleToQuotient C n) :=
  stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n

/-- Every original stage object retains its actual cofiber triangle. -/
theorem originalObjectCofiberSequence (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) :
    IsCofiberSequence ((stageSourceToMiddle C n).app A)
      ((stageMiddleToQuotient C n).app A) :=
  stageTriangle_isCofiberSequence C n A

/-- The base map is the original stock pushout descent, with all stage corners earned. -/
theorem originalBaseCofibration (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) (hφ : IsCofibration φ) :
    letI : HasPushout ((stageSourceToMiddle C n).app A)
        (((stageEvaluationTriangle C n).obj 0).map φ) := (by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
        (C := Stage C n) ((stageSourceToMiddle C n).app A)
        (stageTriangle_isCofiberSequence C n A).1
        (((stageEvaluationTriangle C n).obj 0).obj B)
        (((stageEvaluationTriangle C n).obj 0).map φ)
      exact hP.flip.hasPushout)
    IsCofibration (pushout.desc (((stageEvaluationTriangle C n).obj 1).map φ)
      ((stageSourceToMiddle C n).app B) ((stageSourceToMiddle C n).naturality φ).symm) :=
  stageTriangle_baseCofibration C n φ hφ

/-- The whole original transposed diagram retains both complete index directions. -/
theorem originalWholeDiagram (n : ℕ) (A : Stage (CofiberSequenceCategory C) n) :
    ((relativeStageTranspose C n).obj A).obj ⋙ SConstruction.forget C n =
      (A.obj ⋙ CofiberSequenceCategory.forget C).flip :=
  relativeStageTranspose_obj_forget C n A

/-- Every original coefficient is retained on the complete transposed diagram. -/
theorem originalCoefficient (n : ℕ) (A : Stage (CofiberSequenceCategory C) n)
    (t : Fin 3) (x : Ar n) :
    ((((relativeStageTranspose C n).obj A).obj.obj t).obj.obj x) =
      (A.obj.obj x).obj.obj t :=
  relativeStageTranspose_obj_app C n A t x

/-- The whole original stage morphism retains its full flipped natural transformation. -/
theorem originalWholeMap (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) :
    HEq (Functor.whiskerRight ((relativeStageTranspose C n).map φ).hom
      (SConstruction.forget C n))
      ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
        (Functor.whiskerRight φ.hom (CofiberSequenceCategory.forget C))) :=
  relativeStageTranspose_map_forget_heq C n φ

/-- Every complete scalar map is the original scalar map in both original indices. -/
theorem originalScalarMap (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) (t : Fin 3) (x : Ar n) :
    HEq ((((relativeStageTranspose C n).map φ).hom.app t).hom.app x)
      ((φ.hom.app x).hom.app t) :=
  relativeStageTranspose_map_app_heq C n φ t x

/-- The output relative cofibration is derived from the genuine original stage cofibration. -/
theorem originalRelativeCofibration (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B)
    (hφ : stageCofibrations (CofiberSequenceCategory C) n φ) :
    relativeCofibrations (Stage C n) ((relativeStageTranspose C n).map φ) :=
  relativeStageTranspose_map_relativeCofibration C n φ hφ

/-- The entire original source pushout is preserved by the same full transpose. -/
theorem originalPushout (n : ℕ)
    {A B A' P : Stage (CofiberSequenceCategory C) n}
    (i : A ⟶ B) (f : A ⟶ A') (inl : A' ⟶ P) (inr : B ⟶ P)
    (hi : IsCofibration i) (hP : IsPushout f i inl inr) :
    IsPushout ((relativeStageTranspose C n).map f) ((relativeStageTranspose C n).map i)
      ((relativeStageTranspose C n).map inl) ((relativeStageTranspose C n).map inr) :=
  relativeStageTranspose_map_pushout C n i f inl inr hi hP

/-- All original simplex operators commute with the actual full relative transpose. -/
theorem originalEveryReindex {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := CofiberSequenceCategory C) f ⋙ relativeStageTranspose C a.len =
      relativeStageTranspose C b.len ⋙
        mapOfWaldhausenExact (reindexStage (C := C) f)
          (reindexStage_general_isWaldhausenExact C f) :=
  relativeStageTranspose_reindex C f

/-- Degree zero retains the original relative category of the actual zero stages. -/
theorem originalDegreeZeroExactness :
    (relativeStageTransposeZero C).IsWaldhausenExact :=
  relativeStageTransposeZero_isWaldhausenExact C

end MathlibExtTest.KTheory.Waldhausen.CofiberRelativeStageTransposeExactTests

end
