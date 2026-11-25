/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFirstQuotientDecomposition

/-!
# Clients for the original first-entry/first-face source decomposition

The actual source cofiber condition, whole split-return comparison and
all original interval roles are retained. Degree zero keeps `A11` and
`Q00` as their actual original zero objects.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.StageFirstQuotientDecompositionTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open CategoryTheory.Waldhausen.SConstruction.StageFirstQuotient

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The full source cofibration-sequence certificate uses the original named stage value. -/
theorem originalSourceCertificate (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    IsWaldhausenCofiberFunctorSequence (firstEndo C n) (𝟭 (Stage C (n + 1)))
      (quotientEndo C n) (sourceInclusion C n) (quotientProjection C n) :=
  isWaldhausenCofiberFunctorSequence C n

/-- Every original stage has the actual original first-step cofiber sequence. -/
theorem originalObjectwiseSequence (n : ℕ) (A : Stage C (n + 1)) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    IsCofiberSequence ((sourceInclusion C n).app A) ((quotientProjection C n).app A) :=
  objectwise_isCofiberSequence C n A

/-- The actual first-entry value is the whole original interval `A01`. -/
theorem originalFirstEntry (n : ℕ) (A : Stage C (n + 1)) :
    (source C n).obj A = A.obj.obj (interval 0 (firstIndex n) (Fin.zero_le _)) :=
  source_obj C n A

/-- The source inclusion keeps its entire actual counit and original clamp component. -/
theorem originalInclusionMap (n : ℕ) (A : Stage C (n + 1)) :
    (sourceInclusion C n).app A =
      (firstEndoIso C n).hom.app A ≫ (clampInclusion C n).app A :=
  sourceInclusion_app C n A

/-- The stock relative lift has its exactness earned from the source certificate. -/
theorem originalExactLift (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C (n + 1))) :=
      CofiberSequenceCategory.relativeWaldhausenCategory (Stage C (n + 1))
    (cofiberLift C n).IsWaldhausenExact :=
  cofiberLift_isWaldhausenExact C n

/-- The whole stock cofiber middle is the unchanged original stage functor. -/
theorem originalWholeMiddle (n : ℕ) :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    cofiberLift C n ⋙ CofiberSequenceCategory.middle (Stage C (n + 1)) =
      𝟭 (Stage C (n + 1)) :=
  cofiberLift_middle C n

/-- The actual split return followed by the original projection has its whole natural Iso. -/
def originalSplitReturnIso (n : ℕ) :
    splitReturn C n ⋙ projection C n ≅ 𝟭 (C × Stage C n) :=
  splitReturnProjectionIso C n

/-- The entire split-return map retains both original components and
the same original stage coproduct. -/
theorem originalSplitReturnMap (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {Q Q' : Stage C n} (g : Q ⟶ Q') :
    letI : HasZeroObject (Stage C (n + 1)) := generalStageHasZeroObject C (n + 1)
    letI : WaldhausenCategoryWithoutGluing (Stage C (n + 1)) :=
      generalStageWaldhausenCategory C (n + 1)
    (splitReturn C n).map (X := (X, Q)) (Y := (Y, Q')) (f, g) =
      (waldhausenCoproductFunctor (Stage C (n + 1))).map
        (X := ((insert C n).obj X, (degenerateReturn C n).obj Q))
        (Y := ((insert C n).obj Y, (degenerateReturn C n).obj Q'))
        ((insert C n).map f, (degenerateReturn C n).map g) :=
  splitReturn_map C n f g

/-- Degree zero retains `A11` rather than equating it to a chosen zero object. -/
theorem originalDegreeZeroDiagonal (A : Stage C 1) :
    ((zeroEndo C 0).obj A).obj.obj (interval (0 : Fin 2) 1 (by decide)) =
      A.obj.obj (diag (1 : Fin 2)) := by
  rw [zeroEndo_obj, firstIndex_eq_one]

/-- The degree-zero split return retains the actual original `Q00` coproduct input. -/
def originalDegreeZeroFirstInterval (X : C) (Q : Stage C 0) :
    ((splitReturn C 0).obj (X, Q)).obj.obj
        (interval 0 (firstIndex 0) (Fin.zero_le _)) ≅
      (waldhausenCoproductFunctor C).obj (X, Q.obj.obj (diag (0 : Fin 1))) :=
  splitReturnFirstIntervalIso C 0 X Q

end MathlibExtTest.KTheory.Waldhausen.StageFirstQuotientDecompositionTests

end
