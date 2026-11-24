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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeWaldhausen
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

import Mathlib.Tactic.FinCases

/-!
# Exact evaluation of general cofiber sequences

The actual relative pushout presentation gives component pushouts for the
three evaluations. The stock span-preservation criterion then proves
preservation of every pushout along a relative cofibration. Together with
the derived component cofibrations, the existing component weak equivalences
and zero-object preservation, this proves Waldhausen exactness.

The same named extension-category value is installed locally in every
statement and proof. No E(C) Waldhausen or evaluation-exactness witness is
an input.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- Evaluation at every original row position is Waldhausen exact for the
same named general extension-category value. -/
theorem evaluationIsRelativeWaldhausenExact (k : Fin 3) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    ((forget C) ⋙ (evaluation (Fin 3) C).obj k).IsWaldhausenExact := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  refine {
    map_isZero := ?_
    map_cofibration := ?_
    map_weakEquivalence := ?_
    map_pushout := ?_ }
  · intro X hX
    let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
    exact ((evaluation (Fin 3) C).obj k).map_isZero ((forget C).map_isZero hX)
  · intro X Y f hf
    have hrel := (isCofibration_relativeWaldhausenCategory_iff C f).mp hf
    have hparts := relativeCofibrations_components C f hrel
    fin_cases k
    · exact hparts.1
    · exact hparts.2.1
    · exact hparts.2.2
  · intro X Y f hf
    have hweak := (isWeakEquivalence_relativeWaldhausenCategory_iff C f).mp hf
    have hparts := (mem_levelwiseWeakEquivalences_iff C f).mp hweak
    fin_cases k
    · exact hparts.1
    · exact hparts.2.1
    · exact hparts.2.2
  · intro X Y X' Q i f inl inr hi hPushout
    have hrel := (isCofibration_relativeWaldhausenCategory_iff C i).mp hi
    let P := CofiberRelativePushoutPresentation.ofRelativeCofibration (C := C) i f hrel
    have hEval : IsPushout
        (((forget C) ⋙ (evaluation (Fin 3) C).obj k).map f)
        (((forget C) ⋙ (evaluation (Fin 3) C).obj k).map i)
        (((forget C) ⋙ (evaluation (Fin 3) C).obj k).map P.inl)
        (((forget C) ⋙ (evaluation (Fin 3) C).obj k).map P.inr) := by
      fin_cases k
      · exact P.sourceIsPushout
      · exact P.middleIsPushout
      · exact P.quotientIsPushout
    let : PreservesColimit (span f i) ((forget C) ⋙ (evaluation (Fin 3) C).obj k) :=
      (P.isPushout.preservesColimit_span_iff
        (F := (forget C) ⋙ (evaluation (Fin 3) C).obj k)).mpr hEval
    exact hPushout.map ((forget C) ⋙ (evaluation (Fin 3) C).obj k)

/-- The existing source evaluation is exact for the named general
extension-category Waldhausen value. -/
theorem sourceIsRelativeWaldhausenExact :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    (source C).IsWaldhausenExact := by
  simpa only [source] using
    evaluationIsRelativeWaldhausenExact C (⟨0, by decide⟩ : Fin 3)

/-- The existing middle evaluation is exact for the named general
extension-category Waldhausen value. -/
theorem middleIsRelativeWaldhausenExact :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    (middle C).IsWaldhausenExact := by
  simpa only [middle] using
    evaluationIsRelativeWaldhausenExact C (⟨1, by decide⟩ : Fin 3)

/-- The existing quotient evaluation is exact for the named general
extension-category Waldhausen value. -/
theorem quotientIsRelativeWaldhausenExact :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    (quotient C).IsWaldhausenExact := by
  simpa only [quotient] using
    evaluationIsRelativeWaldhausenExact C (⟨2, by decide⟩ : Fin 3)

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
