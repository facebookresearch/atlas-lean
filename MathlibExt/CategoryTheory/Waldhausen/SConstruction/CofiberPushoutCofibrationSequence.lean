/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutZeroCoherence

/-!
# Exact-category cofiber-sequence bridge for the levelwise pushout

Smallest sound bridge from admissible exactness of the assembled levelwise
pushout short complex to a Waldhausen cofibration sequence in the standard
structure `ExactCategory.waldhausenCategory C`.

Reuse `levelwisePushoutShortComplex` and its `_f`/`_g`
computation lemmas, plus `ExactCategory.isCofibrationSequence_of_isAdmissibleExact`.
No duplicate universal-property proof, wrapper, or instance is introduced here.

Requires `[Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]`
`[ExactCategory C]`; the `[HasZeroMorphisms C]` needed by the packaged complex
is supplied by the preadditive instance.

Nonclaims: no `WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C)` instance,
no gluing, additivity, `K₀`/G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

/-- Admissible exactness of the assembled levelwise pushout yields the
corresponding cofibration sequence on the induced maps in the standard
exact-category Waldhausen structure. -/
theorem isCofibrationSequence_levelwisePushout (D : LevelwisePushoutData C)
    (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
    (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0)
    (h : ExactCategory.IsAdmissibleExact (levelwisePushoutShortComplex C D wS wT)) :
    @IsCofibrationSequence C _ _ (ExactCategory.waldhausenCategory C)
      D.P0 D.P1 D.P2 D.inducedMap01 D.inducedMap12 := by
  have hSeq := ExactCategory.isCofibrationSequence_of_isAdmissibleExact h
  simpa only [levelwisePushoutShortComplex, levelwisePushoutShortComplex_f,
    levelwisePushoutShortComplex_g] using hSeq

end CategoryTheory.Waldhausen.SConstruction
