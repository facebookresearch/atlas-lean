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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutZeroCoherence

/-!
# Consumer checks for cofiber pushout zero coherence

Focused public-API checks for `levelwisePushout_comp_zero` and
`levelwisePushoutShortComplex`: the packaged short complex recovers both
induced maps `D.inducedMap01`/`D.inducedMap12`, the induced composite
`D.inducedMap01 ≫ D.inducedMap12` is zero from the two source-zero
hypotheses, and the `.zero` field witnesses that packaged composite.
Both `wS`/`wT` are explicit variables; omitting either fails elaboration.
Requires only `[Category C] [HasZeroMorphisms C]`. No `Preadditive`,
`HasZeroObject`, `ExactCategory`, or `WaldhausenCategoryWithoutGluing` hypotheses, no
`IsPushout.hom_ext` re-proof or leg-law fixtures, no admissible-mono/exact
or cofiber-sequence/category instance, no cokernel comparison, and no
additivity, `K₀`/G-theory, spectra, or Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutZeroCoherenceTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C]
variable (D : LevelwisePushoutData C)
variable (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
variable (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0)

-- Packaged `f` recovers the first induced map; fails on `f`/`g` swap or def drift.
example : (levelwisePushoutShortComplex C D wS wT).f = D.inducedMap01 :=
  levelwisePushoutShortComplex_f C D wS wT

-- Packaged `g` recovers the second induced map; fails on swap.
example : (levelwisePushoutShortComplex C D wS wT).g = D.inducedMap12 :=
  levelwisePushoutShortComplex_g C D wS wT

-- Composition orientation pins `inducedMap01 ≫ inducedMap12 = 0`; fails on flip.
example : D.inducedMap01 ≫ D.inducedMap12 = 0 :=
  levelwisePushout_comp_zero C D wS wT

-- Packaged `.zero` witnesses the short-complex composite; needs both `wS`/`wT`.
example : (levelwisePushoutShortComplex C D wS wT).f ≫
    (levelwisePushoutShortComplex C D wS wT).g = 0 :=
  (levelwisePushoutShortComplex C D wS wT).zero

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutZeroCoherenceTests
