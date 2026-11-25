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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutCofibrationSequence

/-!
# Consumer check for cofiber-sequence bridge

Focused public-API check for `isCofibrationSequence_levelwisePushout`:
admissible exactness of the assembled levelwise pushout short complex yields
the cofibration sequence on `D.inducedMap01`/`D.inducedMap12`, exposing the
`IsPushout` orientation. No exactness or universal-property re-proof, no
fixture/helper/instance, no additivity, `K₀`/G-theory, spectra, or Q/S
comparison.
-/

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace CofiberPushoutCofibrationSequenceTests

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : LevelwisePushoutData C)
variable (wS : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0)
variable (wT : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0)
variable (h : ExactCategory.IsAdmissibleExact (levelwisePushoutShortComplex C D wS wT))

-- Bridge invokes the named theorem; pins induced maps and orientation.
example : @IsCofibrationSequence C _ _ (ExactCategory.waldhausenCategory C)
    D.P0 D.P1 D.P2 D.inducedMap01 D.inducedMap12 :=
  isCofibrationSequence_levelwisePushout C D wS wT h

-- Destructured `IsPushout` orientation on the induced maps; fails on leg flip.
example : ∃ (h0 : D.P0 ⟶ (0 : C)) (q : (0 : C) ⟶ D.P2),
    IsPushout h0 D.inducedMap01 q D.inducedMap12 :=
  (isCofibrationSequence_levelwisePushout C D wS wT h).2

end CofiberPushoutCofibrationSequenceTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
