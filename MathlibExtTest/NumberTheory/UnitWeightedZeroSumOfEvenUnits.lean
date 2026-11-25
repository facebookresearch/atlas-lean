/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.NumberTheory.UnitWeightedZeroSumOfEvenUnits

namespace MetaMathlibExt

-- In modulus one even the zero entries are units.
example : ∃ a : Fin 2 → ZMod 1, (∀ i, IsUnit (a i)) ∧ ∑ i, a i * ![0, 0] i = 0 :=
  unitWeightedZeroSum_of_even_units (r := 0) ![0, 0] (by decide) (by decide)

-- In modulus eight the two units both occur as 1, and the nonunit 2 also contributes.
example : ∃ a : Fin 3 → ZMod 8, (∀ i, IsUnit (a i)) ∧ ∑ i, a i * ![1, 1, 2] i = 0 :=
  unitWeightedZeroSum_of_even_units (r := 3) ![1, 1, 2] (by decide) (by decide)

end MetaMathlibExt
