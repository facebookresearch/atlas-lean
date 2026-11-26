/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetryGaussKuzminMassEqIffCharacteristicNumberEq

/-!
# Tests for equality of Gauss–Kuzmin masses

These tests apply the characteristic-number criterion to reversed pairs, unequal triples,
and the empty string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2.
-/

namespace MathlibExtTest.NumberTheory
namespace GaussKuzminSymmetryGaussKuzminMassEqIffCharacteristicNumberEq

open MetaMathlibExt

example : gaussKuzminMass [1, 2] = gaussKuzminMass [2, 1] := by
  exact (gaussKuzminMass_eq_iff_characteristicNumber_eq [1, 2] [2, 1]
    (by decide) (by decide) (by decide)).mpr (by decide)

example : gaussKuzminMass [1, 2, 2] ≠ gaussKuzminMass [2, 1, 2] := by
  intro h
  have hc := (gaussKuzminMass_eq_iff_characteristicNumber_eq [1, 2, 2] [2, 1, 2]
    (by decide) (by decide) (by decide)).mp h
  exact (by decide : characteristicNumber [1, 2, 2] ≠ characteristicNumber [2, 1, 2]) hc

example : gaussKuzminMass [] ≠ gaussKuzminMass [1, 1] := by
  intro h
  have hc := (gaussKuzminMass_eq_iff_characteristicNumber_eq [] [1, 1]
    (by simp) (by decide) (by decide)).mp h
  exact (by decide : characteristicNumber [] ≠ characteristicNumber [1, 1]) hc

end GaussKuzminSymmetryGaussKuzminMassEqIffCharacteristicNumberEq
end MathlibExtTest.NumberTheory
