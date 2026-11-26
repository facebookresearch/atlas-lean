/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetryNontrivialSymmetryLengthThreeAndInfinite

/-!
# Tests for nontrivial Gauss–Kuzmin symmetries

These tests exclude a nontrivial symmetry for a concrete triple and derive existence at length
four. They also apply the characteristic-number criterion to reversed pairs, unequal triples,
and the empty string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2 and Theorem 3.
-/

namespace MathlibExtTest.NumberTheory.GaussKuzminSymmetryNontrivialSymmetryLengthThreeAndInfinite

open MetaMathlibExt

example : ¬ HasNontrivialSymmetry [1, 2, 3] := by
  exact nontrivialSymmetry_length_three_and_infinite.1 _ (by simp) rfl

example : ∃ a : List ℕ, a.length = 4 ∧ (∀ x ∈ a, 0 < x) ∧ HasNontrivialSymmetry a := by
  exact (nontrivialSymmetry_length_three_and_infinite.2 4 (by decide)).nonempty

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

end MathlibExtTest.NumberTheory.GaussKuzminSymmetryNontrivialSymmetryLengthThreeAndInfinite
