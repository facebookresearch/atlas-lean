/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticPackingPolynomials
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.ShearedTwelveSeventhsTest

private noncomputable abbrev shearedLattice : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (p.1 - 1 / 2 * p.2, p.2)) '' sectorLatticePoints ((12 : ℝ) / 7)

private noncomputable abbrev polynomial (p : ℝ × ℝ) : ℝ :=
  6 * p.1 * (p.1 - 3 / 2) + p.1 + 3 / 2 * p.2 + 2

-- The shear of (1, 1) has a half-integral first coordinate and gives the value 1.
example : (1 / 2, 1) ∈ shearedLattice ∧ polynomial (1 / 2, 1) = 1 := by
  exact ⟨⟨(1, 1), ⟨1, 1, by norm_num⟩, by norm_num⟩, by norm_num [polynomial]⟩

-- The boundary point (7, 12) shears to the unique preimage of 18.
example {p : ℝ × ℝ} (hp : p ∈ shearedLattice) : polynomial p = 18 ↔ p = (1, 12) := by
  have hmem : ((1, 12) : ℝ × ℝ) ∈ shearedLattice :=
    ⟨(7, 12), ⟨7, 12, by norm_num⟩, by norm_num⟩
  have hval : polynomial (1, 12) = 18 := by norm_num [polynomial]
  constructor
  · intro h
    exact isQuadraticPackingPolynomial_sheared_example_twelve_sevenths.2.injOn
      hp hmem (h.trans hval.symm)
  · rintro rfl
    exact hval

end MetaMathlibExt.ShearedTwelveSeventhsTest
