/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EllipticCurveTwoPQRank
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

namespace MathlibExtTest.EllipticCurveTwoPQRank

private abbrev curve (p q : ℕ) : WeierstrassCurve ℚ := ⟨0, 0, 0, -(2 * p * q : ℚ), 0⟩

-- The residue-table branch, with primes congruent to 3 and 5.
example (hparity : Odd (Module.finrank ℤ (curve 3 5).toProjective.Point)) :
    Module.finrank ℤ (curve 3 5).toProjective.Point = 1 :=
  MetaMathlibExt.finrank_point_two_mul_mul_eq_one (p := 3) (q := 5)
    (hp := by norm_num) (hq := by norm_num) (hpq := by decide)
    (E := curve 3 5) (hE := rfl) (hcase := Or.inl (by decide)) hparity

-- The nonresidue branch, with 17 congruent to 1 modulo 8 and to 2 modulo 3.
example (hparity : Odd (Module.finrank ℤ (curve 17 3).toProjective.Point)) :
    Module.finrank ℤ (curve 17 3).toProjective.Point = 1 :=
  MetaMathlibExt.finrank_point_two_mul_mul_eq_one (p := 17) (q := 3)
    (hp := by norm_num) (hq := by norm_num) (hpq := by decide)
    (E := curve 17 3) (hE := rfl) (hcase := Or.inr ⟨rfl, by decide, by norm_num⟩) hparity

end MathlibExtTest.EllipticCurveTwoPQRank
