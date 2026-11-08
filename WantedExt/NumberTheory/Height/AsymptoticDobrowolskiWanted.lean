/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Height.AsymptoticDobrowolski

/-!
# Known Dobrowolski and earlier Mahler-measure bounds

These five literature results are private requests, not completed proofs. The actual polynomial,
height and optimization model, including the strict/non-strict equivalence, are implemented
upstream.
Sources: catalogue C40b and Voutier, arXiv:1211.3110v1, Introduction, lines 68–87 and 104–117.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.AsymptoticDobrowolski

open NumberField

/-- Source: Dobrowolski (1979), as reported by Voutier, coefficient `1`. -/
theorem_wanted dobrowolski_one_le_asymptoticConstant :
    (1 : EReal) ≤ asymptoticDobrowolskiConstant

/-- Source: Cantor--Straus (1982), as reported by Voutier, coefficient `2`. -/
theorem_wanted cantorStraus_two_le_asymptoticConstant :
    (2 : EReal) ≤ asymptoticDobrowolskiConstant

/-- Source: Louboutin (1983), as reported by Voutier, coefficient `9/4`. -/
theorem_wanted louboutin_nine_fourths_le_asymptoticConstant :
    ((9 : ℝ) / 4 : EReal) ≤ asymptoticDobrowolskiConstant

/-- Source: Blanksby--Montgomery, the strict degree-dependent bound quoted by Voutier. -/
theorem_wanted blanksbyMontgomery_degreeBound (α : ℂ)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    (hd : 2 ≤ (minpoly ℚ α).natDegree) :
    1 + 1 / (52 * (minpoly ℚ α).natDegree * Real.log (6 * (minpoly ℚ α).natDegree)) <
      algebraicMahlerMeasure α

/-- Source: Stewart (1978), the strict degree-dependent bound quoted by Voutier. -/
theorem_wanted stewart_degreeBound (α : ℂ)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    (hd : 2 ≤ (minpoly ℚ α).natDegree) :
    1 + 1 / (10000 * (minpoly ℚ α).natDegree * Real.log (minpoly ℚ α).natDegree) <
      algebraicMahlerMeasure α

end MathlibExt.NumberTheory.AsymptoticDobrowolski
