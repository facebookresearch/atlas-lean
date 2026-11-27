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

/-- **Dobrowolski's lower bound for the asymptotic Dobrowolski constant.** The asymptotic
Dobrowolski constant is at least $1$, as an extended real number.

Source: Dobrowolski (1979), as reported by Voutier, coefficient `1`. -/
theorem_wanted dobrowolski_one_le_asymptoticConstant :
    (1 : EReal) ≤ asymptoticDobrowolskiConstant

/-- **Cantor–Straus lower bound for the asymptotic Dobrowolski constant.** The asymptotic
Dobrowolski constant is at least $2$, as an extended real number.

Source: Cantor--Straus (1982), as reported by Voutier, coefficient `2`. -/
theorem_wanted cantorStraus_two_le_asymptoticConstant :
    (2 : EReal) ≤ asymptoticDobrowolskiConstant

/-- **Louboutin's lower bound for the asymptotic Dobrowolski constant.** The asymptotic
Dobrowolski constant is at least $9/4$, as an extended real number.

Source: Louboutin (1983), as reported by Voutier, coefficient `9/4`. -/
theorem_wanted louboutin_nine_fourths_le_asymptoticConstant :
    ((9 : ℝ) / 4 : EReal) ≤ asymptoticDobrowolskiConstant

/-- **Blanksby–Montgomery lower bound for the Mahler measure.** Let $\alpha$ be a nonzero complex
number that is algebraic over $\mathbb{Q}$ and is not a root of unity, and let $d$ be the degree
of its minimal polynomial over $\mathbb{Q}$. If $d \ge 2$, then the algebraic Mahler measure
$M(\alpha)$ satisfies $M(\alpha) > 1 + \frac{1}{52\, d \log(6d)}$, with $\log$ the natural
logarithm.

Source: Blanksby--Montgomery, the strict degree-dependent bound quoted by Voutier. -/
theorem_wanted blanksbyMontgomery_degreeBound (α : ℂ)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    (hd : 2 ≤ (minpoly ℚ α).natDegree) :
    1 + 1 / (52 * (minpoly ℚ α).natDegree * Real.log (6 * (minpoly ℚ α).natDegree)) <
      algebraicMahlerMeasure α

/-- **Stewart's lower bound for the Mahler measure.** Let $\alpha$ be a nonzero complex number
that is algebraic over $\mathbb{Q}$ and is not a root of unity, and let $d$ be the degree of its
minimal polynomial over $\mathbb{Q}$. If $d \ge 2$, then the algebraic Mahler measure $M(\alpha)$
satisfies $M(\alpha) > 1 + \frac{1}{10000\, d \log d}$, with $\log$ the natural logarithm.

Source: Stewart (1978), the strict degree-dependent bound quoted by Voutier. -/
theorem_wanted stewart_degreeBound (α : ℂ)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) (hroot : ¬IsOfFinOrder α)
    (hd : 2 ≤ (minpoly ℚ α).natDegree) :
    1 + 1 / (10000 * (minpoly ℚ α).natDegree * Real.log (minpoly ℚ α).natDegree) <
      algebraicMahlerMeasure α

end MathlibExt.NumberTheory.AsymptoticDobrowolski
