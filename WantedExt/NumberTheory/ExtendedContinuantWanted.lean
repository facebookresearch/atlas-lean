/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ExtendedContinuant

/-!
# Extended continuants and bi-infinite periodic continued fractions

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73.

Proved in `MathlibExt.NumberTheory.ExtendedContinuant`, which also defines the
extended continuant `MetaMathlibExt.extendedContinuant` and proves Lemma 1
(`MetaMathlibExt.extendedContinuant_neg_three_to_six`): Proposition 1
(`MetaMathlibExt.extendedContinuant_westbound_matrix_prod`), Theorems 1–3
(`MetaMathlibExt.extendedContinuant_neg_order`,
`MetaMathlibExt.extendedContinuant_bennett_nat`,
`MetaMathlibExt.extendedContinuant_bennett`), Corollaries 1 and 2
(`MetaMathlibExt.extendedContinuant_euler`,
`MetaMathlibExt.extendedContinuant_det`), Theorems 4–7
(`MetaMathlibExt.not_silent_of_even`, `MetaMathlibExt.oneSilent_terms`,
`MetaMathlibExt.threeSilent_terms`, `MetaMathlibExt.oddSilent_terms`) and both
cases of Proposition 3 (`MetaMathlibExt.silentTerms_table_one_mod_six`,
`MetaMathlibExt.silentTerms_table_five_mod_six`).

Recorded here: Lemma 3, that the simple continued fraction of the smaller
conjugate of a real quadratic irrational is not purely periodic.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Lemma 3: for conjugate real quadratic irrationals `α = (P + √D)/Q > ᾱ = (P - √D)/Q`
(`D > 0` not a square, `Q > 0`), the simple continued fraction of `ᾱ` is not purely periodic,
i.e. it has at least one nonperiodic term (`ṙ ≥ 1`). The terms are the integer parts `b` of
Mathlib's continued-fraction stream `GenContFract.IntFractPair.stream`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Lemma 3. -/
public theorem_wanted conjugate_continuedFraction_not_purelyPeriodic (P Q D : ℤ) (hD : 0 < D)
    (hsq : ¬ IsSquare D) (hQ : 0 < Q) :
    ¬ ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
      (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) (n + s)).map (·.b) =
        (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) n).map (·.b)

end

end MetaMathlibExt
