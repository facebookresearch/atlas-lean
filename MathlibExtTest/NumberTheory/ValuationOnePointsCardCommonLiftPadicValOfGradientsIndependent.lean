/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ValuationOnePointsCardCommonLiftPadicValOfGradientsIndependent
import Mathlib.Tactic.NormNum

/-!
# Tests for common lifts of two points with independent gradients

For `f = xy` modulo two, the points `(0, 1)` and `(1, 0)` have independent gradients, and each
of the three common-lift counts is one.
-/

namespace MathlibExtTest.NumberTheory.ValuationOnePointsCardCommonLiftPadicValOfGradientsIndependent

open MvPolynomial

-- All three common-lift counts of `(0, 1)` and `(1, 0)` for `xy` modulo two are one.
example : ((Finset.range 2 ×ˢ Finset.range 2).filter fun kl : ℕ × ℕ =>
    (((2 : ℕ) : ℤ) ∣ MvPolynomial.eval ![(((0 : ℕ) : ℤ)) + kl.1 * 2, (((1 : ℕ) : ℤ)) + kl.2 * 2]
        (X 0 * X 1) ∧
      ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ MvPolynomial.eval
        ![(((0 : ℕ) : ℤ)) + kl.1 * 2, (((1 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1)) ∧
    (((2 : ℕ) : ℤ) ∣ MvPolynomial.eval ![(((1 : ℕ) : ℤ)) + kl.1 * 2, (((0 : ℕ) : ℤ)) + kl.2 * 2]
        (X 0 * X 1) ∧
      ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ MvPolynomial.eval
        ![(((1 : ℕ) : ℤ)) + kl.1 * 2, (((0 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1))).card = 1 ∧
    ((Finset.range 2 ×ˢ Finset.range 2).filter fun kl : ℕ × ℕ =>
      ((2 : ℕ) : ℤ) ^ 2 ∣ MvPolynomial.eval
        ![(((0 : ℕ) : ℤ)) + kl.1 * 2, (((1 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1) ∧
      (((2 : ℕ) : ℤ) ∣ MvPolynomial.eval
          ![(((1 : ℕ) : ℤ)) + kl.1 * 2, (((0 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1) ∧
        ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ MvPolynomial.eval
          ![(((1 : ℕ) : ℤ)) + kl.1 * 2, (((0 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1))).card = 1 ∧
    ((Finset.range 2 ×ˢ Finset.range 2).filter fun kl : ℕ × ℕ =>
      ((2 : ℕ) : ℤ) ^ 2 ∣ MvPolynomial.eval
        ![(((0 : ℕ) : ℤ)) + kl.1 * 2, (((1 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1) ∧
      ((2 : ℕ) : ℤ) ^ 2 ∣ MvPolynomial.eval
        ![(((1 : ℕ) : ℤ)) + kl.1 * 2, (((0 : ℕ) : ℤ)) + kl.2 * 2] (X 0 * X 1)).card = 1 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 * X 1
  have h := MetaMathlibExt.card_common_lift_padicVal_of_gradients_independent (p := 2)
    Nat.prime_two f (r₁ := 0) (s₁ := 1) (r₂ := 1) (s₂ := 0) (by decide) (by decide) (by decide)
    (by decide) (by norm_num [f]) (by norm_num [f]) (by norm_num [f])
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide), h.2.2⟩

end MathlibExtTest.NumberTheory.ValuationOnePointsCardCommonLiftPadicValOfGradientsIndependent
