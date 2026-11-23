/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Padics.HilbertReciprocity

open IsDedekindDomain NumberField

namespace HilbertReciprocityTest

/-- Consumer with the original binders and hypotheses. -/
theorem exactSource
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      (∀ v, v ∈ S ↔
        ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
            - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) ∧
      Even (S.card + if (a < 0 ∧ b < 0) then 1 else 0) :=
  Rat.hilbertReciprocity_even_card_not_ternary_isotropic a b ha hb

/-- The sign term matters: for `a = b = -1` the parity includes the
extra `1`. -/
example : ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
    Even (S.card + 1) :=
  let ⟨S, _, hEven⟩ := exactSource (-1) (-1) (by norm_num) (by norm_num)
  ⟨S, by simpa using hEven⟩

end HilbertReciprocityTest
