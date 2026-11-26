/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ExtendedContinuantOddSilentTerms

/-!
# Tests for terms of a σ-silent sequence for odd σ ≥ 5

At `σ = 5` the first boundary formula computes `x_{-3} x_{-4} = z_0 x_{-1}`, the westbound tail
gives `x_{-6} = -z_2`, and the eastbound terms agree.
-/

namespace MathlibExtTest.NumberTheory.ExtendedContinuantOddSilentTerms

open MetaMathlibExt

-- At σ = 5 the first boundary formula computes x_{-3} x_{-4} = z₀ x_{-1}.
example (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 5 - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 5 - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    x (-3) * x (-4) = z 0 * x (-1) := by
  have h := (oddSilent_terms x y z 5 ⟨2, rfl⟩ le_rfl heast hwest).2.1
  norm_num [extendedContinuant_neg_one, extendedContinuant_zero] at h
  linear_combination h

-- At σ = 5 the westbound tail gives x_{-6} = -z₂.
example (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 5 - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 5 - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    x (-6) = -z 2 := by
  have h := (oddSilent_terms x y z 5 ⟨2, rfl⟩ le_rfl heast hwest).2.2.2.2 6 (by decide)
  rw [show (6 : ℤ) - 5 + 1 = 2 by decide] at h
  exact h

-- East of the origin the two sequences agree termwise.
example (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 5 - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 5 - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    x 7 = y 7 := by
  have h := (oddSilent_terms x y z 5 ⟨2, rfl⟩ le_rfl heast hwest).1 7
  simpa using h

end MathlibExtTest.NumberTheory.ExtendedContinuantOddSilentTerms
