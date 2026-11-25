/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Digits.BergmanLucasEvenAdd

/-!
# Tests for the Bergman expansion of $L_{2n} + k$
-/

open scoped goldenRatio

namespace MetaMathlibExt

-- The Bergman expansion of $1$ is $\{0\}$, and that of $L_2 + 1 = 4$ is $\{2, 0, -2\}$.
example : (2 : ℤ) ∉ ({0} : Finset ℤ) ∧ -(2 : ℤ) ∉ ({0} : Finset ℤ) ∧
    ({2, 0, -2} : Finset ℤ) =
      insert (2 : ℤ) (insert (-(2 : ℤ)) ({0} : Finset ℤ)) := by
  have h1 : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  have h2 : φ ^ (-2 : ℤ) = 2 - φ := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat, ← inv_pow, h1]
    linear_combination Real.goldenRatio_sq
  have hvalT : basePhiValue ({2, 0, -2} : Finset ℤ) = 4 := by
    rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, zpow_ofNat, zpow_zero, h2]
    linear_combination Real.goldenRatio_sq
  exact bergman_lucas_even_add 1 1 le_rfl (by decide) (by unfold IsBergmanExpansion; decide)
    (by simpa using basePhiValue_singleton_zero) (by unfold IsBergmanExpansion; decide)
    (by show basePhiValue ({2, 0, -2} : Finset ℤ) = (4 : ℝ); exact hvalT)

-- The Bergman expansion of $0$ is empty, and that of $L_2 = 3$ is $\{2, -2\}$.
example : (2 : ℤ) ∉ (∅ : Finset ℤ) ∧ -(2 : ℤ) ∉ (∅ : Finset ℤ) ∧
    ({2, -2} : Finset ℤ) =
      insert (2 : ℤ) (insert (-(2 : ℤ)) (∅ : Finset ℤ)) := by
  have h1 : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  have h2 : φ ^ (-2 : ℤ) = 2 - φ := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat, ← inv_pow, h1]
    linear_combination Real.goldenRatio_sq
  have hvalT : basePhiValue ({2, -2} : Finset ℤ) = 3 := by
    rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_singleton, zpow_ofNat, h2]
    linear_combination Real.goldenRatio_sq
  exact bergman_lucas_even_add 1 0 le_rfl (by decide) (by unfold IsBergmanExpansion; decide) (by simpa using basePhiValue_empty)
    (by unfold IsBergmanExpansion; decide) (by show basePhiValue ({2, -2} : Finset ℤ) = (3 : ℝ); exact hvalT)

end MetaMathlibExt
