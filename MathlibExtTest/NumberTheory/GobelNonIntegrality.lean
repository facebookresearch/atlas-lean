/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelNonIntegrality
import Mathlib.Tactic.NormNum.LegendreSymbol

open MetaMathlibExt

-- The walk from 3 first steps down to meet the diagonal at 2.
-- It then follows the diagonal to 5 and stays at 5 on the next step.
example : gobelResidueWalk 5 3 5 = 5 ∧ gobelResidueWalk 5 3 6 = 5 := by
  have h₂ : gobelResidueWalk 5 3 2 = 2 := by norm_num [gobelResidueWalk]
  have h₅ := gobelResidueWalk_eq_index_of_eq_index 5 3 2 (by decide) ⟨2, rfl⟩
    (by decide) (by decide) (by decide) h₂ 5 (by decide) (by decide)
  exact ⟨h₅, gobelResidueWalk_succ_of_eq_prime 5 3 5 (by decide) h₅⟩

-- Zero is absorbing even when the index is strictly between zero and the modulus.
example : gobelResidueWalk 5 0 2 = 0 :=
  gobelResidueWalk_succ_of_eq_zero 5 0 1 (by decide) rfl
