/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GeneralizedMarkovVietaEq

open MetaMathlibExt

-- The triple (1, 1, 1) satisfies both Vieta jumping identities for every k.
example (k : ℕ) :
    ((1 : ℤ) ^ 2 + k * 1 * 1 + (1 : ℤ) ^ 2 =
      (1 : ℤ) * ((3 + 3 * k) * 1 * 1 - 1 - k * (1 + 1))) ∧
    ((1 : ℤ) ^ 2 + k * 1 * 1 + (1 : ℤ) ^ 2 =
      (1 : ℤ) * ((3 + 3 * k) * 1 * 1 - 1 - k * (1 + 1))) :=
  IsGenMarkovTriple.vieta_eq (isGenMarkovTriple_one_one_one k)

-- The classical Markov triple (1, 5, 2) satisfies both identities, with
-- distinct values 26 and 29 on the two sides of the conjunction.
example :
    ((1 : ℤ) ^ 2 + (0 : ℕ) * 1 * 5 + (5 : ℤ) ^ 2 =
      (2 : ℤ) * ((3 + 3 * (0 : ℕ)) * 1 * 5 - 2 - (0 : ℕ) * (1 + 5))) ∧
    ((5 : ℤ) ^ 2 + (0 : ℕ) * 5 * 2 + (2 : ℤ) ^ 2 =
      (1 : ℤ) * ((3 + 3 * (0 : ℕ)) * 5 * 2 - 1 - (0 : ℕ) * (5 + 2))) := by
  have htriple : IsGenMarkovTriple 0 1 5 2 :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact IsGenMarkovTriple.vieta_eq htriple
