/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Infix
import MathlibExt.Combinatorics.Enumerative.FibternarySums

/-! # Tests for sums of Fibternary and Tribternary numbers -/

namespace MetaMathlibExt.exists_fibternary_sum_four_and_tribternary_sum_three

private abbrev Avoids (run : List ℕ) (x : ℕ) : Prop :=
  (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ run <:+: Nat.digits 3 x

-- The empty ternary expansion admits both decompositions.
example : (∃ a b c d : ℕ, (∀ x ∈ [a, b, c, d], Avoids [1, 1] x) ∧ 0 = a + b + c + d) ∧
    ∃ a b c : ℕ, (∀ x ∈ [a, b, c], Avoids [1, 1, 1] x) ∧ 0 = a + b + c :=
  exists_fibternary_sum_four_and_tribternary_sum_three 0

-- In 222₃ every column needs two ones. The Fibternary witnesses repeat 101₃ and 10₃.
example :
    let parts := [10, 10, 3, 3]
    (∀ x ∈ parts, Avoids [1, 1] x) ∧ parts.sum = 26 := by decide

-- The Tribternary witnesses 110₃, 101₃ and 11₃ put their zeros in different columns.
example :
    let parts := [12, 10, 4]
    (∀ x ∈ parts, Avoids [1, 1, 1] x) ∧ parts.sum = 26 := by decide

end MetaMathlibExt.exists_fibternary_sum_four_and_tribternary_sum_three
