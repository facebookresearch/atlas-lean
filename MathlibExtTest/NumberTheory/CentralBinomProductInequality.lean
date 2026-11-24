/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductInequality

/-!
# Tests for Allen's inequality for central binomial products
-/

open MetaMathlibExt

-- The endpoint `a = 0` gives a strict bound for every positive shift.
example (x b : ℕ) (hx : 0 < x) (hb : 0 < b) :
    b.centralBinom < (x + 2 * b).choose b := by
  obtain ⟨hle, heq⟩ := centralBinom_add_le_centralBinom_mul_choose_of_le x 0 b hx hb (by omega)
  simpa using hle.lt_of_ne (fun h => Nat.zero_ne_one (heq.mp h).2)

example (b : ℕ) (hb : 0 < b) : (1 + b).centralBinom = 2 * (1 + 2 * b).choose b :=
  (centralBinom_add_le_centralBinom_mul_choose_of_le 1 1 b (by decide) hb le_rfl).2.mpr ⟨rfl, rfl⟩

-- The next diagonal value already gives strict inequality.
example (b : ℕ) (hb : 0 < b) : (2 + b).centralBinom < 6 * (2 + 2 * b).choose b := by
  obtain ⟨hle, heq⟩ := centralBinom_add_le_centralBinom_mul_choose_of_le 2 2 b (by decide) hb le_rfl
  exact hle.lt_of_ne (fun h => (by decide : (2 : ℕ) ≠ 1) (heq.mp h).1)
