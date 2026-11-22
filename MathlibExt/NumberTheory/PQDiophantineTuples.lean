/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs

/-!
# A divisibility lemma for `S`-Diophantine triples

Lemma 1 of Volker Ziegler, *On the Existence of `{p, q}`-Diophantine
Quadruples and Quintuples*, INTEGERS 25 (2025), Article A92, quoting
Szalay and Ziegler (2013), Lemma 2.1.

If `ac + 1 ∣ bc + 1`, then `ac + 1` divides
`b (ac + 1) - a (bc + 1) = b - a`, which is positive and smaller than
`c ≤ ac`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- If `a < b < c` are positive integers, then `ac + 1` does not divide
`bc + 1`. The paper states this for `S`-Diophantine triples; the
`S`-unit hypothesis is not needed.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine
Quadruples and Quintuples*, INTEGERS 25 (2025), Article A92, Lemma 1,
quoting Szalay and Ziegler (2013), Lemma 2.1
(`integers-2025-A92-lem-1`).
Proves `Wanted` entry `not_mul_add_one_dvd_mul_add_one`. -/
theorem not_mul_add_one_dvd_mul_add_one {a b c : ℕ} (ha : 0 < a)
    (hab : a < b) (hbc : b < c) : ¬(a * c + 1 ∣ b * c + 1) := by
  intro h
  have h1 : a * c + 1 ∣ b * (a * c + 1) - a * (b * c + 1) :=
    Nat.dvd_sub (Nat.dvd_mul_left _ _) (Nat.dvd_trans h (Nat.dvd_mul_left _ _))
  have h2 : b * (a * c + 1) - a * (b * c + 1) = b - a := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one,
      Nat.mul_left_comm b a c, ← Nat.mul_assoc a b c]
    omega
  rw [h2] at h1
  have h3 := Nat.le_of_dvd (by omega) h1
  have h4 : c ≤ a * c := Nat.le_mul_of_pos_left c ha
  omega

end MetaMathlibExt
