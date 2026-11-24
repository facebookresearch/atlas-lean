/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Two representations by coprime generators

`MetaMathlibExt.twoGenerator_dvd_sub_of_eq` gives the divisibility relations between the
coefficients of two representations of the same natural number.
-/

namespace MetaMathlibExt

/-- **Two representations by coprime generators.** Let $c$ and $d$ be coprime natural numbers.
If natural numbers $x, y, x', y'$ satisfy $cx + dy = cx' + dy'$, then $c$ divides $y - y'$ and
$d$ divides $x - x'$ in the integers.

The paper's standing assumption $1 < c < d$ is not needed and is dropped.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 1 (`integers-2025-A51-lem-1`). -/
public theorem twoGenerator_dvd_sub_of_eq {c d : ℕ} (hcd : c.Coprime d)
    {x y x' y' : ℕ} (h : c * x + d * y = c * x' + d * y') :
    (c : ℤ) ∣ (y : ℤ) - y' ∧ (d : ℤ) ∣ (x : ℤ) - x' := by
  have hdiff : (c : ℤ) * ((x : ℤ) - x') = d * ((y' : ℤ) - y) := by
    rw [mul_sub, mul_sub, sub_eq_sub_iff_add_eq_add]
    exact_mod_cast h.trans (add_comm ..)
  exact ⟨dvd_sub_comm.mp (hcd.isCoprime.dvd_of_dvd_mul_left ⟨_, hdiff.symm⟩),
    hcd.symm.isCoprime.dvd_of_dvd_mul_left ⟨_, hdiff⟩⟩

end MetaMathlibExt
