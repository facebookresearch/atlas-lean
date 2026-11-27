/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# A small-base constraint for repetend tables

The bounds on the second residue rule out a particular value of its integer coefficient.

## References

* R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*,
  INTEGERS 25 (2025), Article A26, pp. 1–53, Lemma 31 (p. 37).
  We use the plus sign in the statement of the lemma; its printed proof uses a minus sign.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **A constraint on $b^2 + un$ between $2$ and $n - 2$.** Let $n$ and $b$ be natural numbers and
$u$ an integer, and put $b_2 = b^2 + un$. If $2 \le b_2 \le n - 2$, then $b \ne u + 1$.

The paper states this for a small base $b$; here $b$ is any natural number.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 31 (`integers-2025-A26-lem-31`). -/
public theorem ne_add_one_of_sq_add_mul_mem (n b : ℕ) (u : ℤ)
    (h2 : 2 ≤ (b : ℤ) ^ 2 + u * n) (hn : (b : ℤ) ^ 2 + u * n ≤ n - 2) :
    (b : ℤ) ≠ u + 1 := by
  intro h
  have hb : 0 ≤ (b : ℤ) := Nat.cast_nonneg b
  have hn₀ : 0 ≤ (n : ℤ) := Nat.cast_nonneg n
  rcases (by omega : (b : ℤ) = 0 ∨ (b : ℤ) = 1 ∨ 2 ≤ (b : ℤ)) with hb₀ | hb₁ | hb₂
  · have hu : u = -1 := by omega
    simp [hb₀, hu] at h2
    omega
  · have hu : u = 0 := by omega
    simp [hb₁, hu] at h2
  · have hu : (1 : ℤ) ≤ u := by omega
    have hmul : (n : ℤ) ≤ u * n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu hn₀
    have hsq := sq_nonneg (b : ℤ)
    omega

end

end MetaMathlibExt
