/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
# A small-base constraint for repetend tables

The bounds on the second residue rule out a particular value of the quotient.

## References

* R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*,
  INTEGERS 25 (2025), Article A26, pp. 1–53, Lemma 31 (p. 37).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **A constraint on the quotient of the square of a small base.** Let $n$ be a positive integer
and let $b$ be a small base: a positive integer coprime to $n$ and less than $n$.
If $b^2 = b_2 + un$ with $2 \le b_2 \le n - 2$, then $b \ne u + 1$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 31 (`integers-2025-A26-lem-31`). -/
public theorem ne_add_one_of_sq_add_mul_mem (n b : ℕ) (hbpos : 0 < b)
    (_hcoprime : Nat.Coprime b n) (hsmall : b < n) (u b₂ : ℤ)
    (hb : (b : ℤ) ^ 2 = b₂ + u * n) (h2 : 2 ≤ b₂) (_hn : b₂ ≤ n - 2) :
    (b : ℤ) ≠ u + 1 := by
  intro h
  have hfactor : b₂ - 1 = ((b : ℤ) - 1) * ((b : ℤ) + 1 - n) := by
    calc
      b₂ - 1 = (b : ℤ) ^ 2 - u * n - 1 := by omega
      _ = ((b : ℤ) - 1) * ((b : ℤ) + 1 - n) := by
        rw [show u = (b : ℤ) - 1 by omega]
        ring
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (a := (b : ℤ) - 1)
    (b := (b : ℤ) + 1 - n) (by omega) (by omega)
  omega

end

end MetaMathlibExt
