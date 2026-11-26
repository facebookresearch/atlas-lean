/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Scaled binomial coefficients as digits

If all the scaled coefficients fit in base `b`, the binomial theorem gives
these coefficients as the digits of `α * (1 + b) ^ k`. This includes the
single-digit expansion for `k = 0`.
-/

namespace MetaMathlibExt

/-- **Digits of a multiple of a power of one more than the base.** Let $\alpha \ge 1$, $k$ and $b$
be natural numbers with $\alpha\binom{k}{\lceil k/2 \rceil} < b$. Then the base-$b$
representation of $\alpha(1 + b)^k$ has exactly the $k + 1$ digits
$\alpha\binom{k}{k}, \alpha\binom{k}{k-1}, \dots, \alpha\binom{k}{0}$, from the most significant
to the least significant.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 1
(`integers-2024-A69-lem-1`). -/
public theorem digits_mul_one_add_pow (α k b : ℕ) (hα : 1 ≤ α)
    (h : α * k.choose ((k + 1) / 2) < b) :
    Nat.digits b (α * (1 + b) ^ k) = (List.range (k + 1)).map fun i => α * k.choose i := by
  have hmiddle : k.choose (k / 2) = k.choose ((k + 1) / 2) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hlt (i : ℕ) : α * k.choose i < b :=
    (Nat.mul_le_mul_left α ((Nat.choose_le_middle i k).trans_eq hmiddle)).trans_lt h
  have hb : 1 < b := hα.trans_lt (by simpa using hlt 0)
  have hvalue : Nat.ofDigits b ((List.range (k + 1)).map fun i => α * k.choose i) =
      α * (1 + b) ^ k := calc
    _ = ∑ i ∈ Finset.range (k + 1), α * k.choose i * b ^ i := by
      rw [Nat.ofDigits_eq_sum_mapIdx, Finset.sum_range, ← Fin.sum_ofFn]
      congr 1
      apply List.ext_getElem
      · simp only [List.length_mapIdx, List.length_map, List.length_range, List.length_ofFn]
      · intro i hi hj
        simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    _ = α * (1 + b) ^ k := by
      simp [add_comm 1 b, add_pow, Finset.mul_sum, mul_left_comm, mul_comm]
  rw [← hvalue]
  refine Nat.digits_ofDigits b hb _ ?_ ?_
  · intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    exact hlt i
  · intro hne
    simpa using Nat.ne_of_gt hα

end MetaMathlibExt
