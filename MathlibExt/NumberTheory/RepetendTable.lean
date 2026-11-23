/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Long division of a proper fraction

The long division of a proper fraction `m / n` in a base `b ≥ 1`, with remainders
`c_j = m b^j mod n` and digits `r_j = ⌊b c_j / n⌋`, satisfies
`m / n = ∑_{i<k} r_i / b^(i+1) + c_k / (n b^k)` for every `k`, and `r_j n = b c_j - c_{j+1}`
(`MetaMathlibExt.long_division_remainder_expansion`; its docstring gives the source).

## Proof outline

Since `m b^(j+1) = b (m b^j)`, the next remainder is `c_{j+1} = b c_j mod n`, so the division of
`b c_j` by `n` reads `n r_j + c_{j+1} = b c_j`. This gives the second identity. The first one
follows by induction on `k`: for `k = 0` it is `m / n = c_0 / n`, where `c_0 = m` because
`m < n`, and dividing the step identity by `n b^(k+1)` gives
`c_k / (n b^k) = r_k / b^(k+1) + c_{k+1} / (n b^(k+1))`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Long division of a proper fraction.** Let $m < n$ be natural numbers and $b \ge 1$. For
$j \ge 0$ let $c_j = m b^j \bmod n$ (the remainders of the long division of $m/n$ in base $b$) and
$r_j = \lfloor b c_j / n \rfloor$ (its digits). Then for every $k \ge 0$
$$\frac{m}{n} = \sum_{i<k} \frac{r_i}{b^{i+1}} + \frac{c_k}{n b^k},$$
and $r_j n = b c_j - c_{j+1}$ for every $j \ge 0$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 5 (`integers-2025-A26-lem-5`). -/
theorem long_division_remainder_expansion (m n b : ℕ) (hmn : m < n) (hb : 0 < b) :
    let c : ℕ → ℕ := fun j => m * b ^ j % n
    let r : ℕ → ℕ := fun j => b * c j / n
    (∀ k : ℕ, (m : ℚ) / n =
      ∑ i ∈ Finset.range k, (r i : ℚ) / (b : ℚ) ^ (i + 1) + (c k : ℚ) / ((n : ℚ) * (b : ℚ) ^ k)) ∧
    ∀ j : ℕ, r j * n = b * c j - c (j + 1) := by
  intro c r
  -- One step of the long division: `b c_j = n r_j + c_{j+1}`.
  have hstep (j : ℕ) : n * r j + c (j + 1) = b * c j := by
    have hc : c (j + 1) = b * c j % n := by
      simp only [c]
      rw [Nat.mul_mod_mod, pow_succ, mul_comm b, mul_assoc]
    rw [hc]
    exact Nat.div_add_mod (b * c j) n
  refine ⟨fun k => ?_, fun j => ?_⟩
  · have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    induction k with
    | zero =>
      have hc0 : c 0 = m := by simp [c, Nat.mod_eq_of_lt hmn]
      simp [hc0]
    | succ k ih =>
      have hq : (n : ℚ) * r k + c (k + 1) = b * c k := by exact_mod_cast hstep k
      rw [Finset.sum_range_succ, ih, add_assoc]
      congr 1
      field_simp
      linear_combination (-(b : ℚ) ^ k) * hq
  · have h := hstep j
    rw [mul_comm]
    omega

end MetaMathlibExt
