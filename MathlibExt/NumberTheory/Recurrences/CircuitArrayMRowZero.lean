/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.CircuitArrayM
import all MathlibExt.NumberTheory.Recurrences.CircuitArray
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Row zero of the multivariable circuit array

Row zero follows the first left boundary value through successive reductions. Each reduction
beyond the first divides the difference from `1` by `9`.

## References

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows
  of the Circuit Array*, Fibonacci Quarterly 62 (4) (2024), pp. 290–304, Corollary 4.8 and
  Remark 4.9; see also Section 2 and the row-zero calculation in Proposition 4.1(v).
- Emily Evans and Russell Jay Hendel, *An Infinite 2-Dimensional Array Associated with Electric
  Circuits*, Fibonacci Quarterly 60 (5) (2022), pp. 151–171, Section 8 (the original circuit
  array).
- Emily J. Evans and Russell Jay Hendel, *Resistance values under transformations in regular
  triangular grids*, Discrete Applied Mathematics 355 (2024), pp. 129–141, Theorem 6.5
  (Uniform Center Theorem, cited for the row-zero reduction).
-/

namespace MetaMathlibExt

/-- **Row 0 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 1$, $C^M_{0,s} = (9^{s-1} - 1 + X_1)/9^{s-1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.8 (`fq-2024-hendel08232024rev2-cor-4.8`). -/
public theorem circuitArrayM_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayM 0 s = (9 ^ (s - 1) - 1 + circuitVar 1) / 9 ^ (s - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  let bdry (m : ℕ) := if m = 0 then none else some (circuitVar m)
  have hstart : (bdry 1).getD (2 / 3) = 1 - (1 - circuitVar 1) := by simp [bdry]
  change circuitArrayOf bdry 0 (k + 1) = _
  rw [circuitArrayOf_zero_succ,
    circuitGrid_front bdry (1 - circuitVar 1) hstart circuitArrayM_row_one.front_nonsingular
      k (2 * k + 1) le_rfl, Nat.add_sub_cancel]
  have hq : (9 : FractionRing (MvPolynomial ℕ ℚ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hq]
  ring

end MetaMathlibExt
