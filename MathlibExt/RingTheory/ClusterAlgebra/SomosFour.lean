/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The Somos-4 sequence

The Somos-4 sequence `1, 1, 1, 1, 2, 3, 7, 23, 59, 314, …` is defined by
`z₀ = z₁ = z₂ = z₃ = 1` and `z_{m+2} z_{m-2} = z_{m+1} z_{m-1} + z_m²` (Fomin, Williams and
Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5,
Example 3.4.3). It is defined here over `ℚ`; its terms are positive, so the defining division
is never by zero.
-/

@[expose] public section

namespace MathlibExt.RingTheory.ClusterAlgebra

/-- **Somos-4 sequence.** `somos4 0 = somos4 1 = somos4 2 = somos4 3 = 1` and
`somos4 (m + 4) = (somos4 (m + 3) * somos4 (m + 1) + somos4 (m + 2) ^ 2) / somos4 m`, the
recurrence `z_{m+2} z_{m-2} = z_{m+1} z_{m-1} + z_m²` of Fomin, Williams and Zelevinsky,
*Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Example 3.4.3, solved for
the newest term in `ℚ`. -/
def somos4 : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | m + 4 => (somos4 (m + 3) * somos4 (m + 1) + somos4 (m + 2) ^ 2) / somos4 m

/-- **Positivity of the Somos-4 sequence.** Every term of `somos4` is positive, so its defining
division is never by zero. -/
theorem somos4_pos (m : ℕ) : 0 < somos4 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ | 1, _ | 2, _ | 3, _ => simp [somos4]
    | m + 4, ih =>
      have h3 := ih (m + 3) (by omega)
      have h2 := ih (m + 2) (by omega)
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      simp only [somos4]
      positivity

/-- **Somos-4 recurrence.** `somos4 (m + 4) * somos4 m = somos4 (m + 3) * somos4 (m + 1) +
somos4 (m + 2) ^ 2` for every `m` (Fomin, Williams and Zelevinsky, *Introduction to cluster
algebras, Chapters 1–3*, arXiv:1608.05735v5, Example 3.4.3). -/
theorem somos4_add_four_mul (m : ℕ) :
    somos4 (m + 4) * somos4 m = somos4 (m + 3) * somos4 (m + 1) + somos4 (m + 2) ^ 2 := by
  have h := (somos4_pos m).ne'
  rw [somos4]
  field_simp

/-- **First terms of the Somos-4 sequence.** `somos4 4, …, somos4 9` are `2, 3, 7, 23, 59, 314`
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, Example 3.4.3). -/
theorem somos4_four_to_nine :
    somos4 4 = 2 ∧ somos4 5 = 3 ∧ somos4 6 = 7 ∧ somos4 7 = 23 ∧ somos4 8 = 59 ∧
      somos4 9 = 314 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [somos4]

end MathlibExt.RingTheory.ClusterAlgebra
