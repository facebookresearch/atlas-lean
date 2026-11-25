/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.LinearAlgebra.Matrix.SinkhornEntropyUniqueness

/-!
# Entropy uniqueness checks

Focused checks for
`MathlibExt.LinearAlgebra.Matrix.SinkhornEntropyUniqueness`:
the general gauge identity at the factor rescaling `c = 2`,
the forward uniqueness direction applied to a scaled table
itself under positivity hypotheses, and the scaled-table
form where the rescaled factors `(2, 1 / 2)` differ from
`(1, 1)` but give the same table.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Gauge invariance at `c = 2` for general factors. -/
example (K : Fin 2 → Fin 2 → ℝ) (a b : Fin 2 → ℝ) :
    (fun i j => (2 * a i) * K i j * (b j / 2))
      = fun i j => a i * K i j * b j :=
  SinkhornMargins.scaled_table_gauge K a b (by norm_num)

/-- Forward uniqueness applied to a scaled table itself: its
entropy equality is reflexivity, and the conclusion is the
table equality. -/
example (K : Fin 2 → Fin 2 → ℝ) (a b : Fin 2 → ℝ)
    (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) :
    (fun i j => a i * K i j * b j)
      = fun i j => a i * K i j * b j :=
  (SinkhornMargins.entropy_minimizer_unique K
    (fun i j => a i * K i j * b j) a b hK ha hb
    (fun i j => le_of_lt (mul_pos (mul_pos (ha i) (hK i j)) (hb j)))
    (fun _ => rfl) (fun _ => rfl)).mp rfl

/-- The rescaled factors `(2, 1 / 2)` and `(1, 1)` are
different factor pairs giving the same scaled table. -/
example : SinkhornMargins.scaledTable (m := 1) (n := 1)
        (fun _ => (2 : ℝ)) (fun _ _ => (1 : ℝ)) (fun _ => 1 / 2)
      = SinkhornMargins.scaledTable (m := 1) (n := 1)
        (fun _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    ∧ (fun _ : Fin 1 => (2 : ℝ)) ≠ (fun _ : Fin 1 => (1 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · funext i j
    simp [SinkhornMargins.scaledTable]
  · intro h
    have hc := congrFun h 0
    norm_num at hc
