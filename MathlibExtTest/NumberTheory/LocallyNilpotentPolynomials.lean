/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LocallyNilpotentPolynomials
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

-- The degree restriction excludes the zero polynomial even though its first iterate is zero.
example : IsWeaklyLocallyNilpotentAt 0 (-1) ∅ ∧ ¬ (0 < (0 : ℤ[X]).natDegree) := by
  exact ⟨fun p _ _ => ⟨1, by decide, by simp⟩, by simp⟩

-- The translation belongs to the classification and stays strictly negative at every iterate.
example : IsWeaklyLocallyNilpotentAt (X - 1) (-1) ∅ ∧ ¬ IsNilpotentAt (X - 1) (-1) := by
  constructor
  · have h : (X - 1 : ℤ[X]) ∈
        {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅} := by
      rw [locallyNilpotentAt_neg_one_classification]
      exact Or.inr rfl
    exact h.2
  · have hneg (n : ℕ) : (fun x => (X - 1 : ℤ[X]).eval x)^[n] (-1) < 0 := by
      induction n with
      | zero => decide
      | succ n ih =>
        rw [Function.iterate_succ_apply', eval_sub, eval_X, eval_one]
        omega
    rintro ⟨n, _, hn⟩
    exact (hneg n).ne hn

-- A nonconstant multiple of the three linear factors preserves the exact first hitting time.
example :
    let u : ℤ[X] := 2 * X ^ 2 + 7 * X + 3 + X * (X + 1) * (X + 2) * (X + 3)
    (fun x => u.eval x)^[1] (-1) = -2 ∧
      (fun x => u.eval x)^[2] (-1) = -3 ∧ (fun x => u.eval x)^[3] (-1) = 0 := by
  dsimp only
  norm_num [Function.iterate_succ_apply']
