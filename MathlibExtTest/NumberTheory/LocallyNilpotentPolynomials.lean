/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LocallyNilpotentPolynomials
import Mathlib.Algebra.Polynomial.Degree.Operations
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

-- Away from `x + 1`, a polynomial of positive degree that is locally nilpotent at `1` is
-- nilpotent there.
example (u : ℤ[X]) (hdeg : 0 < u.natDegree) (hu : IsWeaklyLocallyNilpotentAt u 1 ∅)
    (hne : u ≠ X + 1) : IsNilpotentAt u 1 := by
  by_contra hnil
  have h : u ∈ {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅ ∧
      ¬ IsNilpotentAt u 1} := ⟨hdeg, hu, hnil⟩
  rw [locallyNilpotent_not_nilpotentAt_one_neg_one.1] at h
  exact hne h

-- The translation `x ↦ x - 2` keeps the orbit of `-1` negative, so it is not nilpotent at `-1`,
-- and the corollary shows that it is not locally nilpotent there either (the orbit stays odd).
example : ¬ IsWeaklyLocallyNilpotentAt (X - 2) (-1) ∅ := by
  intro hu
  have hneg (n : ℕ) : (fun x => (X - 2 : ℤ[X]).eval x)^[n] (-1) < 0 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Function.iterate_succ_apply', eval_sub, eval_X, eval_ofNat]
      omega
  have h : (X - 2 : ℤ[X]) ∈ {u : ℤ[X] | 0 < u.natDegree ∧
      IsWeaklyLocallyNilpotentAt u (-1) ∅ ∧ ¬ IsNilpotentAt u (-1)} := by
    refine ⟨?_, hu, fun ⟨n, _, hn⟩ => (hneg n).ne hn⟩
    rw [show (X - 2 : ℤ[X]) = X - C 2 by simp, natDegree_X_sub_C]
    decide
  rw [locallyNilpotent_not_nilpotentAt_one_neg_one.2, Set.mem_singleton_iff] at h
  have h0 := congrArg (eval 0) h
  norm_num at h0

-- A nonconstant multiple of the three linear factors preserves the exact first hitting time.
example :
    let u : ℤ[X] := 2 * X ^ 2 + 7 * X + 3 + X * (X + 1) * (X + 2) * (X + 3)
    (fun x => u.eval x)^[1] (-1) = -2 ∧
      (fun x => u.eval x)^[2] (-1) = -3 ∧ (fun x => u.eval x)^[3] (-1) = 0 := by
  dsimp only
  norm_num [Function.iterate_succ_apply']

-- A polynomial with a nonconstant factor in the third family first reaches zero at step three.
example :
    let u : ℤ[X] := -2 * X ^ 2 + 7 * X - 3 + (X + 1) * (X - 1) * (X - 2) * (X - 3)
    (0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅) ∧
      (fun x => u.eval x)^[1] 1 = 2 ∧ (fun x => u.eval x)^[2] 1 = 3 ∧
      (fun x => u.eval x)^[3] 1 = 0 := by
  intro u
  constructor
  · show u ∈ {v : ℤ[X] | 0 < v.natDegree ∧ IsWeaklyLocallyNilpotentAt v 1 ∅}
    rw [locallyNilpotentAt_one_classification]
    exact Or.inl (Or.inr ⟨X + 1, rfl⟩)
  · norm_num [u, Function.iterate_succ_apply']

-- The translation in the last family is locally nilpotent even though it never reaches zero.
example : IsWeaklyLocallyNilpotentAt (X + 1) 1 ∅ ∧ ¬ IsNilpotentAt (X + 1) 1 := by
  have h : (X + 1 : ℤ[X]) ∈
      {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅} := by
    rw [locallyNilpotentAt_one_classification]
    exact Or.inr rfl
  exact ⟨h.2, not_isNilpotentAt_X_add_one⟩
