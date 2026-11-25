/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.DeterminantalTangent

set_option autoImplicit false

/-! Tests for generic minors, determinantal ideals and their tangent spaces. -/

open MvPolynomial MathlibExt.AlgebraicGeometry.AffineTangent
  MathlibExt.AlgebraicGeometry.DeterminantalTangent

variable {k : Type*} [Field k] {m n : ℕ}

-- A `1 × 1` minor is the corresponding entry.
example (rows : Fin 1 ↪ Fin m) (cols : Fin 1 ↪ Fin n) :
    (minorPolynomial 0 rows cols : MvPolynomial (Fin m × Fin n) k) = X (rows 0, cols 0) := by
  simp [minorPolynomial]

-- Evaluating a generic minor gives the minor of the matrix; minors vanish at the zero matrix.
example (r : ℕ) (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n) :
    eval (fun _ ↦ (0 : k)) (minorPolynomial r rows cols) = 0 := by
  simpa using eval_minorPolynomial r rows cols (0 : Matrix (Fin m) (Fin n) k)

-- The generic minors are among the equations.
example (r : ℕ) (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n) :
    (minorPolynomial r rows cols : MvPolynomial (Fin m × Fin n) k) ∈ minorIdeal r :=
  Ideal.subset_span ⟨(rows, cols), rfl⟩

-- Rank at most zero: the equations are all entries, and the tangent space at `0` is zero.
example : tangent (k := k) (m := m) (n := n) 0 0 = ⊥ := by
  refine eq_bot_iff.mpr fun v hv => ?_
  rw [Submodule.mem_bot]
  funext ⟨i, j⟩
  have h := mem_tangentIdeal_iff.mp hv
    (minorPolynomial 0 ⟨fun _ ↦ i, fun a b _ ↦ Subsingleton.elim (α := Fin 1) a b⟩
      ⟨fun _ ↦ j, fun a b _ ↦ Subsingleton.elim (α := Fin 1) a b⟩) (Ideal.subset_span ⟨(_, _), rfl⟩)
  simp only [minorPolynomial, Matrix.det_succ_row_zero, Fin.sum_univ_succ] at h
  simp at h
  exact h

-- Without `(r + 1)`-minors (more allowed rank than rows) there are no equations.
example (r : ℕ) (hr : m ≤ r) (A : Matrix (Fin m) (Fin n) k) : tangent r A = ⊤ := by
  have hempty : IsEmpty (Fin (r + 1) ↪ Fin m) := ⟨fun e ↦ by
    have := Fintype.card_le_of_embedding e
    simp only [Fintype.card_fin] at this
    omega⟩
  refine eq_top_iff.mpr fun v _ => mem_tangentIdeal_iff.mpr fun f hf => ?_
  have : minorIdeal (k := k) (m := m) (n := n) r = ⊥ := by
    rw [minorIdeal, Set.range_eq_empty, Ideal.span_empty]
  rw [this, Ideal.mem_bot] at hf
  simp [hf]

-- At the rank-one matrix `diag(1, 0)`, tangent directions have vanishing `(1, 1)` entry.
example (B : Matrix (Fin 2) (Fin 2) k)
    (hB : (fun ij ↦ B ij.1 ij.2) ∈ tangent 1 !![(1 : k), 0; 0, 0]) : B 1 1 = 0 := by
  have h := mem_tangentIdeal_iff.mp hB (minorPolynomial 1 (Function.Embedding.refl _)
    (Function.Embedding.refl _)) (Ideal.subset_span ⟨(_, _), rfl⟩)
  simpa [minorPolynomial, Matrix.det_succ_row_zero, Fin.sum_univ_succ, differential_mul,
    differential_neg, differential_add] using h
