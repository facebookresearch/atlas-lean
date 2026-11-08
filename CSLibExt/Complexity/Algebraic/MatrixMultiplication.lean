/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.ArithmeticCircuit
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Fintype.Card

/-!
# Arithmetic circuits for rectangular matrix multiplication

Correctness is equality on every field-valued input assignment, including finite
fields. The charged operations are circuit nodes, not the runtime of the recursive
semantic evaluator. Constants, input access and output references are free.
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

@[expose] public section

/-- A circuit whose inputs and outputs are actual rectangular matrix entries. -/
abbrev MatrixArithmeticCircuit (F : Type u) (m r n : ℕ) :=
  ArithmeticCircuit F ((Fin m × Fin r) ⊕ (Fin r × Fin n)) (Fin m × Fin n)

/-- The actual scalar assignment supplied by a pair of rectangular matrices. -/
def matrixInput {F : Type u} {m r n : ℕ}
    (A : Matrix (Fin m) (Fin r) F) (B : Matrix (Fin r) (Fin n) F) :
    ((Fin m × Fin r) ⊕ (Fin r × Fin n)) → F :=
  Sum.elim (fun p => A p.1 p.2) (fun p => B p.1 p.2)

/-- Correctness on all actual inputs, without a formal-polynomial identity restriction. -/
def IsMatrixMultiplication {F : Type u} [Field F] {m r n : ℕ}
    (c : MatrixArithmeticCircuit F m r n) : Prop :=
  ∀ (A : Matrix (Fin m) (Fin r) F) (B : Matrix (Fin r) (Fin n) F)
    (i : Fin m) (j : Fin n), c.evaluate (matrixInput A B) (i, j) = (A * B) i j

/-- One multiplication per output computes the inner-dimension-one matrix product. -/
def outerMatrixCircuit (F : Type u) (m n : ℕ) : MatrixArithmeticCircuit F m 1 n where
  size := (ArithmeticCircuit.outerProduct F m n).size
  gate i := .mul (.input (.inl ((finProdFinEquiv.symm i).1, 0)))
    (.input (.inr (0, (finProdFinEquiv.symm i).2)))
  output ij := .node (finProdFinEquiv ij)

/-- The direct outer-product matrix circuit is correct for every field input. -/
theorem outerMatrixCircuit_correct {F : Type u} [Field F] (m n : ℕ) :
    IsMatrixMultiplication (outerMatrixCircuit F m n) := by
  intro A B i j
  simp [outerMatrixCircuit, ArithmeticCircuit.evaluate,
    ArithmeticCircuit.outerProduct, ArithmeticCircuit.evaluateNode,
    ArithmeticGate.evaluate, ArithmeticOperand.evaluate, matrixInput, Matrix.mul_apply]

/-- The exact charged cost of the matrix outer-product circuit. -/
theorem outerMatrixCircuit_size (F : Type u) (m n : ℕ) :
    (outerMatrixCircuit F m n).size = m * n := rfl

/-- Every nonconstant matrix-product output must be computed by a charged node. -/
theorem IsMatrixMultiplication.output_is_node {F : Type u} [Field F] {m r n : ℕ}
    {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c)
    (k : Fin r) (i : Fin m) (j : Fin n) :
    ∃ t : Fin c.size, c.output (i, j) = .node t := by
  cases h : c.output (i, j) with
  | constant x =>
    have hz := hc 0 0 i j
    have ho := hc (Matrix.single i k 1) (Matrix.single k j 1) i j
    simp [ArithmeticCircuit.evaluate, h, ArithmeticOperand.evaluate] at hz
    simp [ArithmeticCircuit.evaluate, h, ArithmeticOperand.evaluate] at ho
    exfalso
    simp [hz] at ho
  | input a =>
    cases a with
    | inl a =>
      have hh := hc (Matrix.single a.1 a.2 1) 0 i j
      exfalso
      simp [ArithmeticCircuit.evaluate, h, ArithmeticOperand.evaluate, matrixInput] at hh
    | inr b =>
      have hh := hc 0 (Matrix.single b.1 b.2 1) i j
      exfalso
      simp [ArithmeticCircuit.evaluate, h, ArithmeticOperand.evaluate, matrixInput] at hh
  | node t => exact ⟨t, rfl⟩

/-- Distinct matrix entries require distinct charged nodes, over every field. -/
theorem IsMatrixMultiplication.output_cost_le {F : Type u} [Field F] {m r n : ℕ}
    {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c)
    (k : Fin r) : m * n ≤ c.size := by
  classical
  have hex : ∀ p : Fin m × Fin n, ∃ t : Fin c.size, c.output p = .node t :=
    fun p => hc.output_is_node k p.1 p.2
  choose f hf using hex
  have hi : Function.Injective f := by
    intro p q he
    have ho : c.output p = c.output q := by rw [hf p, hf q, he]
    let A := Matrix.single p.1 k (1 : F)
    let B := Matrix.single k p.2 (1 : F)
    have hh : c.evaluate (matrixInput A B) p = c.evaluate (matrixInput A B) q :=
      congrArg (fun o => o.evaluate (matrixInput A B) (c.evaluateNode (matrixInput A B))) ho
    rw [hc A B p.1 p.2, hc A B q.1 q.2] at hh
    by_contra hne
    have hpq : ¬ (p.1 = q.1 ∧ p.2 = q.2) := fun h => hne (Prod.ext h.1 h.2)
    simp [A, B, hpq] at hh
  simpa using Fintype.card_le_of_injective f hi

end

end Cslib.Complexity.Algebraic
