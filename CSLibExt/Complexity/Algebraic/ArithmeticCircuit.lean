/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.Defs

/-!
# Finite acyclic scalar arithmetic circuits

Constants and input access are free. Each addition, subtraction or multiplication
node is one scalar operation; references only point to earlier nodes. Evaluation
uses actual field values, without a symbolic-polynomial correctness restriction.
Allocation, indexing, output writes and bit operations are outside this model.
-/

set_option autoImplicit false

universe u v w

namespace Cslib.Complexity.Algebraic

/-- A scalar literal, an input coordinate, or a previously computed node. -/
public inductive ArithmeticOperand (F : Type u) (A : Type v) (n : ℕ)
  | constant : F → ArithmeticOperand F A n
  | input : A → ArithmeticOperand F A n
  | node : Fin n → ArithmeticOperand F A n

/-- One charged scalar arithmetic operation. -/
public inductive ArithmeticGate (F : Type u) (A : Type v) (n : ℕ)
  | add : ArithmeticOperand F A n → ArithmeticOperand F A n → ArithmeticGate F A n
  | sub : ArithmeticOperand F A n → ArithmeticOperand F A n → ArithmeticGate F A n
  | mul : ArithmeticOperand F A n → ArithmeticOperand F A n → ArithmeticGate F A n

/-- A finite directed acyclic arithmetic circuit with free output references. -/
public structure ArithmeticCircuit (F : Type u) (A : Type v) (B : Type w) where
  size : ℕ
  gate (i : Fin size) : ArithmeticGate F A i.val
  output : B → ArithmeticOperand F A size

@[expose] public section

/-- Evaluate an operand using the input assignment and computed prefix. -/
def ArithmeticOperand.evaluate {F : Type u} {A : Type v} {n : ℕ}
    (input : A → F) (computed : Fin n → F) : ArithmeticOperand F A n → F
  | .constant x => x
  | .input a => input a
  | .node i => computed i

/-- Evaluate the charged operation on its two actual operands. -/
def ArithmeticGate.evaluate {F : Type u} {A : Type v} {n : ℕ}
    [Add F] [Sub F] [Mul F] (input : A → F) (computed : Fin n → F) :
    ArithmeticGate F A n → F
  | .add a b => a.evaluate input computed + b.evaluate input computed
  | .sub a b => a.evaluate input computed - b.evaluate input computed
  | .mul a b => a.evaluate input computed * b.evaluate input computed

namespace ArithmeticCircuit

/-- Circuits with the same length, charged gates and output references are equal. -/
@[ext] theorem ext {F : Type u} {A : Type v} {B : Type w}
    {c d : ArithmeticCircuit F A B} (hs : c.size = d.size)
    (hg : HEq c.gate d.gate) (ho : HEq c.output d.output) : c = d := by
  cases c
  cases d
  cases hs
  cases hg
  cases ho
  rfl

/-- Actual evaluation of a node, recursively evaluating only prior references. -/
def evaluateNode {F : Type u} {A : Type v} {B : Type w} [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (input : A → F) (i : Fin c.size) : F :=
  (c.gate i).evaluate input (fun j =>
    evaluateNode c input ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
termination_by i.val
decreasing_by exact j.isLt

/-- Read an output after the actual arithmetic computation. -/
def evaluate {F : Type u} {A : Type v} {B : Type w} [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (input : A → F) (b : B) : F :=
  (c.output b).evaluate input (c.evaluateNode input)

/-- The direct outer-product circuit has exactly one multiplication per output. -/
def outerProduct (F : Type u) (m n : ℕ) :
    ArithmeticCircuit F (Fin m ⊕ Fin n) (Fin m × Fin n) where
  size := m * n
  gate i := .mul (.input (.inl (finProdFinEquiv.symm i).1))
    (.input (.inr (finProdFinEquiv.symm i).2))
  output ij := .node (finProdFinEquiv ij)

/-- The outer-product circuit returns the actual product of its two scalar inputs. -/
theorem outerProduct_evaluate {F : Type u} [Add F] [Sub F] [Mul F] {m n : ℕ}
    (a : Fin m → F) (b : Fin n → F) (i : Fin m) (j : Fin n) :
    (outerProduct F m n).evaluate (Sum.elim a b) (i, j) = a i * b j := by
  simp [evaluate, outerProduct, ArithmeticOperand.evaluate, evaluateNode,
    ArithmeticGate.evaluate]

/-- The exact arithmetic-operation count of the finite outer-product circuit. -/
theorem outerProduct_size (F : Type u) (m n : ℕ) :
    (outerProduct F m n).size = m * n := rfl

end ArithmeticCircuit

end

end Cslib.Complexity.Algebraic
