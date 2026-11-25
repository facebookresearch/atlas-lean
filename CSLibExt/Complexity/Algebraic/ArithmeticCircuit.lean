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

/-- **Arithmetic operand.** An arithmetic operand over $F$ with inputs indexed by $A$ and $n$
nodes is a constant $x \in F$, an input $a \in A$, or a reference to a node $i < n$. -/
public inductive ArithmeticOperand (F : Type u) (A : Type v) (n : ℕ)
  | constant : F → ArithmeticOperand F A n
  | input : A → ArithmeticOperand F A n
  | node : Fin n → ArithmeticOperand F A n

/-- **Arithmetic gate.** An arithmetic gate over $F$ with inputs indexed by $A$ and $n$ prior
nodes is an addition, a subtraction or a multiplication of two arithmetic operands, each of
which is a constant in $F$, an input $a \in A$ or a reference to a node $i < n$. -/
public inductive ArithmeticGate (F : Type u) (A : Type v) (n : ℕ)
  | add : ArithmeticOperand F A n → ArithmeticOperand F A n → ArithmeticGate F A n
  | sub : ArithmeticOperand F A n → ArithmeticOperand F A n → ArithmeticGate F A n
  | mul : ArithmeticOperand F A n → ArithmeticOperand F A n → ArithmeticGate F A n

/-- **Arithmetic circuit.** An arithmetic circuit over $F$ with inputs indexed by $A$ and
outputs indexed by $B$ consists of a size $s \in \mathbb{N}$, a gate $g_i$ for each $i < s$, and
an output operand for each $b \in B$. Each gate $g_i$ is an addition, subtraction or
multiplication of two operands, each a constant in $F$, an input $a \in A$ or an earlier gate
$g_j$ with $j < i$; an output operand is a constant in $F$, an input or any gate $g_j$ with
$j < s$.

Constants and inputs are free; each gate counts as one scalar operation. -/
public structure ArithmeticCircuit (F : Type u) (A : Type v) (B : Type w) where
  size : ℕ
  gate (i : Fin size) : ArithmeticGate F A i.val
  output : B → ArithmeticOperand F A size

@[expose] public section

/-- **Operand evaluation.** Let $F$ and $A$ be types and $n \in \mathbb{N}$. Given a value in $F$
for each input $a \in A$ and a value in $F$ for each node $i < n$, an arithmetic operand over $F$
with inputs indexed by $A$ and $n$ nodes evaluates as follows: a constant $x$ evaluates to $x$, an
input $a$ to its assigned value, and a reference to node $i$ to the value given for node $i$. -/
def ArithmeticOperand.evaluate {F : Type u} {A : Type v} {n : ℕ}
    (input : A → F) (computed : Fin n → F) : ArithmeticOperand F A n → F
  | .constant x => x
  | .input a => input a
  | .node i => computed i

/-- **Gate evaluation.** Let $F$ be a type with addition, subtraction and multiplication, let $A$
be a type and let $n \in \mathbb{N}$. Given a value in $F$ for each input $a \in A$ and a value
in $F$ for each node $i < n$, write $v(x)$ for the value of an arithmetic operand $x$: a constant
evaluates to itself, an input $a$ to its assigned value and a reference to node $i$ to the value
given for node $i$. An arithmetic gate over $F$ with inputs indexed by $A$ and $n$ prior nodes
that adds, subtracts or multiplies the operands $x$ and $y$ evaluates to $v(x) + v(y)$,
$v(x) - v(y)$ or $v(x) \cdot v(y)$ respectively. -/
def ArithmeticGate.evaluate {F : Type u} {A : Type v} {n : ℕ}
    [Add F] [Sub F] [Mul F] (input : A → F) (computed : Fin n → F) :
    ArithmeticGate F A n → F
  | .add a b => a.evaluate input computed + b.evaluate input computed
  | .sub a b => a.evaluate input computed - b.evaluate input computed
  | .mul a b => a.evaluate input computed * b.evaluate input computed

namespace ArithmeticCircuit

/-- **Extensionality for arithmetic circuits.** Two arithmetic circuits over $F$ with inputs
indexed by $A$ and outputs indexed by $B$ are equal if they have the same size, the same gate at
each position and the same output operand for each $b \in B$. -/
@[ext] theorem ext {F : Type u} {A : Type v} {B : Type w}
    {c d : ArithmeticCircuit F A B} (hs : c.size = d.size)
    (hg : HEq c.gate d.gate) (ho : HEq c.output d.output) : c = d := by
  cases c
  cases d
  cases hs
  cases hg
  cases ho
  rfl

/-- **Value of a gate in a circuit.** Let $F$ be a type with addition, subtraction and
multiplication and let $c$ be an arithmetic circuit over $F$ with inputs indexed by $A$. Given a
value in $F$ for each input $a \in A$, the value of gate $g_i$ of $c$ is the value of the operation
of $g_i$ on its two operands, where a constant $x$ has value $x$, an input has its assigned value
and a reference to an earlier gate $g_j$ with $j < i$ takes the value of $g_j$, defined
recursively. -/
def evaluateNode {F : Type u} {A : Type v} {B : Type w} [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (input : A → F) (i : Fin c.size) : F :=
  (c.gate i).evaluate input (fun j =>
    evaluateNode c input ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
termination_by i.val
decreasing_by exact j.isLt

/-- **Circuit evaluation.** Let $F$ be a type with addition, subtraction and multiplication and
let $c$ be an arithmetic circuit over $F$ with inputs indexed by $A$ and outputs indexed by $B$.
Given a value in $F$ for each input $a \in A$, the value of $c$ at an output $b \in B$ is the value
of the output operand of $b$, where a constant $x$ has value $x$, an input has its assigned value
and a reference to gate $g_j$ has the value of $g_j$, each gate being evaluated from the values of
the gates before it. -/
def evaluate {F : Type u} {A : Type v} {B : Type w} [Add F] [Sub F] [Mul F]
    (c : ArithmeticCircuit F A B) (input : A → F) (b : B) : F :=
  (c.output b).evaluate input (c.evaluateNode input)

/-- **Outer-product circuit.** For a type $F$ of scalars and $m, n \in \mathbb{N}$, the
outer-product circuit has inputs $a_0, \dots, a_{m-1}$ and $b_0, \dots, b_{n-1}$, one output for
each pair $(i, j)$ with $i < m$ and $j < n$, and exactly $mn$ gates: the gate for $(i, j)$
multiplies $a_i$ by $b_j$, and the output at $(i, j)$ is that gate. -/
def outerProduct (F : Type u) (m n : ℕ) :
    ArithmeticCircuit F (Fin m ⊕ Fin n) (Fin m × Fin n) where
  size := m * n
  gate i := .mul (.input (.inl (finProdFinEquiv.symm i).1))
    (.input (.inr (finProdFinEquiv.symm i).2))
  output ij := .node (finProdFinEquiv ij)

/-- **Correctness of the outer-product circuit.** Let $F$ be a type with addition, subtraction and
multiplication. For all $m, n \in \mathbb{N}$, $a \in F^m$, $b \in F^n$, $i < m$ and $j < n$, the
outer-product circuit over $F$ evaluated on the inputs $a$ and $b$ has value $a_i b_j$ at the
output $(i, j)$. -/
theorem outerProduct_evaluate {F : Type u} [Add F] [Sub F] [Mul F] {m n : ℕ}
    (a : Fin m → F) (b : Fin n → F) (i : Fin m) (j : Fin n) :
    (outerProduct F m n).evaluate (Sum.elim a b) (i, j) = a i * b j := by
  simp [evaluate, outerProduct, ArithmeticOperand.evaluate, evaluateNode,
    ArithmeticGate.evaluate]

/-- **Size of the outer-product circuit.** For every $F$ and all $m, n \in \mathbb{N}$, the
outer-product circuit over $F$ for $m \times n$ outer products has exactly $mn$ gates. -/
theorem outerProduct_size (F : Type u) (m n : ℕ) :
    (outerProduct F m n).size = m * n := rfl

end ArithmeticCircuit

end

end Cslib.Complexity.Algebraic
