/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH UNLIMITED REGISTERS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 273, problem [PO5] CODE
GENERATION WITH UNLIMITED REGISTERS;
A. V. Aho, S. C. Johnson, and J. D. Ullman, "Code generation for expressions
with common subexpressions", Journal of the ACM 24 (1977), 146-160,
doi:10.1145/321992.322001.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegisters

/-- An instance: vertex count `n` (vertices `Fin n`), the arc list (`(v, u, true)` is an arc
`(v, u) ∈ L`, `(v, u, false)` an arc `(v, u) ∈ R`), and the bound `K`. -/
abbrev CodeGenerationWithUnlimitedRegistersInstance := ℕ × List (ℕ × ℕ × Bool) × ℕ

/-- The digraph `G` of the instance on `Fin n`: `v → u` is an arc iff `(v, u)` is in `L` or
in `R`. -/
def Graph (i : CodeGenerationWithUnlimitedRegistersInstance) : Digraph (Fin i.1) where
  Adj v u := ∃ b, ((v : ℕ), (u : ℕ), b) ∈ i.2.1

/-- Well-formedness of an instance: no arc `(v, u)` is listed twice (so `L` and `R` are
disjoint and partition `A`), endpoints are vertices, the digraph is acyclic, no vertex has
out-degree larger than `2`, two arcs leaving the same vertex belong to different sets, and `K`
is positive. -/
def WellFormed (i : CodeGenerationWithUnlimitedRegistersInstance) : Prop :=
  (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧
    (∀ v, {u | (Graph i).Adj v u}.ncard ≤ 2) ∧
    (∀ a ∈ i.2.1, ∀ a' ∈ i.2.1, a.1 = a'.1 → a.2.1 ≠ a'.2.1 → a.2.2 ≠ a'.2.2) ∧ 0 < i.2.2

/-- An instruction: `copy a b` is `r_a ← r_b`, and `op a b` is `r_a ← r_a op r_b`. -/
inductive Instruction where
  | copy (a b : ℕ)
  | op (a b : ℕ)

/-- Register contents: `s r` is the vertex in register `r`, or `none` if `r` is empty. -/
abbrev Registers (n : ℕ) := ℕ → Option (Fin n)

/-- `Step i s ins s'`: executing `ins` on registers `s` is allowed and leads to `s'`.
`r_a ← r_b` copies `r_b` into `r_a`; `r_a ← r_a op r_b` needs `r_a` to hold `u` and `r_b` to
hold `w` with `(v, u) ∈ L` and `(v, w) ∈ R` for some `v`, and puts `v` in `r_a`. -/
def Step (i : CodeGenerationWithUnlimitedRegistersInstance) (s : Registers i.1) :
    Instruction → Registers i.1 → Prop
  | .copy a b, s' => s' = Function.update s a (s b)
  | .op a b, s' => ∃ v u w : Fin i.1, s a = some u ∧ s b = some w ∧
      ((v : ℕ), (u : ℕ), true) ∈ i.2.1 ∧ ((v : ℕ), (w : ℕ), false) ∈ i.2.1 ∧
      s' = Function.update s a (some v)

/-- A vertex of out-degree `0`. -/
def IsLeaf (i : CodeGenerationWithUnlimitedRegistersInstance) (u : Fin i.1) : Prop :=
  ∀ w, ¬ (Graph i).Adj u w

/-- A program `p` of at most `K` instructions and the register contents `s 0, ..., s |p|` it
passes through: in `s 0` every register holds a leaf or nothing and every leaf is in exactly
one register, instruction `k` leads from `s k` to `s (k + 1)`, and every root (in-degree `0`)
is held by some register in some `s k`. -/
def CodeGenerationWithUnlimitedRegistersFeasible
    (i : CodeGenerationWithUnlimitedRegistersInstance) : Prop :=
  ∃ p : List Instruction, p.length ≤ i.2.2 ∧
    ∃ s : Fin (p.length + 1) → Registers i.1,
      (∀ r u, s 0 r = some u → IsLeaf i u) ∧ (∀ u, IsLeaf i u → ∃! r, s 0 r = some u) ∧
      (∀ k : Fin p.length, Step i (s k.castSucc) p[k] (s k.succ)) ∧
      ∀ v, (∀ w, ¬ (Graph i).Adj w v) → ∃ k r, s k r = some v

open Classical in
/-- CODE GENERATION WITH UNLIMITED REGISTERS as a decision problem over bitstrings. -/
noncomputable def codeGenerationWithUnlimitedRegistersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationWithUnlimitedRegistersInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationWithUnlimitedRegistersFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegisters
