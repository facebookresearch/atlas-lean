/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 273, problem [PO5] CODE
GENERATION WITH UNLIMITED REGISTERS;
A. V. Aho, S. C. Johnson, and J. D. Ullman, "Code generation for expressions
with common subexpressions", Journal of the ACM 24 (1977), 146-160,
doi:10.1145/321992.322001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegisters

/-!
# CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which no vertex has out-degree larger than
`2`, a partition of `A` into disjoint sets `L` and `R` such that two arcs leaving the same
vertex always belong to different sets, and a positive integer `K`. QUESTION: is there a
program with `K` or fewer instructions for computing all the root vertices of `G` (those with
in-degree `0`), starting with all the leaves of `G` (those with out-degree `0`) stored in
registers and using only instructions of the form `rᵢ ← rⱼ` or `rᵢ ← rᵢ op rⱼ`, `i, j ∈ ℤ⁺`,
where a vertex `v` with out-degree `2` and outgoing arcs `(v, u) ∈ L` and `(v, w) ∈ R` can be
computed only by an instruction `rᵢ ← rᵢ op rⱼ` when `rᵢ` contains `u` and `rⱼ` contains `w`?

Reading of the machine. Registers are indexed by `ℕ` (there is no bound on how many are used).
At the start each leaf is in exactly one register and no register holds anything else (with
unboundedly many registers, which registers hold the leaves does not matter). `rᵢ ← rⱼ`
copies the content of `rⱼ` into `rᵢ`; `rᵢ ← rᵢ op rⱼ` computes a vertex `v` as above and puts
it in `rᵢ`. The program computes the roots when each root is held by some register at some
point of the run. Garey and Johnson give the OP instruction only for vertices of out-degree
`2`, so a vertex of out-degree `1` is never computed, as their entry reads.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete.** Source: Garey and Johnson
(1979), [PO5]; Aho, Johnson, and Ullman (1977). -/
public theorem_wanted codeGenerationWithUnlimitedRegisters_npComplete :
    codeGenerationWithUnlimitedRegistersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationWithUnlimitedRegistersDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegisters
