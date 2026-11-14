/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION ON A ONE-REGISTER MACHINE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), pp. 272-273, problem [PO4]
CODE GENERATION ON A ONE-REGISTER MACHINE;
J. Bruno and R. Sethi, "Code generation for a one-register machine", Journal of
the ACM 23 (1976), 502-510, doi:10.1145/321958.321971.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationOnAOneRegisterMachine

/-!
# CODE GENERATION ON A ONE-REGISTER MACHINE is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which no vertex has out-degree larger than
`2`, and a positive integer `K`. QUESTION: is there a program with `K` or fewer instructions
for computing all the root vertices of `G` (those with in-degree `0`) on a one-register
machine, starting with all the leaves of `G` (those with out-degree `0`) in memory and using
only LOAD, STORE and OP instructions?

The machine, as Garey and Johnson define it: a LOAD instruction copies a specified vertex
(from memory) into the register. A STORE instruction copies the vertex in the register into
memory. A new vertex `v` can be computed by an OP instruction if the vertex `u` in the register
satisfies `(v, u) ∈ A` and, if there is another vertex `u'` with `(v, u') ∈ A`, then `u'` is in
memory; executing the OP instruction replaces `u` by `v` in the register. The computation of a
new vertex is not completed until it is copied into memory by a STORE instruction, so the
program computes the roots when every root is in memory after its last instruction. The
register is empty at the start.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), arc list of `G` (`(v, u)` is the arc
from `v` to `u`), and the bound `K`. -/
abbrev CodeGenerationOnAOneRegisterMachineInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The digraph of the instance on `Fin n`: `v → u` is an arc iff `(v, u)` is in the arc
list. -/
def Graph (i : CodeGenerationOnAOneRegisterMachineInstance) : Digraph (Fin i.1) where
  Adj v u := ((v : ℕ), (u : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are
vertices, the digraph is acyclic (no vertex reaches itself by a nonempty directed path), no
vertex has out-degree larger than `2`, and `K` is positive. -/
def WellFormed (i : CodeGenerationOnAOneRegisterMachineInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧
    (∀ v, {u | (Graph i).Adj v u}.ncard ≤ 2) ∧ 0 < i.2.2

/-- An instruction of the one-register machine on vertices `Fin n`: LOAD `v`, STORE, or OP
computing `v`. -/
inductive Instruction (n : ℕ) where
  | load (v : Fin n)
  | store
  | op (v : Fin n)

/-- A machine state: the register content (`none` while the register is empty) and the set of
vertices in memory. -/
abbrev MachineState (n : ℕ) := Option (Fin n) × Set (Fin n)

/-- `Step i s ins s'`: executing `ins` in state `s` is allowed and leads to `s'`. LOAD `v`
needs `v` in memory and puts it in the register; STORE needs a vertex `u` in the register and
adds `u` to memory; OP `v` needs a vertex `u` in the register with `(v, u) ∈ A` and every other
`u'` with `(v, u') ∈ A` in memory, and replaces `u` by `v` in the register. -/
def Step (i : CodeGenerationOnAOneRegisterMachineInstance) :
    MachineState i.1 → Instruction i.1 → MachineState i.1 → Prop
  | (_, M), .load v, s' => v ∈ M ∧ s' = (some v, M)
  | (r, M), .store, s' => ∃ u, r = some u ∧ s' = (some u, insert u M)
  | (r, M), .op v, s' => ∃ u, r = some u ∧ (Graph i).Adj v u ∧
      (∀ u', (Graph i).Adj v u' → u' ≠ u → u' ∈ M) ∧ s' = (some v, M)

/-- A program `p` of at most `K` instructions and the states `s 0, ..., s |p|` it passes
through: `s 0` has an empty register and the leaves (out-degree `0`) in memory, instruction
`k` leads from `s k` to `s (k + 1)`, and every root (in-degree `0`) is in memory in the last
state. -/
def CodeGenerationOnAOneRegisterMachineFeasible
    (i : CodeGenerationOnAOneRegisterMachineInstance) : Prop :=
  ∃ p : List (Instruction i.1), p.length ≤ i.2.2 ∧
    ∃ s : Fin (p.length + 1) → MachineState i.1,
      s 0 = (none, {u | ∀ w, ¬ (Graph i).Adj u w}) ∧
      (∀ k : Fin p.length, Step i (s k.castSucc) p[k] (s k.succ)) ∧
      ∀ v, (∀ w, ¬ (Graph i).Adj w v) → v ∈ (s (Fin.last p.length)).2

open Classical in
/-- CODE GENERATION ON A ONE-REGISTER MACHINE as a decision problem over bitstrings. -/
noncomputable def codeGenerationOnAOneRegisterMachineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationOnAOneRegisterMachineInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationOnAOneRegisterMachineFeasible i)
  | none => false

/-- **CODE GENERATION ON A ONE-REGISTER MACHINE is NP-complete.** Source: Garey and Johnson
(1979), [PO4]; Bruno and Sethi (1976). -/
public theorem_wanted codeGenerationOnAOneRegisterMachine_npComplete :
    codeGenerationOnAOneRegisterMachineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationOnAOneRegisterMachineDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationOnAOneRegisterMachine
