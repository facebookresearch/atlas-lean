/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMUTATIVE CODE GENERATION WITH UNLIMITED REGISTERS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO5] CODE GENERATION WITH UNLIMITED
REGISTERS, p. 273 (comment: the "commutative" variant in which instructions of the form
`rᵢ ← rⱼ op rᵢ` are also allowed is NP-complete [Aho, Johnson, and Ullman, 1977b]; Garey and
Johnson list [Aho, Johnson, and Ullman, 1977b] as a private communication, which was not
available);
A. V. Aho, S. C. Johnson, and J. D. Ullman, "Code generation for expressions with common
subexpressions", Journal of the ACM 24 (1977), 146-160, doi:10.1145/321992.322001 (the
non-commutative problem [PO5]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegistersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommutativeCodeGenerationUnlimitedRegisters

open CodeGenerationWithUnlimitedRegisters (Graph IsLeaf Instruction Registers Step)

/-- An instance, as in `CodeGenerationWithUnlimitedRegistersWanted`: vertex count `n`
(vertices `Fin n`), the arc list (`(v, u, true)` is an arc `(v, u) ∈ L`, `(v, u, false)` an
arc `(v, u) ∈ R`), and the bound `K`. -/
abbrev CommutativeCodeGenerationUnlimitedRegistersInstance :=
  CodeGenerationWithUnlimitedRegisters.CodeGenerationWithUnlimitedRegistersInstance

/-- Well-formedness of an instance, exactly as in `CodeGenerationWithUnlimitedRegistersWanted`:
a simple acyclic digraph with out-degrees at most `2`, the two arcs leaving a vertex in
different sets, and `0 < K`. -/
def WellFormed (i : CommutativeCodeGenerationUnlimitedRegistersInstance) : Prop :=
  CodeGenerationWithUnlimitedRegisters.WellFormed i

/-- An instruction of the commutative machine: `base ins` is an instruction of the parent
(`r_a ← r_b` or `r_a ← r_a op r_b`), and `opRev a b` is `r_a ← r_b op r_a`. -/
inductive CommInstruction where
  | base (ins : Instruction)
  | opRev (a b : ℕ)

/-- `CommStep i s ins s'`: executing `ins` on registers `s` is allowed and leads to `s'`. A
parent instruction behaves as in `CodeGenerationWithUnlimitedRegisters.Step`;
`r_a ← r_b op r_a` needs `r_b` to hold `u` and `r_a` to hold `w` with `(v, u) ∈ L` and
`(v, w) ∈ R` for some `v`, and puts `v` in `r_a`. -/
def CommStep (i : CommutativeCodeGenerationUnlimitedRegistersInstance) (s : Registers i.1) :
    CommInstruction → Registers i.1 → Prop
  | .base ins, s' => Step i s ins s'
  | .opRev a b, s' => ∃ v u w : Fin i.1, s b = some u ∧ s a = some w ∧
      ((v : ℕ), (u : ℕ), true) ∈ i.2.1 ∧ ((v : ℕ), (w : ℕ), false) ∈ i.2.1 ∧
      s' = Function.update s a (some v)

/-- A program `p` of at most `K` instructions of the commutative machine and the register
contents `s 0, ..., s |p|` it passes through: in `s 0` every register holds a leaf or nothing
and every leaf is in exactly one register, instruction `k` leads from `s k` to `s (k + 1)`, and
every root (in-degree `0`) is held by some register in some `s k`. -/
def CommutativeCodeGenerationUnlimitedRegistersFeasible
    (i : CommutativeCodeGenerationUnlimitedRegistersInstance) : Prop :=
  ∃ p : List CommInstruction, p.length ≤ i.2.2 ∧
    ∃ s : Fin (p.length + 1) → Registers i.1,
      (∀ r u, s 0 r = some u → IsLeaf i u) ∧ (∀ u, IsLeaf i u → ∃! r, s 0 r = some u) ∧
      (∀ k : Fin p.length, CommStep i (s k.castSucc) p[k] (s k.succ)) ∧
      ∀ v, (∀ w, ¬ (Graph i).Adj w v) → ∃ k r, s k r = some v

open Classical in
/-- COMMUTATIVE CODE GENERATION WITH UNLIMITED REGISTERS as a decision problem over
bitstrings. -/
noncomputable def commutativeCodeGenerationUnlimitedRegistersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CommutativeCodeGenerationUnlimitedRegistersInstance) x with
  | some i => decide (WellFormed i ∧ CommutativeCodeGenerationUnlimitedRegistersFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CommutativeCodeGenerationUnlimitedRegisters
