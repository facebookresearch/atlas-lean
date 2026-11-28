/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO12] INEQUIVALENCE OF PROGRAMS
WITH ASSIGNMENTS;
P. J. Downey and R. Sethi, "Assignment commands and array structures", Proceedings of the
17th Annual Symposium on Foundations of Computer Science (1976), 57-66,
doi:10.1109/SFCS.1976.7.
-/
module

public import Mathlib.Logic.Function.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignments

/-- An assignment `(x₀, x₁, x₂, x₃, x₄)`, read `x₀ ← if x₁ = x₂ then x₃ else x₄`. -/
abbrev Assignment := ℕ × ℕ × ℕ × ℕ × ℕ

/-- An instance: the number `n` of variables, the programs `P₁` and `P₂`, and the size `|V|`
of the value set. -/
abbrev InequivalenceProgramsAssignmentsInstance :=
  ℕ × List Assignment × List Assignment × ℕ

/-- Executes one assignment `x₀ ← if x₁ = x₂ then x₃ else x₄` on the store `s`. -/
def execAssignment (s : ℕ → ℕ) (c : Assignment) : ℕ → ℕ :=
  Function.update s c.1 (if s c.2.1 = s c.2.2.1 then s c.2.2.2.1 else s c.2.2.2.2)

/-- The final store of the program `P` started from the store `s`. -/
def run (P : List Assignment) (s : ℕ → ℕ) : ℕ → ℕ :=
  P.foldl execAssignment s

/-- Well-formedness of an instance: every assignment of either program names only the
variables `0, …, n - 1`. -/
def WellFormed (i : InequivalenceProgramsAssignmentsInstance) : Prop :=
  ∀ c ∈ i.2.1 ++ i.2.2.1,
    c.1 < i.1 ∧ c.2.1 < i.1 ∧ c.2.2.1 < i.1 ∧ c.2.2.2.1 < i.1 ∧ c.2.2.2.2 < i.1

/-- The store holding `a j` in variable `j < n` (other indices hold `0` and are never read by a
well-formed program). -/
def initialStore {n v : ℕ} (a : Fin n → Fin v) (j : ℕ) : ℕ :=
  if h : j < n then (a ⟨j, h⟩ : ℕ) else 0

/-- Some initial assignment `a : X → V` makes the two programs end with different values in
some variable `x ∈ X`. -/
def InequivalenceProgramsAssignmentsFeasible (i : InequivalenceProgramsAssignmentsInstance) :
    Prop :=
  ∃ a : Fin i.1 → Fin i.2.2.2, ∃ x : Fin i.1,
    run i.2.1 (initialStore a) x ≠ run i.2.2.1 (initialStore a) x

open Classical in
/-- INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS as a decision problem over bitstrings. -/
noncomputable def inequivalenceProgramsAssignmentsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceProgramsAssignmentsInstance) x with
  | some i => decide (WellFormed i ∧ InequivalenceProgramsAssignmentsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignments
