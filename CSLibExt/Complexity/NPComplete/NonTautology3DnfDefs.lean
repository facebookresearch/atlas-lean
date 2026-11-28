/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-TAUTOLOGY OF 3DNF: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO8] NON-TAUTOLOGY, comment: remains
NP-complete for `E` in disjunctive normal form with three literals per disjunct;
S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the 3rd Annual ACM
Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.KeyTheorems.KarpLubyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonTautology3Dnf

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, and the disjuncts of `E`, each a
list of literals `(x, b)`. -/
abbrev NonTautology3DnfInstance := ℕ × List (List (ℕ × Bool))

/-- Well-formedness of an instance: the expression has at least one disjunct, every disjunct
consists of three literals, and every literal names one of `u₀, …, u_{n-1}`. -/
def WellFormed (i : NonTautology3DnfInstance) : Prop :=
  i.2 ≠ [] ∧ ∀ t ∈ i.2, t.length = 3 ∧ ∀ l ∈ t, l.1 < i.1

/-- Some truth assignment makes the expression false. Assignments are functions `ℕ → Bool`;
under `WellFormed` only their values on `0, …, n - 1` matter. -/
def NonTautology3DnfFeasible (i : NonTautology3DnfInstance) : Prop :=
  ∃ σ : ℕ → Bool, ¬ MetaMathlibExt.Complexity.KeyTheorems.KarpLuby.dnfSat σ i.2

open Classical in
/-- NON-TAUTOLOGY OF 3DNF as a decision problem over bitstrings. -/
noncomputable def nonTautology3DnfDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonTautology3DnfInstance) x with
  | some i => decide (WellFormed i ∧ NonTautology3DnfFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NonTautology3Dnf
