/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA with a fixed bound `K ≥ 6`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL7] REDUCTION OF
INCOMPLETELY SPECIFIED AUTOMATA, comment: remains NP-complete for any fixed `K ≥ 6`;
C. P. Pfleeger, "State reduction in incompletely specified finite-state
machines", IEEE Transactions on Computers C-22 (1973), 1099-1102,
doi:10.1109/T-C.1973.223655 (the reference Garey and Johnson give for [AL7]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataFixedK

open MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata

/-- An instance for a fixed bound: state count `n` (states `Fin n`), alphabet size `m` (letters
`Fin m`), the specified transitions `((q, a), q')`, start state `q₀`, and accept states `F`. -/
abbrev FixedBoundInstance := ℕ × ℕ × List ((ℕ × ℕ) × ℕ) × ℕ × List ℕ

/-- The REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA instance given by the automaton `i` and the
bound `K`. -/
abbrev withBound (i : FixedBoundInstance) (K : ℕ) :
    ReductionOfIncompletelySpecifiedAutomataInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

open Classical in
/-- REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA with the bound fixed to `K`, as a decision
problem over bitstrings. -/
noncomputable def fixedBoundDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed (withBound i K) ∧
      ReductionOfIncompletelySpecifiedAutomataFeasible (withBound i K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataFixedK
