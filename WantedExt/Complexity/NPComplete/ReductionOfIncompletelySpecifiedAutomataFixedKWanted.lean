/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA with a fixed bound `K ≥ 6` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL7] REDUCTION OF
INCOMPLETELY SPECIFIED AUTOMATA, comment: remains NP-complete for any fixed `K ≥ 6`;
C. P. Pfleeger, "State reduction in incompletely specified finite-state
machines", IEEE Transactions on Computers C-22 (1973), 1099-1102,
doi:10.1109/T-C.1973.223655 (the reference Garey and Johnson give for [AL7]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataFixedK

open MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata

/-!
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA with a fixed bound `K ≥ 6` is NP-complete

For a fixed constant `K ≥ 6`: given an incompletely specified deterministic finite state
automaton `A = (Q, Σ, δ, q₀, F)`, whose transition function `δ` maps a subset of `Q × Σ` into `Q`,
can `δ` be extended to a total function `Q × Σ → Q` so that the resulting completely specified
automaton has an equivalent reduced automaton with `K` or fewer states?

This is the restriction of REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA
(`WantedExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataWanted`) in which `K`
is no longer part of the instance. The instance is the automaton alone, and `withBound i K`
appends the fixed `K` to obtain an instance of that problem, whose `WellFormed` and
`ReductionOfIncompletelySpecifiedAutomataFeasible` are reused unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete for every fixed `K ≥ 6`.**
Source: Garey and Johnson (1979), [AL7], comment; Pfleeger (1973). -/
public theorem_wanted reductionOfIncompletelySpecifiedAutomataFixedK_npComplete (K : ℕ)
    (hK : 6 ≤ K) :
    fixedBoundDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedBoundDec K)

end MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataFixedK
