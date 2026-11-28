/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EXACT COVER: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM EXACT COVER (decision version);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (EXACT COVER is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.ExactCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumExactCover

/-- An instance: the size `n` of `S`, the members of `C` in order, and the bound `K`. -/
abbrev MinimumExactCoverInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: `(n, C)` is a well-formed `ExactCoverWanted` instance. -/
def WellFormed (i : MinimumExactCoverInstance) : Prop :=
  ExactCover.WellFormed (i.1, i.2.1)

/-- Some set `C'` of positions in the list of members covers every element of `S`, and the
lengths of the selected list entries sum to at most `K` (a member listed with a repeated element
counts it twice; for well-formed members the length is the size). -/
def MinimumExactCoverFeasible (i : MinimumExactCoverInstance) : Prop :=
  ∃ C' : Finset (Fin i.2.1.length), (∀ x < i.1, ∃ j ∈ C', x ∈ i.2.1.get j) ∧
    ∑ j ∈ C', (i.2.1.get j).length ≤ i.2.2

open Classical in
/-- MINIMUM EXACT COVER as a decision problem over bitstrings. -/
noncomputable def minimumExactCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumExactCoverInstance) x with
  | some i => decide (WellFormed i ∧ MinimumExactCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumExactCover
