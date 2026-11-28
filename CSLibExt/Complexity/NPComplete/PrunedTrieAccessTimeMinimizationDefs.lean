/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRUNED TRIE ACCESS TIME MINIMIZATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR3] PRUNED TRIE SPACE MINIMIZATION, p. 226,
comment: the related "access time minimization" problem is also NP-complete for pruned tries
(the entry's reference is [Comer and Sethi, 1976]);
D. Comer and R. Sethi, "The complexity of trie index construction", Journal of the ACM 24
(1977), 428-440, doi:10.1145/322017.322023 (Problem 3, least access time pruned trie;
Theorem 1 and Appendix C).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrunedTrieSpaceMinimizationDefs
public import Mathlib.Order.Bounds.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrunedTrieAccessTimeMinimization

open PrunedTrieSpaceMinimization

/-- `L(a) = l`: `l` is the least `i` for which no other `b ∈ S = Fin s` has the same `i`-tuple
`(f₁(b), …, fᵢ(b))` as `a`. -/
def IsAccessTime (s : ℕ) (fs : List (List ℕ)) (a : Fin s) (l : ℕ) : Prop :=
  IsLeast {i : ℕ | ∀ b : Fin s, b ≠ a → prefixTuple fs i b ≠ prefixTuple fs i a} l

/-- Some sequence of functions from `F` distinguishes every two elements of `S` and has
`∑_{a ∈ S} L(a) ≤ K`. -/
def PrunedTrieAccessTimeMinimizationFeasible (i : PrunedTrieSpaceMinimizationInstance) :
    Prop :=
  ∃ fs : List (List ℕ), (∀ f ∈ fs, f ∈ i.2.1) ∧ Distinguishes i.1 fs ∧
    ∃ L : Fin i.1 → ℕ, (∀ a, IsAccessTime i.1 fs a (L a)) ∧ ∑ a, L a ≤ i.2.2

open Classical in
/-- PRUNED TRIE ACCESS TIME MINIMIZATION as a decision problem over bitstrings. -/
noncomputable def prunedTrieAccessTimeMinimizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrunedTrieSpaceMinimizationInstance) x with
  | some i => decide (WellFormed i ∧ PrunedTrieAccessTimeMinimizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrunedTrieAccessTimeMinimization
