/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRUNED TRIE SPACE MINIMIZATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR3] PRUNED TRIE SPACE MINIMIZATION, p. 226
(reference [Comer and Sethi, 1976]; transformation from 3DM);
D. Comer and R. Sethi, "The complexity of trie index construction", Journal of the ACM 24
(1977), 428-440, doi:10.1145/322017.322023 (Theorem 3(a)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrunedTrieSpaceMinimization

/-- An instance: the number `s` of elements of `S` (`S = Fin s`), the collection `F` (each
function as the list of its values `[f(0), …, f(s - 1)]`), and the bound `K`. -/
abbrev PrunedTrieSpaceMinimizationInstance := ℕ × List (List ℕ) × ℕ

/-- The value `f(a)` of a function given by its list of values. -/
def value (f : List ℕ) (a : ℕ) : ℕ := f.getD a 0

/-- The `i`-tuple `(f₁(a), …, fᵢ(a))` of the sequence `fs = ⟨f₁, …, f_m⟩`, for `i ≤ m`. -/
def prefixTuple (fs : List (List ℕ)) (i a : ℕ) : List ℕ :=
  (fs.take i).map fun f => value f a

/-- The sequence `fs` distinguishes every two distinct elements of `S = Fin s`: some function of
`fs` takes different values on them. -/
def Distinguishes (s : ℕ) (fs : List (List ℕ)) : Prop :=
  ∀ a b : Fin s, a ≠ b → ∃ f ∈ fs, value f a ≠ value f b

/-- `N(i)`: the number of distinct `i`-tuples `X` for which more than one `a ∈ S = Fin s` has
`(f₁(a), …, fᵢ(a)) = X`. -/
def numShared (s : ℕ) (fs : List (List ℕ)) (i : ℕ) : ℕ :=
  ((Finset.univ.image fun a : Fin s => prefixTuple fs i a).filter fun X =>
    1 < (Finset.univ.filter fun a : Fin s => prefixTuple fs i a = X).card).card

/-- Well-formedness of an instance: `F` has no repeated function, every member of `F` is a
function `S → ℤ⁺` (a list of `s` positive values), and `K` is positive. -/
def WellFormed (i : PrunedTrieSpaceMinimizationInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ f ∈ i.2.1, f.length = i.1 ∧ ∀ v ∈ f, 0 < v) ∧ 0 < i.2.2

/-- Some sequence of distinct functions from `F` distinguishes every two elements of `S` and has
`∑_{i=1}^{m} N(i) ≤ K`. -/
def PrunedTrieSpaceMinimizationFeasible (i : PrunedTrieSpaceMinimizationInstance) : Prop :=
  ∃ fs : List (List ℕ), fs.Nodup ∧ (∀ f ∈ fs, f ∈ i.2.1) ∧ Distinguishes i.1 fs ∧
    ∑ j ∈ Finset.Icc 1 fs.length, numShared i.1 fs j ≤ i.2.2

open Classical in
/-- PRUNED TRIE SPACE MINIMIZATION as a decision problem over bitstrings. -/
noncomputable def prunedTrieSpaceMinimizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrunedTrieSpaceMinimizationInstance) x with
  | some i => decide (WellFormed i ∧ PrunedTrieSpaceMinimizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrunedTrieSpaceMinimization
