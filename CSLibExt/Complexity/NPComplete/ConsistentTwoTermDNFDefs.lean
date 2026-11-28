/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENT 2-TERM DNF: definitions

Source:
L. Pitt and L. G. Valiant, "Computational limitations on learning from examples", Journal of
the ACM 35(4) (1988), 965-984, doi:10.1145/48014.63140 (disjunctions of two monomials, i.e.
2-term DNF, cannot be learned by 2-term DNF hypotheses unless RP = NP; the reduction shows that
deciding whether some 2-term DNF is consistent with given examples is NP-complete);
S. Ghoshal and R. Saket, "Hardness of learning DNFs using halfspaces", arXiv:1911.06358
(Section 1: "it is NP-hard to properly learn a t-term DNF [PV88], for any t ≥ 2").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.KeyTheorems.KarpLubyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistentTwoTermDNF

open MetaMathlibExt.Complexity.KeyTheorems.KarpLuby (dnfSat)

/-- An instance: the number `n` of variables, the positive examples, and the negative
examples. -/
abbrev ConsistentTwoTermDNFInstance := ℕ × List (List Bool) × List (List Bool)

/-- An example vector as an assignment of the variables (`x_k` is entry `k`). -/
def assignment (x : List Bool) : ℕ → Bool :=
  fun k => x.getD k false

/-- Well-formedness of an instance: every example is a vector of length `n`. -/
def WellFormed (i : ConsistentTwoTermDNFInstance) : Prop :=
  ∀ x ∈ i.2.1 ++ i.2.2, x.length = i.1

/-- Some DNF formula with at most two terms, over the variables `x₀, …, x_{n-1}`, is true on
every positive example and false on every negative example. -/
def ConsistentTwoTermDNFFeasible (i : ConsistentTwoTermDNFInstance) : Prop :=
  ∃ φ : List (List (ℕ × Bool)), φ.length ≤ 2 ∧ (∀ t ∈ φ, ∀ l ∈ t, l.1 < i.1) ∧
    (∀ x ∈ i.2.1, dnfSat (assignment x) φ) ∧ ∀ x ∈ i.2.2, ¬ dnfSat (assignment x) φ

open Classical in
/-- CONSISTENT 2-TERM DNF as a decision problem over bitstrings. -/
noncomputable def consistentTwoTermDNFDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsistentTwoTermDNFInstance) x with
  | some i => decide (WellFormed i ∧ ConsistentTwoTermDNFFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsistentTwoTermDNF
