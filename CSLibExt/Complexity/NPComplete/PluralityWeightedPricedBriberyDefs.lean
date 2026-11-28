/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY-WEIGHTED-$BRIBERY: definitions

Source:
P. Faliszewski, E. Hemaspaandra and L. A. Hemaspaandra, "How hard is bribery in elections?",
Journal of Artificial Intelligence Research 35 (2009), 485-532, doi:10.1613/jair.2676
(arXiv:cs/0608081), Section 2.2 (the problem plurality-weighted-$bribery, nonunique-winner model)
and Theorem 3.2 (it is NP-complete, even for two candidates).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityWeightedPricedBribery

/-- An instance: the number of candidates `m`, the distinguished candidate `p`, the voters
`(prefs, weight, price)`, and the budget `k`. -/
abbrev PluralityWeightedPricedBriberyInstance := ℕ × ℕ × List (List ℕ × ℕ × ℕ) × ℕ

/-- The voters of the instance, `Fin n` for `n` listed voters. -/
abbrev Voter (i : PluralityWeightedPricedBriberyInstance) : Type := Fin i.2.2.1.length

/-- The weighted plurality score of candidate `a` when voter `v` casts the preference list
`P v`: the total weight of the voters ranking `a` first. -/
def weightedScore (i : PluralityWeightedPricedBriberyInstance) (P : Voter i → List ℕ) (a : ℕ) :
    ℕ :=
  ∑ v, if (P v).head? = some a then (i.2.2.1.get v).2.1 else 0

/-- Well-formedness of an instance: `p` is a candidate, and every voter's preference list
contains every candidate exactly once. -/
def WellFormed (i : PluralityWeightedPricedBriberyInstance) : Prop :=
  i.2.1 < i.1 ∧ ∀ v ∈ i.2.2.1, v.1.Perm (List.range i.1)

/-- Some set `B` of voters of total price at most `k` can be bribed to cast preference lists
`P` (arbitrary for `B`, unchanged outside `B`) under which `p` has maximum weighted plurality
score. -/
def PluralityWeightedPricedBriberyFeasible (i : PluralityWeightedPricedBriberyInstance) : Prop :=
  ∃ B : Finset (Voter i), ∑ v ∈ B, (i.2.2.1.get v).2.2 ≤ i.2.2.2 ∧
    ∃ P : Voter i → List ℕ, (∀ v, (P v).Perm (List.range i.1)) ∧
      (∀ v, v ∉ B → P v = (i.2.2.1.get v).1) ∧
      ∀ a < i.1, weightedScore i P a ≤ weightedScore i P i.2.1

open Classical in
/-- PLURALITY-WEIGHTED-$BRIBERY as a decision problem over bitstrings. -/
noncomputable def pluralityWeightedPricedBriberyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PluralityWeightedPricedBriberyInstance) x with
  | some i => decide (WellFormed i ∧ PluralityWeightedPricedBriberyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PluralityWeightedPricedBribery
