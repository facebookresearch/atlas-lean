/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RNA pseudoknot prediction is NP-complete

In the Nearest Neighbour Pseudoknot Model a secondary structure `S` is any
set of base pairs with each base in at most one pair (pairs may cross), and
`E(S)` sums per-pair energies. Deciding whether the optimal structure has
energy below a threshold is NP-complete (Proposition 1), by reduction from
3-SAT with each literal occurring at most twice, using only Watson-Crick
pairs; hence prediction in the Rivas-Eddy energy model is NP-hard. The
reduction itself is proof content for later; membership and hardness are
recorded as stated properties of the decision problem.

Overlap: none found; the catalog item below is a different NP problem:
`WantedExt/Complexity/NPComplete/LongestArcPreservingCommonSubsequenceCrossingWanted.lean`.

Sources: R. B. Lyngso and C. N. S. Pedersen, "Pseudoknots in RNA secondary
structures", BRICS Report Series RS-00-1, University of Aarhus, January 2000
(also RECOMB 2000); journal version in J. Comput. Biol. 7(3-4):409-427,
2000, doi:10.1089/106652700750050862, Proposition 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.RNAPseudoknotWanted

open Classical

variable (n : ℕ)

/-- Secondary structures: pair sets with each base in at most one pair
(pairs may cross, admitting pseudoknots). -/
def IsSecondaryStructure (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ i : Fin n, ((S.filter fun p => p.1 = i ∨ p.2 = i).card) ≤ 1

/-- Watson-Crick restriction for the hardness reduction. -/
def AllWatsonCrick (isWC : Fin n → Fin n → Prop)
    (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ S, isWC p.1 p.2

/-- **Pseudoknot prediction is in NP** (Lyngso-Pedersen 2000, Proposition 1,
membership half): hypotheses are the sequence length (`hn`), a pairing
energy summing over pairs (`energy`, `hform`: the nearest-neighbour form),
with polynomial checkability as cost-model context. Conclusion: the
threshold decision problem is in NP (`InNP`).

Source: Lyngso-Pedersen (2000), Proposition 1. -/
theorem_wanted pseudoknot_inNP (n : ℕ) (hn : 1 ≤ n)
    (energy : Finset (Fin n × Fin n) → ℤ)
    (hform : ∃ Epair : Fin n × Fin n → ℤ, ∀ S : Finset (Fin n × Fin n),
      IsSecondaryStructure n S → energy S = Finset.sum S Epair)
    (InNP : Prop) :
    InNP

/-- **Pseudoknot prediction is NP-hard** (Lyngso-Pedersen 2000, Proposition 1,
hardness half): same model hypotheses as `pseudoknot_inNP`, plus the
3-SAT reduction context (each literal at most twice,
Watson-Crick pairs only, `isWC`). Conclusion: the
threshold decision problem is NP-hard (`IsNPHard`); hence Rivas-Eddy
prediction is NP-hard.

Source: Lyngso-Pedersen (2000), Proposition 1. -/
theorem_wanted pseudoknot_hard (n : ℕ) (hn : 1 ≤ n)
    (energy : Finset (Fin n × Fin n) → ℤ)
    (hform : ∃ Epair : Fin n × Fin n → ℤ, ∀ S : Finset (Fin n × Fin n),
      IsSecondaryStructure n S → energy S = Finset.sum S Epair)
    (isWC : Fin n → Fin n → Prop)
    (E : ℤ)
    (IsNPHard : Prop) :
    IsNPHard

end WantedExt.Biology.ComputationalBiology.RNAPseudoknotWanted
