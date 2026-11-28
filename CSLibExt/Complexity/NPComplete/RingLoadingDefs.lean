/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RING LOADING: definitions

Source:
A. Schrijver, P. Seymour and P. Winkler, "The ring loading problem", SIAM J. Discrete Math. 11
(1998), 1-14, doi:10.1137/S0895480195294994, Sections 2-3 (the decision form and its
NP-completeness, by a reduction from PARTITION);
S. Cosares and I. Saniee, "An optimization problem related to balancing loads on SONET rings",
Telecommunication Systems 3 (1994), 165-181, doi:10.1007/BF02110141 (the first NP-hardness
proof, for a formulation that allows several demands per node pair);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM RING LOADING.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RingLoading

/-- An instance: the demand table (row `i` is `[d_{i,i+1}, …, d_{i,n-1}]`, so the ring size `n`
is the number of rows) and the target `K`. -/
abbrev RingLoadingInstance := List (List ℕ) × ℕ

/-- The ring size `n`: the number of rows of the demand table. -/
def size (i : RingLoadingInstance) : ℕ := i.1.length

/-- The demand `d_{a,b}` between nodes `a < b`: entry `b - a - 1` of row `a`. -/
def demand (i : RingLoadingInstance) (a b : ℕ) : ℕ :=
  (i.1.getD a []).getD (b - a - 1) 0

/-- Well-formedness of an instance: the ring size `n` is positive, row `a` of the demand table
has exactly `n - a - 1` entries, one for each node `b` with `a < b < n`, and `K` is positive. -/
def WellFormed (i : RingLoadingInstance) : Prop :=
  0 < size i ∧ (∀ a < size i, (i.1.getD a []).length = size i - a - 1) ∧ 0 < i.2

/-- The load `L_k` of link `k` under the routing `Φ`: the demands `d_{a,b}` (`a < b`) routed
with `Φ a b = true` and `a ≤ k < b`, plus those routed with `Φ a b = false` and
`¬(a ≤ k < b)`. -/
def load (i : RingLoadingInstance) (Φ : Fin (size i) → Fin (size i) → Bool)
    (k : Fin (size i)) : ℕ :=
  ((Finset.univ : Finset (Fin (size i) × Fin (size i))).filter fun p =>
      p.1 < p.2 ∧ Φ p.1 p.2 = true ∧ (p.1 ≤ k ∧ k < p.2)).sum
      (fun p => demand i p.1 p.2) +
    ((Finset.univ : Finset (Fin (size i) × Fin (size i))).filter fun p =>
      p.1 < p.2 ∧ Φ p.1 p.2 = false ∧ ¬(p.1 ≤ k ∧ k < p.2)).sum
      (fun p => demand i p.1 p.2)

/-- Some routing puts a load of at most `K` on every link. -/
def RingLoadingFeasible (i : RingLoadingInstance) : Prop :=
  ∃ Φ : Fin (size i) → Fin (size i) → Bool, ∀ k, load i Φ k ≤ i.2

open Classical in
/-- RING LOADING as a decision problem over bitstrings. -/
noncomputable def ringLoadingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RingLoadingInstance) x with
  | some i => decide (WellFormed i ∧ RingLoadingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RingLoading
