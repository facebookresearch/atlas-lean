/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HYPERPLANE CONSISTENCY: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM HYPERPLANE CONSISTENCY;
E. Amaldi and V. Kann, "The complexity and approximability of finding maximum feasible
subsystems of linear relations", Theoretical Computer Science 147 (1995), 181-210,
doi:10.1016/0304-3975(94)00254-G;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP6] OPEN HEMISPHERE;
D. S. Johnson and F. P. Preparata, "The densest hemisphere problem", Theoretical Computer
Science 6 (1978), 93-107, doi:10.1016/0304-3975(78)90006-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HyperplaneConsistency

/-- An instance: the dimension `n`, the list `P` of positive examples and the list `N` of
negative examples (vectors of encoded integers), and the bound `K`. -/
abbrev HyperplaneConsistencyInstance :=
  ℕ × List (List (ℕ × ℕ)) × List (List (ℕ × ℕ)) × ℕ

/-- The integer `p.1 - p.2` encoded by a pair of naturals. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The inner product `w · x` of a rational vector `w` with an encoded integer vector `x`. -/
def dot {n : ℕ} (w : Fin n → ℚ) (x : List (ℕ × ℕ)) : ℚ :=
  ∑ j : Fin n, (intOf (x.getD j (0, 0)) : ℚ) * w j

/-- Well-formedness of an instance: `0 < n`, every example is an `n`-vector, the decoded vectors
of `P` are pairwise distinct and so are those of `N` (`P` and `N` are sets), and
`0 < K ≤ |P| + |N|`. -/
def WellFormed (i : HyperplaneConsistencyInstance) : Prop :=
  0 < i.1 ∧ (∀ x ∈ i.2.1, x.length = i.1) ∧ (∀ x ∈ i.2.2.1, x.length = i.1) ∧
    (i.2.1.map fun x => x.map intOf).Nodup ∧ (i.2.2.1.map fun x => x.map intOf).Nodup ∧
    0 < i.2.2.2 ∧ i.2.2.2 ≤ i.2.1.length + i.2.2.1.length

/-- A hyperplane `(w, w₀)`, `w ≠ 0`, with `w · x > w₀` for positive examples and `w · x < w₀` for
negative examples, for at least `K` examples in total. -/
def HyperplaneConsistencyFeasible (i : HyperplaneConsistencyInstance) : Prop :=
  ∃ (w : Fin i.1 → ℚ) (w₀ : ℚ), w ≠ 0 ∧ i.2.2.2 ≤
    (i.2.1.filter fun x => w₀ < dot w x).length + (i.2.2.1.filter fun x => dot w x < w₀).length

open Classical in
/-- HYPERPLANE CONSISTENCY as a decision problem over bitstrings. -/
noncomputable def hyperplaneConsistencyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HyperplaneConsistencyInstance) x with
  | some i => decide (WellFormed i ∧ HyperplaneConsistencyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HyperplaneConsistency
