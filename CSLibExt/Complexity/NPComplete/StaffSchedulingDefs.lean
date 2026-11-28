/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STAFF SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS20] STAFF SCHEDULING
(reference: [Garey and Johnson, ----], unpublished; transformation from X3C), p. 243;
J. J. Bartholdi, J. B. Orlin and H. D. Ratliff, "Cyclic scheduling via integer programs with
circular ones", Operations Research 28 (1980), 1074-1085, doi:10.1287/opre.28.5.1074 (the
polynomial case of the comment).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StaffScheduling

/-- An instance: `m`, `k`, the tuples of `C` (lists of Booleans), the requirement tuple `R`,
and the number `n` of workers. -/
abbrev StaffSchedulingInstance := ℕ × ℕ × List (List Bool) × List ℕ × ℕ

/-- Well-formedness of an instance: `m` and `k` are positive, `k ≤ m` (an `m`-tuple has `k` 1's
and `m - k` 0's), every tuple of `C` has length `m` and exactly `k` entries `true`, and `R` has
length `m`. -/
def WellFormed (i : StaffSchedulingInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ i.2.1 ≤ i.1 ∧
    (∀ c ∈ i.2.2.1, c.length = i.1 ∧ c.count true = i.2.1) ∧ i.2.2.2.1.length = i.1

/-- Some `f` assigns at most `n` workers in total to the tuples of `C`, and for every position
`j < m` the tuples with a 1 at `j` get at least `R_j` workers. -/
def StaffSchedulingFeasible (i : StaffSchedulingInstance) : Prop :=
  ∃ f : Fin i.2.2.1.length → ℕ, (∑ c, f c) ≤ i.2.2.2.2 ∧
    ∀ j < i.1, i.2.2.2.1.getD j 0 ≤
      ∑ c, f c * (if (i.2.2.1.get c).getD j false then 1 else 0)

open Classical in
/-- STAFF SCHEDULING as a decision problem over bitstrings. -/
noncomputable def staffSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StaffSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ StaffSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StaffScheduling
