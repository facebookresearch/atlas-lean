/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENT FAULT SET: definitions

Source:
H. Fujiwara and K. Kinoshita, "On the computational complexity of system diagnosis", IEEE
Transactions on Computers C-27 (1978), 881-885, doi:10.1109/TC.1978.1674966, Problem 1 (P1)
and Theorem 1, recording the result of S. N. Maheshwari and S. L. Hakimi, "On models for
diagnosable systems and probabilistic fault diagnosis", IEEE Transactions on Computers C-25
(1976), 228-236, doi:10.1109/TC.1976.5009249.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistentFaultSet

/-- An instance: the number `n` of units, the tests `((u_i, u_j), a_ij)` (unit `u_i` tests unit
`u_j` with outcome `a_ij`, `true` for `1`), and the bound `t`. -/
abbrev ConsistentFaultSetInstance := ℕ × List ((ℕ × ℕ) × Bool) × ℕ

/-- Well-formedness of an instance: every test names two different units, no arc is listed
twice, and `t` is positive. -/
def WellFormed (i : ConsistentFaultSetInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.1 < i.1 ∧ e.1.2 < i.1 ∧ e.1.1 ≠ e.1.2) ∧ (i.2.1.map Prod.fst).Nodup ∧
    0 < i.2.2

/-- Some set `F` of at most `t` units is a consistent fault set: for every test
`((u_i, u_j), a_ij)` with `u_i ∉ F`, (1) `a_ij = 1` if `u_j ∈ F` and (2) `a_ij = 0` if
`u_j ∉ F`. -/
def ConsistentFaultSetFeasible (i : ConsistentFaultSetInstance) : Prop :=
  ∃ F : Finset (Fin i.1), F.card ≤ i.2.2 ∧
    ∀ e ∈ i.2.1, ∀ (h1 : e.1.1 < i.1) (h2 : e.1.2 < i.1), (⟨e.1.1, h1⟩ : Fin i.1) ∉ F →
      ((⟨e.1.2, h2⟩ : Fin i.1) ∈ F → e.2 = true) ∧ ((⟨e.1.2, h2⟩ : Fin i.1) ∉ F → e.2 = false)

open Classical in
/-- CONSISTENT FAULT SET as a decision problem over bitstrings. -/
noncomputable def consistentFaultSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsistentFaultSetInstance) x with
  | some i => decide (WellFormed i ∧ ConsistentFaultSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsistentFaultSet
