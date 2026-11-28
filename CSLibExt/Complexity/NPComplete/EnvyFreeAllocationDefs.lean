/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENVY-FREE ALLOCATION OF INDIVISIBLE GOODS: definitions

Source:
R. J. Lipton, E. Markakis, E. Mossel, and A. Saberi, "On approximately fair allocations of
indivisible goods", Proceedings of the 5th ACM Conference on Electronic Commerce (EC 2004),
125-131, doi:10.1145/988772.988792, Section 3.1.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnvyFreeAllocation

/-- An instance: the number of goods `m` and the utility matrix `V`, one row of `m` values per
player. -/
abbrev EnvyFreeAllocationInstance := ℕ × List (List ℕ)

/-- The utility `v_{p,g}` of good `g` for player `p`. -/
def utility (i : EnvyFreeAllocationInstance) (p : Fin i.2.length) (g : Fin i.1) : ℕ :=
  (i.2.get p).getD g 0

/-- Player `p`'s additive utility `v_p(A_q)` for the bundle `A_q = A⁻¹(q)` of player `q`. -/
def bundleUtility (i : EnvyFreeAllocationInstance) (A : Fin i.1 → Fin i.2.length)
    (p q : Fin i.2.length) : ℕ :=
  ∑ g ∈ Finset.univ.filter (fun g => A g = q), utility i p g

/-- Well-formedness of an instance: every row of `V` lists one utility per good. -/
def WellFormed (i : EnvyFreeAllocationInstance) : Prop :=
  ∀ row ∈ i.2, row.length = i.1

/-- Some allocation of all goods is envy-free: no player values another player's bundle more
than her own. -/
def EnvyFreeAllocationFeasible (i : EnvyFreeAllocationInstance) : Prop :=
  ∃ A : Fin i.1 → Fin i.2.length, ∀ p q, bundleUtility i A p q ≤ bundleUtility i A p p

open Classical in
/-- ENVY-FREE ALLOCATION OF INDIVISIBLE GOODS as a decision problem over bitstrings. -/
noncomputable def envyFreeAllocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnvyFreeAllocationInstance) x with
  | some i => decide (WellFormed i ∧ EnvyFreeAllocationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EnvyFreeAllocation
