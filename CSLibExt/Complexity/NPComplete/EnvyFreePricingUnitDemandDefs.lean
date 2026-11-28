/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENVY-FREE PRICING for unit-demand consumers with unlimited supply: definitions

Source:
V. Guruswami, J. D. Hartline, A. R. Karlin, D. Kempe, C. Kenyon and F. McSherry, "On
profit-maximizing envy-free pricing", Proceedings of the Sixteenth Annual ACM-SIAM Symposium on
Discrete Algorithms (SODA 2005), 1164-1173, doi:10.5555/1070432.1070598 (Section 2,
Definitions 2.1 and 2.2; Section 1: the problems are "not only NP-complete, but APX-hard";
Theorem 3.1: the unit-demand problem is APX-hard even with unlimited supply, by a reduction from
VERTEX COVER).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnvyFreePricingUnitDemand

/-- An instance: the number `m` of items, the valuations (for each consumer the list
`[vᵢ(0), …, vᵢ(m - 1)]`), and the revenue bound `R`. -/
abbrev EnvyFreePricingInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every consumer values each of the `m` items. -/
def WellFormed (i : EnvyFreePricingInstance) : Prop :=
  ∀ v ∈ i.2.1, v.length = i.1

/-- The utility `v(j) - pⱼ` of item `j` to a consumer with valuations `v` under prices `p`. -/
def utility {m : ℕ} (v : List ℕ) (p : Fin m → ℕ) (j : Fin m) : ℤ :=
  (v.getD j 0 : ℤ) - p j

/-- The option `x` (`none`: no purchase, utility `0`; `some j`: item `j`) is in the demand set
of a consumer with valuations `v` under prices `p`: no option has larger utility. -/
def InDemandSet {m : ℕ} (v : List ℕ) (p : Fin m → ℕ) : Option (Fin m) → Prop
  | none => ∀ j', utility v p j' ≤ 0
  | some j => 0 ≤ utility v p j ∧ ∀ j', utility v p j' ≤ utility v p j

/-- Some prices and envy-free allocation give the seller a profit of at least `R`. -/
def EnvyFreePricingFeasible (i : EnvyFreePricingInstance) : Prop :=
  ∃ p : Fin i.1 → ℕ, ∃ a : Fin i.2.1.length → Option (Fin i.1),
    (∀ c, InDemandSet (i.2.1.get c) p (a c)) ∧ i.2.2 ≤ ∑ c, (a c).elim 0 p

open Classical in
/-- ENVY-FREE PRICING for unit-demand consumers with unlimited supply as a decision problem over
bitstrings. -/
noncomputable def envyFreePricingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnvyFreePricingInstance) x with
  | some i => decide (WellFormed i ∧ EnvyFreePricingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EnvyFreePricingUnitDemand
