/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIDE-CHAIN POSITIONING (PROTEIN DESIGN): definitions

Source:
N. A. Pierce and E. Winfree, "Protein design is NP-hard", Protein Engineering 15 (2002),
779-782, doi:10.1093/protein/15.10.779;
B. Chazelle, C. Kingsford and M. Singh, "A semidefinite programming approach to side chain
positioning with new rounding strategies", INFORMS Journal on Computing 16 (2004), 380-392,
doi:10.1287/ijoc.1040.0096.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SideChainPositioning

/-- An instance: the number `p` of positions, the position of each rotamer, the self energies,
the pairwise energy matrix (rows and columns indexed by rotamers), and the bound `K`. -/
abbrev SideChainPositioningInstance :=
  ℕ × List ℕ × List (ℕ × ℕ) × List (List (ℕ × ℕ)) × (ℕ × ℕ)

/-- The integer `a - b` encoded by the pair `(a, b)`. -/
def intOf (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - (z.2 : ℤ)

/-- Well-formedness of an instance: every rotamer is at one of the positions `0, …, p - 1`,
every position has at least one rotamer, there is one self energy per rotamer, and the pairwise
energies form an `R × R` matrix. -/
def WellFormed (i : SideChainPositioningInstance) : Prop :=
  (∀ j ∈ i.2.1, j < i.1) ∧ (∀ j < i.1, j ∈ i.2.1) ∧
    i.2.2.1.length = i.2.1.length ∧ i.2.2.2.1.length = i.2.1.length ∧
    ∀ row ∈ i.2.2.2.1, row.length = i.2.1.length

/-- The self energy `E(r)` of rotamer `r`. -/
def selfEnergy (i : SideChainPositioningInstance) (r : ℕ) : ℤ :=
  intOf (i.2.2.1.getD r (0, 0))

/-- The pairwise energy `E(r, s)` of rotamers `r` and `s`. -/
def pairEnergy (i : SideChainPositioningInstance) (r s : ℕ) : ℤ :=
  intOf ((i.2.2.2.1.getD r []).getD s (0, 0))

/-- The total energy `∑ᵢ E(rᵢ) + ∑ᵢ ∑_{j < i} E(rᵢ, rⱼ)` of the choice `c` of rotamers. -/
def totalEnergy (i : SideChainPositioningInstance) (c : Fin i.1 → ℕ) : ℤ :=
  ∑ a, selfEnergy i (c a) + ∑ a, ∑ b ∈ Finset.Iio a, pairEnergy i (c a) (c b)

/-- There is a choice of one rotamer at each position with total energy at most `K`. -/
def SideChainPositioningFeasible (i : SideChainPositioningInstance) : Prop :=
  ∃ c : Fin i.1 → ℕ, (∀ a, c a < i.2.1.length ∧ i.2.1.getD (c a) 0 = a) ∧
    totalEnergy i c ≤ intOf i.2.2.2.2

open Classical in
/-- SIDE-CHAIN POSITIONING as a decision problem over bitstrings. -/
noncomputable def sideChainPositioningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SideChainPositioningInstance) x with
  | some i => decide (WellFormed i ∧ SideChainPositioningFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SideChainPositioning
