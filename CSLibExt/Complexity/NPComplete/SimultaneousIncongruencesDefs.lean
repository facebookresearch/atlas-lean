/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMULTANEOUS INCONGRUENCES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN2] SIMULTANEOUS
INCONGRUENCES;
L. J. Stockmeyer and A. R. Meyer, "Word problems requiring exponential time
(preliminary report)", Proceedings of the 5th Annual ACM Symposium on Theory of
Computing (STOC 1973), 1-9, doi:10.1145/800125.804029.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousIncongruences

/-- An instance: the list of pairs `(aᵢ, bᵢ)`. -/
abbrev SimultaneousIncongruencesInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every pair `(aᵢ, bᵢ)` consists of positive integers with
`aᵢ ≤ bᵢ` (so `bᵢ` is positive as well). -/
def WellFormed (i : SimultaneousIncongruencesInstance) : Prop :=
  ∀ p ∈ i, 0 < p.1 ∧ p.1 ≤ p.2

/-- Some integer `x` satisfies `x ≢ aᵢ (mod bᵢ)` for every pair `(aᵢ, bᵢ)`. -/
def SimultaneousIncongruencesFeasible (i : SimultaneousIncongruencesInstance) : Prop :=
  ∃ x : ℤ, ∀ p ∈ i, ¬ x ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)]

open Classical in
/-- SIMULTANEOUS INCONGRUENCES as a decision problem over bitstrings. -/
noncomputable def simultaneousIncongruencesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimultaneousIncongruencesInstance) x with
  | some i => decide (WellFormed i ∧ SimultaneousIncongruencesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimultaneousIncongruences
