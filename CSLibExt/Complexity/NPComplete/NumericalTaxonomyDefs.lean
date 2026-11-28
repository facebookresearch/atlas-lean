/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMERICAL TAXONOMY: definitions

Source:
R. Agarwala, V. Bafna, M. Farach, M. Paterson and M. Thorup, "On the approximability of
numerical taxonomy (fitting distances by tree metrics)", SIAM Journal on Computing 28 (1999),
1073-1085, doi:10.1137/S0097539795296334, Section 5, Theorem 5.1 (also University of Warwick
Department of Computer Science Research Report CS-RR-330, 1997).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.TreeMetric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NumericalTaxonomy

open MathlibExt.Biology.Phylogenetics.Buneman (IsTreeMetric)

/-- An instance: the rows of the `n × n` distance matrix `D`, each entry a nonnegative rational
`(numerator, denominator)`, and the threshold `Δ` in the same form. -/
abbrev NumericalTaxonomyInstance := List (List (ℕ × ℕ)) × (ℕ × ℕ)

/-- The rational number `p.1 / p.2` as a real number. -/
noncomputable def ratValue (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) / p.2

/-- The pair `(numerator, denominator)` of the entry `D[a, b]`. -/
def cell (i : NumericalTaxonomyInstance) (a b : ℕ) : ℕ × ℕ :=
  (i.1.getD a []).getD b (0, 1)

/-- The entry `D[a, b]` of the distance matrix. -/
noncomputable def entry (i : NumericalTaxonomyInstance) (a b : ℕ) : ℝ :=
  ratValue (cell i a b)

/-- Well-formedness of an instance: `D` is a square matrix, every entry of `D` and the threshold
have a positive denominator, `D` is symmetric (`D[a, b] = D[b, a]` as rationals) and its diagonal
is zero. -/
def WellFormed (i : NumericalTaxonomyInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length ∧ ∀ e ∈ row, 0 < e.2) ∧ 0 < i.2.2 ∧
    (∀ a < i.1.length, ∀ b < i.1.length,
      (cell i a b).1 * (cell i b a).2 = (cell i b a).1 * (cell i a b).2) ∧
    ∀ a < i.1.length, (cell i a a).1 = 0

/-- Some tree metric `T` on the points, with distinct points at positive distance, satisfies
`|T[a, b] - D[a, b]| ≤ Δ` for all points `a < b`. -/
def NumericalTaxonomyFeasible (i : NumericalTaxonomyInstance) : Prop :=
  ∃ T : Fin i.1.length → Fin i.1.length → ℝ, IsTreeMetric T ∧ (∀ a b, a ≠ b → 0 < T a b) ∧
    ∀ a b : Fin i.1.length, a < b → |T a b - entry i a b| ≤ ratValue i.2

open Classical in
/-- NUMERICAL TAXONOMY as a decision problem over bitstrings. -/
noncomputable def numericalTaxonomyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NumericalTaxonomyInstance) x with
  | some i => decide (WellFormed i ∧ NumericalTaxonomyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NumericalTaxonomy
