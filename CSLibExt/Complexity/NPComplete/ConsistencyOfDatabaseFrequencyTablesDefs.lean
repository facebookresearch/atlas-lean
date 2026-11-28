/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENCY OF DATABASE FREQUENCY TABLES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR35] CONSISTENCY OF DATABASE
FREQUENCY TABLES, p. 235, credited there to [Reiss, 1977b]: S. P. Reiss, "Statistical
database confidentiality", Report No. 25, Department of Statistics, University of Stockholm
(1977), transformation from 3SAT (the report was not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistencyOfDatabaseFrequencyTables

/-- An instance: the number `|V|` of objects in unary (a list of length `|V|`), the list of
domain sizes `d_a` (one per attribute), the frequency tables `((a, b), rows)`, and the known
values `(v, a, x)`. -/
abbrev FrequencyTablesInstance :=
  List Bool × List ℕ × List ((ℕ × ℕ) × List (List ℕ)) × List (ℕ × ℕ × ℕ)

/-- The size `d_a` of the domain of attribute `a`. -/
def domSize (i : FrequencyTablesInstance) (a : ℕ) : ℕ :=
  i.2.1.getD a 0

/-- The entry `f_{a,b}(x, y)` of a frequency table with rows `rows`. -/
def entry (rows : List (List ℕ)) (x y : ℕ) : ℕ :=
  (rows.getD x []).getD y 0

/-- Well-formedness of an instance: `|V|` is written in unary as `[true, …, true]`; every
table is indexed by a pair of attributes, has `d_a` rows of length `d_b`, and has positive
entries summing to `|V|`; the pairs of the tables are distinct; and every known value
`(v, a, x)` has `v ∈ V`, `a ∈ A` and `x ∈ D_a`. -/
def WellFormed (i : FrequencyTablesInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧
    (∀ t ∈ i.2.2.1, t.1.1 < i.2.1.length ∧ t.1.2 < i.2.1.length ∧
      t.2.length = domSize i t.1.1 ∧
      (∀ row ∈ t.2, row.length = domSize i t.1.2 ∧ ∀ e ∈ row, 0 < e) ∧
      (t.2.map List.sum).sum = i.1.length) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧
    ∀ k ∈ i.2.2.2, k.1 < i.1.length ∧ k.2.1 < i.2.1.length ∧ k.2.2 < domSize i k.2.1

/-- Some functions `g_a : V → D_a` agree with every known value and realize every frequency
table exactly. -/
def FrequencyTablesFeasible (i : FrequencyTablesInstance) : Prop :=
  ∃ g : ℕ → ℕ → ℕ, (∀ a < i.2.1.length, ∀ v < i.1.length, g a v < domSize i a) ∧
    (∀ k ∈ i.2.2.2, g k.2.1 k.1 = k.2.2) ∧
    ∀ t ∈ i.2.2.1, ∀ x < domSize i t.1.1, ∀ y < domSize i t.1.2,
      ((Finset.range i.1.length).filter fun v => g t.1.1 v = x ∧ g t.1.2 v = y).card =
        entry t.2 x y

open Classical in
/-- CONSISTENCY OF DATABASE FREQUENCY TABLES as a decision problem over bitstrings. -/
noncomputable def frequencyTablesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FrequencyTablesInstance) x with
  | some i => decide (WellFormed i ∧ FrequencyTablesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsistencyOfDatabaseFrequencyTables
