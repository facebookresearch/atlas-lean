/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENCY OF DATABASE FREQUENCY TABLES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR35] CONSISTENCY OF DATABASE
FREQUENCY TABLES, p. 235, credited there to [Reiss, 1977b]: S. P. Reiss, "Statistical
database confidentiality", Report No. 25, Department of Statistics, University of Stockholm
(1977), transformation from 3SAT (the report was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistencyOfDatabaseFrequencyTables

/-!
# CONSISTENCY OF DATABASE FREQUENCY TABLES is NP-complete

INSTANCE: a set `A` of attribute names, a domain set `D_a` for each `a ∈ A`, a set `V` of
objects, a collection `F` of frequency tables for some pairs `a, b ∈ A` (a frequency table for
`a, b ∈ A` is a function `f_{a,b} : D_a × D_b → Z⁺` with the sum, over all pairs `x ∈ D_a` and
`y ∈ D_b`, of `f_{a,b}(x, y)` equal to `|V|`), and a set `K` of triples `(v, a, x)` with
`v ∈ V`, `a ∈ A` and `x ∈ D_a`, representing the known attribute values. QUESTION: are the
frequency tables in `F` consistent with the known attribute values in `K`, i.e., is there a
collection of functions `g_a : V → D_a`, for each `a ∈ A`, such that `g_a(v) = x` if
`(v, a, x) ∈ K` and such that, for each `f_{a,b} ∈ F`, `x ∈ D_a` and `y ∈ D_b`, the number of
`v ∈ V` for which `g_a(v) = x` and `g_b(v) = y` is exactly `f_{a,b}(x, y)`?

The objects are `V = {0, …, |V| - 1}`, with `|V|` written in unary as the length of a list
`[true, …, true]` (as the vertex count in `BoundedDiameterAugmentationWanted`): the source lists
the objects, and a binary `|V|` would make the problem succinct, since a table `[[2^m]]` takes
`O(m)` bits while the functions `g_a` are defined on all `2^m` objects. The attributes are
`A = {0, …, |A| - 1}`, and the domain of attribute `a` is `D_a = {0, …, d_a - 1}`, given by the
list `[d_0, …, d_{|A|-1}]` of domain sizes; a binary `d_a` keeps the problem in NP, since each
value `g_a(v)` takes `O(log d_a)` bits and a table lists its `d_a · d_b` entries. A frequency
table is a pair `((a, b), rows)` whose `rows` list has `d_a` rows, each of length `d_b`, with
`f_{a,b}(x, y)` the `y`-th entry of the `x`-th row. Each table is the table `f_{a,b}` of its
pair, so `WellFormed` requires the pairs `(a, b)` of the tables to be distinct. The functions
`g_a` are given together as one function `g` with `g a v = g_a(v)`.

Table entries are positive integers, as in Garey and Johnson's `f_{a,b} : D_a × D_b → Z⁺`
(`WellFormed`). Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CONSISTENCY OF DATABASE FREQUENCY TABLES is NP-complete.** Source: Garey and Johnson
(1979), [SR35] (Reiss, 1977b). -/
public theorem_wanted frequencyTables_npComplete :
    frequencyTablesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L frequencyTablesDec

end MetaMathlibExt.Complexity.NPComplete.ConsistencyOfDatabaseFrequencyTables
