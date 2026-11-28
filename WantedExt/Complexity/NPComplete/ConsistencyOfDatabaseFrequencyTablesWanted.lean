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
public import CSLibExt.Complexity.NPComplete.ConsistencyOfDatabaseFrequencyTablesDefs

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

/-- **CONSISTENCY OF DATABASE FREQUENCY TABLES is NP-complete.** Source: Garey and Johnson
(1979), [SR35] (Reiss, 1977b). -/
public theorem_wanted frequencyTables_npComplete :
    frequencyTablesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L frequencyTablesDec

end MetaMathlibExt.Complexity.NPComplete.ConsistencyOfDatabaseFrequencyTables
