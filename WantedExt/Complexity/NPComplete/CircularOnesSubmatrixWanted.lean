/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR ONES SUBMATRIX is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR14] CONSECUTIVE ONES SUBMATRIX, p. 229
(comment: the variant in which `B` must have the "circular ones" property, i.e., the columns of
`B` can be permuted so that in each row either all the `1`'s or all the `0`'s occur
consecutively, is also NP-complete; main-entry reference [Booth, 1975]);
K. S. Booth, *PQ-Tree Algorithms*, Ph.D. thesis, University of California, Berkeley (1975), as
cited by Garey and Johnson (the thesis itself was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ConsecutiveBlockMinimizationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularOnesSubmatrix

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveBlockMinimization
  (ConsecutiveBlockMinimizationInstance)

/-!
# CIRCULAR ONES SUBMATRIX is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`.
QUESTION: is there an `m × K` submatrix `B` of `A` that has the "circular ones" property, i.e.,
such that the columns of `B` can be permuted so that in each row either all the `1`'s or all
the `0`'s occur consecutively?

This is the variant of [SR14] CONSECUTIVE ONES SUBMATRIX
(`WantedExt.Complexity.NPComplete.ConsecutiveOnesSubmatrixWanted`) recorded in Garey and
Johnson's comment. As there, the instance format and its well-formedness are those of
CONSECUTIVE BLOCK MINIMIZATION (`ConsecutiveBlockMinimizationWanted`): the number `n` of
columns, the `m` rows (each a list of `n` entries, `true` for `1`), and `K`, with every row of
length `n` and `K` positive; and choosing the `K` columns of `B` and then a permutation of them
is choosing an injective map `f : Fin K → Fin n` (column `j` of the permuted `B` is column
`f j` of `A`). The entries equal to `b` of a row occur consecutively (`EntriesConsecutive`) when
every column between two columns holding `b` also holds `b`; the question asks this for each
row with `b = 1` or with `b = 0`. Garey and Johnson state `K` only as a positive integer; for
`K > n` there is no `m × K` submatrix, so such instances are no-instances, as in the parent.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- In the column order `f`, the entries of `row` equal to `b` occur consecutively: if the
entries in columns `f j₁` and `f j₃` are `b` and `j₁ ≤ j₂ ≤ j₃`, then the entry in column
`f j₂` is `b`. -/
def EntriesConsecutive {K n : ℕ} (row : List Bool) (f : Fin K → Fin n) (b : Bool) : Prop :=
  ∀ j₁ j₂ j₃ : Fin K, j₁ ≤ j₂ → j₂ ≤ j₃ →
    row.getD (f j₁) false = b → row.getD (f j₃) false = b → row.getD (f j₂) false = b

/-- Some `K` distinct columns of `A`, in some order `f`, form a matrix in which, in every row,
the `1`'s occur consecutively or the `0`'s occur consecutively. -/
def CircularOnesSubmatrixFeasible (i : ConsecutiveBlockMinimizationInstance) : Prop :=
  ∃ f : Fin i.2.2 → Fin i.1, Function.Injective f ∧
    ∀ row ∈ i.2.1, EntriesConsecutive row f true ∨ EntriesConsecutive row f false

open Classical in
/-- CIRCULAR ONES SUBMATRIX as a decision problem over bitstrings. -/
noncomputable def circularOnesSubmatrixDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveBlockMinimizationInstance) x with
  | some i => decide (ConsecutiveBlockMinimization.WellFormed i ∧
      CircularOnesSubmatrixFeasible i)
  | none => false

/-- **CIRCULAR ONES SUBMATRIX is NP-complete.** Source: Garey and Johnson (1979), [SR14],
comment; Booth (1975). -/
public theorem_wanted circularOnesSubmatrix_npComplete :
    circularOnesSubmatrixDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circularOnesSubmatrixDec

end MetaMathlibExt.Complexity.NPComplete.CircularOnesSubmatrix
