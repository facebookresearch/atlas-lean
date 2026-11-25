/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR ONES MATRIX AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR16] CONSECUTIVE ONES MATRIX
AUGMENTATION, pp. 229-230, comment: "Variant in which we ask instead that A' have the circular
ones property is also NP-complete" (no separate attribution; the entry cites [Booth, 1975] and
[Papadimitriou, 1976a] for the consecutive ones problem; K. S. Booth, *PQ-Tree Algorithms*,
Ph.D. thesis, University of California, Berkeley (1975); not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Fintype.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CircularOnesSubmatrixWanted
public import WantedExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularOnesMatrixAugmentation

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation

/-!
# CIRCULAR ONES MATRIX AUGMENTATION is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`. QUESTION: is
there a matrix `A'`, obtained from `A` by changing `K` or fewer `0` entries to `1`'s, such that
`A'` has the circular ones property, i.e. the columns of `A'` can be permuted so that in each
row either all the `1`'s or all the `0`'s occur consecutively?

This is the variant of [SR16] CONSECUTIVE ONES MATRIX AUGMENTATION
(`WantedExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationWanted`) recorded in Garey
and Johnson's comment; the circular ones property is the one Garey and Johnson define in
[SR14]. The instance, its well-formedness, the entries `entry i r c` of `A` and the matrix `A'`
(a function `B : Fin m → Fin n → Bool` that is `1` wherever `A` is `1`, with at most `K`
changed entries) are those of the parent. A permutation of the columns is
`σ : Equiv.Perm (Fin n)`: column `j` of the permuted matrix is column `σ j` of `B`. The entries
equal to `b` of a row occur consecutively when every position between two positions holding
`b` also holds `b` (`CircularOnesSubmatrix.EntriesConsecutive` of
`WantedExt.Complexity.NPComplete.CircularOnesSubmatrixWanted`, applied to the row
`List.ofFn (B r)`); the question asks this for each row with `b = 1` or with `b = 0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A matrix `B` with rows `Fin m` and columns `Fin n` has the circular ones property: some
permutation `σ` of the columns makes, in every row of the permuted matrix, the `1`'s
consecutive or the `0`'s consecutive. -/
def HasCircularOnes {m n : ℕ} (B : Fin m → Fin n → Bool) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ r : Fin m,
    CircularOnesSubmatrix.EntriesConsecutive (List.ofFn (B r)) σ true ∨
      CircularOnesSubmatrix.EntriesConsecutive (List.ofFn (B r)) σ false

/-- Some matrix `A'` (`B`) that agrees with `A` except at `K` or fewer entries where `A` has a
`0` and `A'` has a `1` has the circular ones property. -/
def CircularOnesMatrixAugmentationFeasible
    (i : ConsecutiveOnesMatrixAugmentationInstance) : Prop :=
  ∃ B : Fin i.2.1.length → Fin i.1 → Bool,
    (∀ r c, entry i r c = true → B r c = true) ∧
      (Finset.univ.filter fun p : Fin i.2.1.length × Fin i.1 =>
        entry i p.1 p.2 = false ∧ B p.1 p.2 = true).card ≤ i.2.2 ∧
      HasCircularOnes B

open Classical in
/-- CIRCULAR ONES MATRIX AUGMENTATION as a decision problem over bitstrings. -/
noncomputable def circularOnesMatrixAugmentationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveOnesMatrixAugmentationInstance) x with
  | some i => decide (ConsecutiveOnesMatrixAugmentation.WellFormed i ∧
      CircularOnesMatrixAugmentationFeasible i)
  | none => false

/-- **CIRCULAR ONES MATRIX AUGMENTATION is NP-complete.** Source: Garey and Johnson (1979),
[SR16], comment. -/
public theorem_wanted circularOnesMatrixAugmentation_npComplete :
    circularOnesMatrixAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circularOnesMatrixAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.CircularOnesMatrixAugmentation
