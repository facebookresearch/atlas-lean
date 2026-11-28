/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR ONES MATRIX AUGMENTATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR16] CONSECUTIVE ONES MATRIX
AUGMENTATION, pp. 229-230, comment: "Variant in which we ask instead that A' have the circular
ones property is also NP-complete" (no separate attribution; the entry cites [Booth, 1975] and
[Papadimitriou, 1976a] for the consecutive ones problem; K. S. Booth, *PQ-Tree Algorithms*,
Ph.D. thesis, University of California, Berkeley (1975); not available).
-/
module

public import Mathlib.Data.Fintype.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CircularOnesSubmatrixDefs
public import CSLibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularOnesMatrixAugmentation

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation

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

end MetaMathlibExt.Complexity.NPComplete.CircularOnesMatrixAugmentation
