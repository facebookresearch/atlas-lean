/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE ONES MATRIX AUGMENTATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR16] CONSECUTIVE ONES MATRIX
AUGMENTATION, p. 229 (references: [Booth, 1975], [Papadimitriou, 1976a]; transformation from
OPTIMAL LINEAR ARRANGEMENT);
K. S. Booth, *PQ-Tree Algorithms*, Ph.D. thesis, University of California, Berkeley (1975);
W. Lipski, Jr., "Generalizations of the consecutive ones property and related NP-complete
problems", Coordinated Science Laboratory Report T-67, University of Illinois at
Urbana-Champaign (1978), hdl:2142/74046 (records the result as Booth's, Problem 3).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation

/-- An instance: the number of columns `n`, the rows of `A` (each a list of `n` entries,
`true` for `1`), and the bound `K`. -/
abbrev ConsecutiveOnesMatrixAugmentationInstance := ℕ × List (List Bool) × ℕ

/-- Well-formedness of an instance: every row has exactly `n` entries, and `K` is positive. -/
def WellFormed (i : ConsecutiveOnesMatrixAugmentationInstance) : Prop :=
  (∀ row ∈ i.2.1, row.length = i.1) ∧ 0 < i.2.2

/-- The entry `a_rc` of `A` in row `r` and column `c` (indices from `0`). -/
def entry (i : ConsecutiveOnesMatrixAugmentationInstance) (r : Fin i.2.1.length)
    (c : Fin i.1) : Bool :=
  (i.2.1.get r).getD c false

/-- A matrix `B` with rows `Fin m` and columns `Fin n` has the consecutive ones property: some
permutation `σ` of the columns makes the `1`'s of every row consecutive, i.e. whenever positions
`j₁ ≤ j₂ ≤ j₃` of a row of the permuted matrix have `1`'s at `j₁` and `j₃`, they have a `1` at
`j₂`. -/
def HasConsecutiveOnes {m n : ℕ} (B : Fin m → Fin n → Bool) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ (r : Fin m) (j₁ j₂ j₃ : Fin n), j₁ ≤ j₂ → j₂ ≤ j₃ →
    B r (σ j₁) = true → B r (σ j₃) = true → B r (σ j₂) = true

/-- Some matrix `A'` (`B`) that agrees with `A` except at `K` or fewer entries where `A` has a
`0` and `A'` has a `1` has the consecutive ones property. -/
def ConsecutiveOnesMatrixAugmentationFeasible
    (i : ConsecutiveOnesMatrixAugmentationInstance) : Prop :=
  ∃ B : Fin i.2.1.length → Fin i.1 → Bool,
    (∀ r c, entry i r c = true → B r c = true) ∧
      (Finset.univ.filter fun p : Fin i.2.1.length × Fin i.1 =>
        entry i p.1 p.2 = false ∧ B p.1 p.2 = true).card ≤ i.2.2 ∧
      HasConsecutiveOnes B

open Classical in
/-- CONSECUTIVE ONES MATRIX AUGMENTATION as a decision problem over bitstrings. -/
noncomputable def consecutiveOnesMatrixAugmentationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveOnesMatrixAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ ConsecutiveOnesMatrixAugmentationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation
