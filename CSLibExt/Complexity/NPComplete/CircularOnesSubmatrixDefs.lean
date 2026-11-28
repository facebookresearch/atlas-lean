/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR ONES SUBMATRIX: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConsecutiveBlockMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularOnesSubmatrix

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveBlockMinimization
  (ConsecutiveBlockMinimizationInstance)

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

end MetaMathlibExt.Complexity.NPComplete.CircularOnesSubmatrix
