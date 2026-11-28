/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE ONES SUBMATRIX: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR14] CONSECUTIVE ONES SUBMATRIX (reference:
[Booth, 1975]; transformation from HAMILTONIAN PATH);
M. T. Hajiaghayi and Y. Ganjali, "A note on the Consecutive Ones Submatrix problem", Information
Processing Letters 83 (2002), 163-166, doi:10.1016/S0020-0190(01)00325-8;
J. Tan and L. Zhang, "The Consecutive Ones Submatrix problem for sparse matrices", Algorithmica
48 (2007), 287-299, doi:10.1007/s00453-007-0118-z.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConsecutiveBlockMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesSubmatrix

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveBlockMinimization
  (ConsecutiveBlockMinimizationInstance)

/-- Some `K` distinct columns of `A`, in some order `f`, form a matrix in which the `1`'s of
every row occur consecutively: if the entries in columns `f j₁` and `f j₃` of a row are `1` and
`j₁ ≤ j₂ ≤ j₃`, then the entry in column `f j₂` is `1`. -/
def ConsecutiveOnesSubmatrixFeasible (i : ConsecutiveBlockMinimizationInstance) : Prop :=
  ∃ f : Fin i.2.2 → Fin i.1, Function.Injective f ∧
    ∀ row ∈ i.2.1, ∀ j₁ j₂ j₃ : Fin i.2.2, j₁ ≤ j₂ → j₂ ≤ j₃ →
      row.getD (f j₁) false = true → row.getD (f j₃) false = true →
        row.getD (f j₂) false = true

open Classical in
/-- CONSECUTIVE ONES SUBMATRIX as a decision problem over bitstrings. -/
noncomputable def consecutiveOnesSubmatrixDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveBlockMinimizationInstance) x with
  | some i => decide (ConsecutiveBlockMinimization.WellFormed i ∧
      ConsecutiveOnesSubmatrixFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesSubmatrix
