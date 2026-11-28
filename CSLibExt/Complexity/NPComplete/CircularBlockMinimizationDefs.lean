/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR BLOCK MINIMIZATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR17] CONSECUTIVE BLOCK
MINIMIZATION, p. 230, comment: "Remains NP-complete if "j = n" is replaced by "j = n and
b_i1 = 0" [Booth, 1975]";
K. S. Booth, *PQ-tree algorithms*, Ph.D. thesis, University of California, Berkeley (1975), as
cited by Garey and Johnson (the thesis itself was not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConsecutiveBlockMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularBlockMinimization

open ConsecutiveBlockMinimization

/-- Some permutation `σ` of the columns gives a matrix `B` with at most `K` entries `b_rj = 1`
such that `b_{r, j+1} = 0` (with `B` extended by `0` beyond the last column) and, if `j` is the
last column `n - 1`, also `b_{r, 0} = 0`. -/
def CircularBlockMinimizationFeasible (i : ConsecutiveBlockMinimizationInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1),
    ((Finset.range i.2.1.length ×ˢ Finset.range i.1).filter fun p =>
      permutedEntry i σ p.1 p.2 = true ∧ permutedEntry i σ p.1 (p.2 + 1) = false ∧
        (p.2 + 1 = i.1 → permutedEntry i σ p.1 0 = false)).card ≤ i.2.2

open Classical in
/-- CIRCULAR BLOCK MINIMIZATION as a decision problem over bitstrings. -/
noncomputable def circularBlockMinimizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveBlockMinimizationInstance) x with
  | some i => decide (WellFormed i ∧ CircularBlockMinimizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CircularBlockMinimization
