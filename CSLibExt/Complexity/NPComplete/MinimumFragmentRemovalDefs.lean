/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM FRAGMENT REMOVAL: definitions

Source:
G. Lancia, V. Bafna, S. Istrail, R. Lippert, and R. Schwartz, "SNPs problems, complexity, and
algorithms", Algorithms - ESA 2001, Lecture Notes in Computer Science 2161, Springer (2001),
182-193, doi:10.1007/3-540-44676-1_15, Section 1.3 and Theorem 5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.MinimumErrorCorrectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumFragmentRemoval

open MinimumErrorCorrection (MinimumErrorCorrectionInstance)

/-- Rows `X` and `Y` conflict at column `k`: one has value `A` (`0`) and the other value `B`
(`1`) there. -/
def ConflictAt (X Y : List ℕ) (k : ℕ) : Prop :=
  (X.getD k 2 = 0 ∧ Y.getD k 2 = 1) ∨ (X.getD k 2 = 1 ∧ Y.getD k 2 = 0)

/-- The fragment conflict graph `G_F(M)`: the fragments (row positions), two of them adjacent
when they conflict at some SNP (column). -/
def fragmentConflictGraph (i : MinimumErrorCorrectionInstance) :
    SimpleGraph (Fin i.2.1.length) :=
  SimpleGraph.fromRel fun a b => ∃ k : Fin i.1, ConflictAt (i.2.1.get a) (i.2.1.get b) k

/-- Well-formedness of an instance: every row has length `m` and entries in `{0, 1, 2}` (that of
MINIMUM ERROR CORRECTION). -/
def WellFormed (i : MinimumErrorCorrectionInstance) : Prop :=
  MinimumErrorCorrection.WellFormed i

/-- Removing some set `R` of at most `K` fragments leaves a feasible matrix: the conflict graph
induced on the remaining fragments is bipartite. -/
def MinimumFragmentRemovalFeasible (i : MinimumErrorCorrectionInstance) : Prop :=
  ∃ R : Finset (Fin i.2.1.length), R.card ≤ i.2.2 ∧
    ((fragmentConflictGraph i).induce ((↑R : Set (Fin i.2.1.length))ᶜ)).IsBipartite

open Classical in
/-- MINIMUM FRAGMENT REMOVAL as a decision problem over bitstrings. -/
noncomputable def minimumFragmentRemovalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumErrorCorrectionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumFragmentRemovalFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumFragmentRemoval
