/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SNP REMOVAL: definitions

Source:
G. Lancia, V. Bafna, S. Istrail, R. Lippert, and R. Schwartz, "SNPs problems, complexity, and
algorithms", Algorithms - ESA 2001, Lecture Notes in Computer Science 2161, Springer (2001),
182-193, doi:10.1007/3-540-44676-1_15, Section 1.3 and Theorem 8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumFragmentRemovalDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSnpRemoval

open MinimumErrorCorrection (MinimumErrorCorrectionInstance)
open MinimumFragmentRemoval (fragmentConflictGraph)

/-- The matrix with the columns in `C` removed: their entries are replaced by holes (`2`). -/
def removeColumns (i : MinimumErrorCorrectionInstance) (C : Finset (Fin i.1)) :
    MinimumErrorCorrectionInstance :=
  (i.1, i.2.1.map (fun X => X.mapIdx fun k x => if k ∈ C.map Fin.valEmbedding then 2 else x),
    i.2.2)

/-- Well-formedness of an instance: every row has length `m` and entries in `{0, 1, 2}` (that of
MINIMUM FRAGMENT REMOVAL). -/
def WellFormed (i : MinimumErrorCorrectionInstance) : Prop :=
  MinimumFragmentRemoval.WellFormed i

/-- Removing some set `C` of at most `K` columns leaves a feasible matrix: its fragment conflict
graph is bipartite. -/
def MinimumSnpRemovalFeasible (i : MinimumErrorCorrectionInstance) : Prop :=
  ∃ C : Finset (Fin i.1), C.card ≤ i.2.2 ∧ (fragmentConflictGraph (removeColumns i C)).IsBipartite

open Classical in
/-- MINIMUM SNP REMOVAL as a decision problem over bitstrings. -/
noncomputable def minimumSnpRemovalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumErrorCorrectionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumSnpRemovalFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumSnpRemoval
