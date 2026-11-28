/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CROSSWORD PUZZLE CONSTRUCTION with no blank squares: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GP14] CROSSWORD PUZZLE CONSTRUCTION, p. 258,
comment: "Remains NP-complete even if all entries in A are 0" (the entry's reference is
[Lewis and Papadimitriou, 1978]: H. R. Lewis and C. H. Papadimitriou, "The efficiency of
algorithms", Scientific American 238(1) (1978), 96-109, doi:10.1038/scientificamerican0178-96).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CrosswordPuzzleConstructionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstructionNoBlankSquares

open MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstruction
  (CrosswordPuzzleConstructionInstance CrosswordPuzzleConstructionFeasible)

/-- Well-formedness of an instance: a well-formed CROSSWORD PUZZLE CONSTRUCTION instance in
which every entry of `A` is `0`. -/
def WellFormed (i : CrosswordPuzzleConstructionInstance) : Prop :=
  CrosswordPuzzleConstruction.WellFormed i ∧ ∀ row ∈ i.2.2, ∀ a ∈ row, a = false

open Classical in
/-- CROSSWORD PUZZLE CONSTRUCTION with no blank squares as a decision problem over
bitstrings. -/
noncomputable def crosswordPuzzleConstructionNoBlankSquaresDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CrosswordPuzzleConstructionInstance) x with
  | some i => decide (WellFormed i ∧ CrosswordPuzzleConstructionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstructionNoBlankSquares
