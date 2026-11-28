/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two sets whose sumset elements are squares

Statements from Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
*INTEGERS* 26 (2026), Article A66
(<https://math.colgate.edu/~integers/aa66/aa66.pdf>).

Finite families are indexed by `Fin m` and `Fin n`; the paper's
one-based index `1` is Lean index `0` here.  A `3 × 3` matrix with
squared entries is represented by its integer roots
`e : Fin 3 → Fin 3 → ℤ`, with matrix entries `(e i j)^2`.
Semi-magic means all row sums and all column sums of those squared
entries have one common value.

Lemma 2 is split into the actual construction and converse
statements used in its proof, rather than the bare existence
formulation.  This avoids a vacuous reading in which both sides are
satisfied independently by zero examples: the forward parts start
from given semi-magic root matrices, and the converse parts produce
the matrices `E₁`, `F₁`, `G₁`, and `H₁` built from the pairwise
sums in the paper's proof.  The forward part for quintuples,
`exists_isSemiMagicRoots_f_of_pairwiseSumsSquares_quintuple`, is
proved in
`MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple`.
The statement
`exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple` is
proved in
`MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuadruple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuintuple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresTriple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresTripleFamily31
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresPairwiseSumsSquaresQuintupleFamily41
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsFOfPairwiseSumsSquaresQuintuple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresExistsIsSemiMagicRootsGhOfPairwiseSumsSquaresQuadruple

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

end TwoSetsSumsetSquaresWanted

end NumberTheory

end MathlibExt
