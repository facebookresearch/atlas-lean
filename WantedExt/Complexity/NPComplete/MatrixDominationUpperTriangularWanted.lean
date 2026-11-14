/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX DOMINATION for upper triangular matrices is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS12] MATRIX DOMINATION, comment:
remains NP-complete when `M` is upper triangular;
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38 (1980), 364-372, doi:10.1137/0138030 (the reference Garey and Johnson give for
[MS12]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MatrixDominationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixDominationUpperTriangular

open MetaMathlibExt.Complexity.NPComplete.MatrixDomination

/-!
# MATRIX DOMINATION for upper triangular matrices is NP-complete

Given an `n × n` upper triangular matrix `M` with entries from `{0, 1}` and a positive integer
`K`, is there a set of `K` or fewer non-zero entries of `M` that dominate all others, that is, a
subset `C ⊆ {1, ..., n} × {1, ..., n}` with `|C| ≤ K` such that `M i j = 1` for all
`(i, j) ∈ C` and such that, whenever `M i j = 1`, there is an `(i', j') ∈ C` with `i = i'` or
`j = j'`?

This is the restriction of MATRIX DOMINATION
(`WantedExt.Complexity.NPComplete.MatrixDominationWanted`) to upper triangular matrices: the
instance, `WellFormed`, `Entry` and `MatrixDominationFeasible` are reused unchanged, and the
restriction `UpperTriangular` (every non-zero entry `(r, c)` has `r ≤ c`) is added to the
instance class. Rows and columns are indexed from `0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The matrix is upper triangular: every entry below the main diagonal is `0`, i.e., every
non-zero entry `(r, c)` has `r ≤ c`. -/
def UpperTriangular (i : MatrixDominationInstance) : Prop :=
  ∀ r c, Entry i r c → r ≤ c

open Classical in
/-- MATRIX DOMINATION for upper triangular matrices as a decision problem over bitstrings. -/
noncomputable def matrixDominationUpperTriangularDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatrixDominationInstance) x with
  | some i => decide (WellFormed i ∧ UpperTriangular i ∧ MatrixDominationFeasible i)
  | none => false

/-- **MATRIX DOMINATION is NP-complete for upper triangular matrices.** Source: Garey and
Johnson (1979), [MS12], comment; Yannakakis and Gavril (1980). -/
public theorem_wanted matrixDominationUpperTriangular_npComplete :
    matrixDominationUpperTriangularDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matrixDominationUpperTriangularDec

end MetaMathlibExt.Complexity.NPComplete.MatrixDominationUpperTriangular
