/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM FRAGMENT REMOVAL is NP-complete

Source:
G. Lancia, V. Bafna, S. Istrail, R. Lippert, and R. Schwartz, "SNPs problems, complexity, and
algorithms", Algorithms - ESA 2001, Lecture Notes in Computer Science 2161, Springer (2001),
182-193, doi:10.1007/3-540-44676-1_15, Section 1.3 and Theorem 5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import WantedExt.Complexity.NPComplete.MinimumErrorCorrectionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumFragmentRemoval

open MinimumErrorCorrection (MinimumErrorCorrectionInstance)

/-!
# MINIMUM FRAGMENT REMOVAL is NP-complete

INSTANCE: an SNP matrix `M`, an `n × m` matrix over `{A, B, -}` whose rows are fragments and
whose columns are SNPs, and an integer `K`.
QUESTION: can at most `K` fragments (rows) be removed so that the resulting matrix is feasible?

The definitions are those of Lancia, Bafna, Istrail, Lippert and Schwartz (Section 1.3): two
fragments are in conflict if some SNP has value `A` in one and `B` in the other; the fragment
conflict graph `G_F(M)` has an edge for each pair of fragments in conflict; `M` is feasible if
`G_F(M)` is bipartite; MFR asks to remove the minimum number of fragments so that the resulting
matrix is feasible. Theorem 5 proves MFR NP-hard (by encoding any graph as the conflict graph of
an SNP matrix, Lemma 7, which reduces node deletion to a bipartite graph); a set of removed rows
with a 2-colouring of the rest is a short certificate.

The instance and its well-formedness are those of MINIMUM ERROR CORRECTION
(`MinimumErrorCorrectionWanted`): the number `m` of columns, the rows with entries `0` (`A`),
`1` (`B`) and `2` (a hole `-`), and `K`. Fragments are the row positions `Fin n`. Conflicts
depend only on pairs of rows, so the conflict graph of the matrix `M[F - R]` without the rows `R`
is the subgraph of `G_F(M)` induced on the remaining rows; bipartiteness is Mathlib's
`SimpleGraph.IsBipartite`. `K` uses the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MINIMUM FRAGMENT REMOVAL is NP-complete.** Source: Lancia, Bafna, Istrail, Lippert, and
Schwartz (2001), Theorem 5. -/
public theorem_wanted minimumFragmentRemoval_npComplete :
    minimumFragmentRemovalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumFragmentRemovalDec

end MetaMathlibExt.Complexity.NPComplete.MinimumFragmentRemoval
