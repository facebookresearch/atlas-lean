/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM ERROR CORRECTION (single individual SNP haplotyping) is NP-complete

Source:
R. Cilibrasi, L. van Iersel, S. Kelk and J. Tromp, "The complexity of the single individual
SNP haplotyping problem", Algorithmica 49 (2007), 13-36, doi:10.1007/s00453-007-0029-z,
arXiv:q-bio/0508012, Section II.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumErrorCorrection

/-!
# MINIMUM ERROR CORRECTION (single individual SNP haplotyping) is NP-complete

An SNP matrix is an `n × m` matrix with entries in `{0, 1, -}`, where `-` is a hole. For a
row `X ∈ {0, 1, -}^m` and a haplotype `Y ∈ {0, 1}^m`, `d(X, Y)` is the number of positions
where `X` is `0` and `Y` is `1`, or vice versa; holes do not count. A matrix is feasible iff
there are two haplotypes `H₁, H₂ ∈ {0, 1}^m` such that every row `r` has `d(r, H₁) = 0` or
`d(r, H₂) = 0`. A flip converts a `0` entry to `1` or vice versa (holes are never flipped).
MEC asks for the smallest number of flips that makes the matrix feasible; its decision form:
given the matrix and an integer `K`, can at most `K` flips make it feasible? Cilibrasi, van
Iersel, Kelk and Tromp (2007) proved MEC NP-hard already for gapless matrices (Lemma 1,
Ungapped-MEC, "and hence 1-gap MEC and also the general MEC").

At most `K` flips make the matrix feasible iff there are haplotypes `H₁, H₂` and an assignment
of each row `r` to one of them with `∑_r d(r, H_{side r}) ≤ K`: flipping the `d(r, H_{side r})`
mismatched entries of each row makes it agree with its haplotype; conversely, if flips make
every row `r` agree with `H_{side r}` off the holes, they flip at least the
`d(r, H_{side r})` mismatched entries of `r`. `MinimumErrorCorrectionFeasible` states the
question in this form.

Entries are `0`, `1`, and `2` for a hole.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of columns (SNP sites), the rows (fragments) of the SNP matrix
with entries `0`, `1`, or `2` for a hole, and the bound `K`. -/
abbrev MinimumErrorCorrectionInstance := ℕ × List (List ℕ) × ℕ

/-- `d(X, Y)`: the number of positions `j` where the row `X` has a `0` or `1` entry different
from the haplotype value `Y j`; holes (`2`) do not count. -/
def mismatches {m : ℕ} (X : List ℕ) (Y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin m => X.getD j 2 ≠ 2 ∧ decide (X.getD j 2 = 1) ≠ Y j).card

/-- Well-formedness of an instance: every row has length `m` and entries in `{0, 1, 2}`. -/
def WellFormed (i : MinimumErrorCorrectionInstance) : Prop :=
  ∀ r ∈ i.2.1, r.length = i.1 ∧ ∀ x ∈ r, x ≤ 2

/-- At most `K` flips make the matrix feasible: there are haplotypes `H₁`, `H₂` and an
assignment `side` of the rows to them with total mismatch count at most `K`. -/
def MinimumErrorCorrectionFeasible (i : MinimumErrorCorrectionInstance) : Prop :=
  ∃ H₁ H₂ : Fin i.1 → Bool, ∃ side : Fin i.2.1.length → Bool,
    (∑ r : Fin i.2.1.length, mismatches (i.2.1.get r) (if side r then H₂ else H₁)) ≤ i.2.2

open Classical in
/-- MINIMUM ERROR CORRECTION as a decision problem over bitstrings. -/
noncomputable def minimumErrorCorrectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumErrorCorrectionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumErrorCorrectionFeasible i)
  | none => false

/-- **MINIMUM ERROR CORRECTION is NP-complete.** Source: Cilibrasi, van Iersel, Kelk and Tromp
(2007), Section II. -/
public theorem_wanted minimumErrorCorrection_npComplete :
    minimumErrorCorrectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumErrorCorrectionDec

end MetaMathlibExt.Complexity.NPComplete.MinimumErrorCorrection
