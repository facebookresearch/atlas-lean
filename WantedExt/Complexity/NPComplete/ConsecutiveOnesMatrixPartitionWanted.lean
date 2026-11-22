/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE ONES MATRIX PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR15] CONSECUTIVE ONES MATRIX PARTITION
(attributed to W. Lipski, Jr. [1978], private communication).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixPartition

/-!
# CONSECUTIVE ONES MATRIX PARTITION is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s. QUESTION: can the rows of `A` be partitioned
into two groups such that the resulting `m₁ × n` and `m₂ × n` matrices (`m₁ + m₂ = m`) each have
the consecutive ones property?

This is Garey and Johnson's [SR15] (p. 229), with reference "[Lipsky, 1978]" (their spelling of
W. Lipski, Jr.; a private communication per their bibliography), transformation from
HAMILTONIAN PATH for cubic graphs; the original was not available. Membership in NP: the
partition and a column permutation for each group are a certificate.

The matrix is a list of `m` rows, each a list of `n` Booleans (`true` for `1`); rows and columns
are indexed from `0`. The partition is a map `g` from rows to `Bool`: one group is the rows with
`g r = true`, the other the rest (`m₁ + m₂ = m`; a group may be empty). The consecutive ones
property is `ConsecutiveOnesMatrixAugmentation.HasConsecutiveOnes`: some permutation of the
columns makes the `1`'s of every row consecutive. It is applied to `A` with the rows outside the
group replaced by rows of `0`'s; a row of `0`'s constrains no column order, so this says exactly
that the matrix formed by the rows of the group has the property.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of columns `n` and the rows of `A` (each a list of `n` entries,
`true` for `1`). -/
abbrev ConsecutiveOnesMatrixPartitionInstance := ℕ × List (List Bool)

/-- Well-formedness of an instance: every row has exactly `n` entries. -/
def WellFormed (i : ConsecutiveOnesMatrixPartitionInstance) : Prop :=
  ∀ row ∈ i.2, row.length = i.1

/-- The entry `a_rc` of `A` in row `r` and column `c` (indices from `0`). -/
def entry (i : ConsecutiveOnesMatrixPartitionInstance) (r : Fin i.2.length) (c : Fin i.1) :
    Bool :=
  (i.2.get r).getD c false

/-- The rows can be split into the group `g r = true` and the group `g r = false` so that the
matrix of each group has the consecutive ones property. -/
def ConsecutiveOnesMatrixPartitionFeasible (i : ConsecutiveOnesMatrixPartitionInstance) :
    Prop :=
  ∃ g : Fin i.2.length → Bool,
    ConsecutiveOnesMatrixAugmentation.HasConsecutiveOnes (fun r c => g r && entry i r c) ∧
      ConsecutiveOnesMatrixAugmentation.HasConsecutiveOnes (fun r c => !g r && entry i r c)

open Classical in
/-- CONSECUTIVE ONES MATRIX PARTITION as a decision problem over bitstrings. -/
noncomputable def consecutiveOnesMatrixPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsecutiveOnesMatrixPartitionInstance) x with
  | some i => decide (WellFormed i ∧ ConsecutiveOnesMatrixPartitionFeasible i)
  | none => false

/-- **CONSECUTIVE ONES MATRIX PARTITION is NP-complete.** Source: Garey and Johnson (1979),
[SR15]; Lipski (1978, private communication). -/
public theorem_wanted consecutiveOnesMatrixPartition_npComplete :
    consecutiveOnesMatrixPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consecutiveOnesMatrixPartitionDec

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixPartition
