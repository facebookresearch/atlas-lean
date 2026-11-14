/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENSEMBLE COMPUTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO9] ENSEMBLE
COMPUTATION; the proof is Theorem 3.6 in Section 3.2.2 of the book (local
replacement, a transformation from VERTEX COVER).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputation

/-!
# ENSEMBLE COMPUTATION is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `A`, and a positive integer `J`.
QUESTION: is there a sequence `S = (z₁ ← x₁ ∪ y₁, z₂ ← x₂ ∪ y₂, ..., zⱼ ← xⱼ ∪ yⱼ)` of
`j ≤ J` union operations, where each `xᵢ` and `yᵢ` is either `{a}` for some `a ∈ A` or `zₖ`
for some `k < i`, such that `xᵢ` and `yᵢ` are disjoint, `1 ≤ i ≤ j`, and such that for every
subset `c ∈ C` there exists some `zᵢ`, `1 ≤ i ≤ j`, that is identical to `c`?

The elements of `A` are `Fin m`; each member of `C` is given as a strictly increasing list,
so equal subsets have equal lists. A sequence is given by the values `zᵢ` and, for each `i`,
the two operands, each `Sum.inl a` (the singleton `{a}`) or `Sum.inr k` (the earlier result
`zₖ`, `k < i`); indices are 0-based.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the size `m` of `A` (elements `Fin m`), the collection `C` as a list of
strictly increasing lists of elements, and the bound `J`. -/
abbrev EnsembleComputationInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every member of `C` is a strictly increasing list of
elements of `A`, no member is listed twice, and `J` is positive. -/
def WellFormed (i : EnsembleComputationInstance) : Prop :=
  (∀ c ∈ i.2.1, c.Pairwise (· < ·) ∧ ∀ a ∈ c, a < i.1) ∧ i.2.1.Nodup ∧ 0 < i.2.2

/-- The subset of `Fin m` listed by `c` (entries out of range are dropped). -/
def toSubset (m : ℕ) (c : List ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun a => (a : ℕ) ∈ c

/-- The value of an operand of operation `i`: `Sum.inl a` is `{a}`, `Sum.inr k` is `z k`. -/
def operandValue {m j : ℕ} (z : Fin j → Finset (Fin m)) : Fin m ⊕ Fin j → Finset (Fin m)
  | .inl a => {a}
  | .inr k => z k

/-- A sequence of `j ≤ J` union operations `zᵢ ← xᵢ ∪ yᵢ` with disjoint operands, each a
singleton or an earlier result, such that every member of `C` equals some `zᵢ`. -/
def EnsembleComputationFeasible (i : EnsembleComputationInstance) : Prop :=
  ∃ j ≤ i.2.2, ∃ z : Fin j → Finset (Fin i.1), ∃ x y : Fin j → Fin i.1 ⊕ Fin j,
    (∀ t k, x t = .inr k → k < t) ∧ (∀ t k, y t = .inr k → k < t) ∧
    (∀ t, Disjoint (operandValue z (x t)) (operandValue z (y t))) ∧
    (∀ t, z t = operandValue z (x t) ∪ operandValue z (y t)) ∧
    ∀ c ∈ i.2.1, ∃ t, z t = toSubset i.1 c

open Classical in
/-- ENSEMBLE COMPUTATION as a decision problem over bitstrings. -/
noncomputable def ensembleComputationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnsembleComputationInstance) x with
  | some i => decide (WellFormed i ∧ EnsembleComputationFeasible i)
  | none => false

/-- **ENSEMBLE COMPUTATION is NP-complete.** Source: Garey and Johnson (1979), [PO9] and
Theorem 3.6 (Section 3.2.2). -/
public theorem_wanted ensembleComputation_npComplete :
    ensembleComputationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ensembleComputationDec

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputation
