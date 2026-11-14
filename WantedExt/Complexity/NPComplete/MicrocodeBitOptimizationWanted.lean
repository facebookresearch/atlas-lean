/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MICROCODE BIT OPTIMIZATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO10] MICROCODE BIT OPTIMIZATION;
E. L. Robertson, "Microcode bit optimization is NP-complete", IEEE Transactions on Computers
C-28 (1979), 316-319, doi:10.1109/TC.1979.1675353.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Log
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MicrocodeBitOptimization

/-!
# MICROCODE BIT OPTIMIZATION is NP-complete

Given a finite set `A` of micro-commands, a collection `C = {C₁, …, Cₘ}` of subsets of `A`
(micro-instructions), and a positive integer `K`, is there a partition of `A` into disjoint
sets `A₁, …, Aₙ` such that no pair `Aᵢ, Cⱼ` has more than one element in common and
`∑ᵢ ⌈log₂(|Aᵢ| + 1)⌉ ≤ K`?

The micro-commands are `Fin a`; each micro-instruction is a list of distinct micro-commands, and
`K ≥ 1` (`WellFormed`). The partition is a block map `f : Fin a → Fin a`, block `b` being
`{x | f x = b}`. Every partition has at most `a` nonempty blocks, so `a` labels suffice, and an
empty block adds `⌈log₂ 1⌉ = 0` to the sum, so empty labels change nothing. `⌈log₂ m⌉` is
Mathlib's `Nat.clog 2 m`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `a` of micro-commands, the micro-instructions `C₁, …, Cₘ` (lists of
micro-commands), and the bound `K`. -/
abbrev MicrocodeBitOptimizationInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every micro-instruction lists distinct micro-commands
`< a`, and the bound `K` is positive. -/
def WellFormed (i : MicrocodeBitOptimizationInstance) : Prop :=
  (∀ c ∈ i.2.1, c.Nodup ∧ ∀ x ∈ c, x < i.1) ∧ 0 < i.2.2

/-- A partition of the micro-commands, as a block map `f`, in which every block shares at most
one micro-command with every micro-instruction, and whose total field width
`∑ ⌈log₂(|block| + 1)⌉` is at most `K`. -/
def MicrocodeBitOptimizationFeasible (i : MicrocodeBitOptimizationInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.1,
    (∀ b, ∀ c ∈ i.2.1, (Finset.univ.filter fun x => f x = b ∧ (x : ℕ) ∈ c).card ≤ 1) ∧
      ∑ b, Nat.clog 2 ((Finset.univ.filter fun x => f x = b).card + 1) ≤ i.2.2

open Classical in
/-- MICROCODE BIT OPTIMIZATION as a decision problem over bitstrings. -/
noncomputable def microcodeBitOptimizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MicrocodeBitOptimizationInstance) x with
  | some i => decide (WellFormed i ∧ MicrocodeBitOptimizationFeasible i)
  | none => false

/-- **MICROCODE BIT OPTIMIZATION is NP-complete.** Source: Garey and Johnson (1979), [PO10];
Robertson (1979). -/
public theorem_wanted microcodeBitOptimization_npComplete :
    microcodeBitOptimizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L microcodeBitOptimizationDec

end MetaMathlibExt.Complexity.NPComplete.MicrocodeBitOptimization
