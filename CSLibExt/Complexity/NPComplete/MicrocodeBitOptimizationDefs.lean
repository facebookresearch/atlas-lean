/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MICROCODE BIT OPTIMIZATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO10] MICROCODE BIT OPTIMIZATION;
E. L. Robertson, "Microcode bit optimization is NP-complete", IEEE Transactions on Computers
C-28 (1979), 316-319, doi:10.1109/TC.1979.1675353.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Log
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MicrocodeBitOptimization

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

end MetaMathlibExt.Complexity.NPComplete.MicrocodeBitOptimization
