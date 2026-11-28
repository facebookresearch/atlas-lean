/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SORTING BY PREFIX REVERSALS (PANCAKE FLIPPING): definitions

Source:
L. Bulteau, G. Fertin and I. Rusu, "Pancake flipping is hard", Journal of Computer and System
Sciences 81(8) (2015), 1556-1574, doi:10.1016/j.jcss.2015.02.003, Theorem 2 (Sorting By
Prefix Reversals is NP-hard, by a reduction from 3-SAT); preprint arXiv:1111.0434.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PancakeFlipping

/-- An instance: the permutation `π = x₁, …, xₙ` (as a list) and the bound `K`. -/
abbrev PancakeFlippingInstance := List ℕ × ℕ

/-- The flip (prefix reversal) of length `r`: reverse the first `r` elements. -/
def flip (r : ℕ) (s : List ℕ) : List ℕ := (s.take r).reverse ++ s.drop r

/-- Well-formedness of an instance: `π` is a permutation of `1, …, n`. -/
def WellFormed (i : PancakeFlippingInstance) : Prop := i.1.Perm (List.range' 1 i.1.length)

/-- Some sequence of at most `K` flips, each of a length `r` with `1 ≤ r ≤ n`, applied in order,
turns `π` into the identity `1, 2, …, n`. -/
def PancakeFlippingFeasible (i : PancakeFlippingInstance) : Prop :=
  ∃ rs : List ℕ, rs.length ≤ i.2 ∧ (∀ r ∈ rs, 1 ≤ r ∧ r ≤ i.1.length) ∧
    rs.foldl (fun s r => flip r s) i.1 = List.range' 1 i.1.length

open Classical in
/-- SORTING BY PREFIX REVERSALS (PANCAKE FLIPPING) as a decision problem over bitstrings. -/
noncomputable def pancakeFlippingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PancakeFlippingInstance) x with
  | some i => decide (WellFormed i ∧ PancakeFlippingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PancakeFlipping
