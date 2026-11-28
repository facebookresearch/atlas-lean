/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREFIX REVERSAL DISTANCE FOR BINARY STRINGS: definitions

Source:
C. Hurkens, L. van Iersel, J. Keijsper, S. Kelk, L. Stougie and J. Tromp, "Prefix reversals on
binary and ternary strings", SIAM Journal on Discrete Mathematics 21(3) (2007), 592-611,
doi:10.1137/060664252, Theorem 9 (the decision problem binary-PD is NP-complete, by a reduction
from 3-PARTITION); preprint arXiv:math/0602456.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PancakeFlippingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PancakeFlippingBinaryStrings

/-- An instance: the strings `s` and `t` (lists of symbols) and the bound `B`. -/
abbrev PancakeFlippingBinaryStringsInstance := List ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: `s` is a fully binary string (every symbol is `0` or `1`,
and both occur), `t` is compatible with `s` (a permutation of it), and `B` is positive. -/
def WellFormed (i : PancakeFlippingBinaryStringsInstance) : Prop :=
  (∀ a ∈ i.1, a < 2) ∧ 0 ∈ i.1 ∧ 1 ∈ i.1 ∧ i.1.Perm i.2.1 ∧ 0 < i.2.2

/-- Some sequence of at most `B` flips, each of a length `r` with `1 ≤ r ≤ n`, applied in order,
turns `s` into `t`. -/
def PancakeFlippingBinaryStringsFeasible (i : PancakeFlippingBinaryStringsInstance) : Prop :=
  ∃ rs : List ℕ, rs.length ≤ i.2.2 ∧ (∀ r ∈ rs, 1 ≤ r ∧ r ≤ i.1.length) ∧
    rs.foldl (fun x r => PancakeFlipping.flip r x) i.1 = i.2.1

open Classical in
/-- PREFIX REVERSAL DISTANCE FOR BINARY STRINGS as a decision problem over bitstrings. -/
noncomputable def pancakeFlippingBinaryStringsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PancakeFlippingBinaryStringsInstance) x with
  | some i => decide (WellFormed i ∧ PancakeFlippingBinaryStringsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PancakeFlippingBinaryStrings
