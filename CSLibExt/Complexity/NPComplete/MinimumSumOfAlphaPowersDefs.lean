/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUM OF `α`-TH POWERS is NP-complete for every fixed integer `α ≥ 2`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP19] MINIMUM SUM OF SQUARES, p. 225,
comment: NP-completeness is preserved if the exponent `2` is replaced by any fixed rational
`α > 1` (stated here for the integer exponents `α ≥ 2`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSumOfAlphaPowers

/-- An instance: the sizes `s(a)` of the elements of `A` as a list, the number `K` of sets, and
the bound `J`. -/
abbrev MinimumSumOfAlphaPowersInstance := List ℕ × ℕ × ℕ

/-- Well-formedness of an instance: every size is positive, `0 < K ≤ |A|`, and `0 < J`. -/
def WellFormed (i : MinimumSumOfAlphaPowersInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ 0 < i.2.1 ∧ i.2.1 ≤ i.1.length ∧ 0 < i.2.2

/-- Some partition `f : A → Fin K` of `A` into `K` sets has `∑ⱼ (∑_{f a = j} s(a))^α ≤ J`. -/
def MinimumSumOfAlphaPowersFeasible (α : ℕ) (i : MinimumSumOfAlphaPowersInstance) : Prop :=
  ∃ f : Fin i.1.length → Fin i.2.1,
    ∑ j : Fin i.2.1, ((Finset.univ.filter fun a => f a = j).sum fun a => i.1.get a) ^ α ≤
      i.2.2

open Classical in
/-- MINIMUM SUM OF `α`-TH POWERS as a decision problem over bitstrings. -/
noncomputable def minimumSumOfAlphaPowersDec (α : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumSumOfAlphaPowersInstance) x with
  | some i => decide (WellFormed i ∧ MinimumSumOfAlphaPowersFeasible α i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumSumOfAlphaPowers
