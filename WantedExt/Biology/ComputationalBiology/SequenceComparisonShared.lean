/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared model for comparing two random letter sequences

Definitions used by more than one `WantedExt` module on comparing two random letter sequences
(`LongestMatchShiftsWanted` and `AlignmentScorePhaseTransitionWanted`). As in Arratia and Waterman
(1985, 1994), the letters of both sequences are indexed from `1` and are independent and
identically distributed. Mathlib states such a hypothesis as separate `iIndepFun` and
`IdentDistrib` assumptions; `IIDLetters` bundles them for the letters the scores read, and assumes
nothing about the unused letters at index `0`.
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SequenceComparisonShared

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **I.i.d. letters from index 1.** The family `Z` carries letter `i` of the first sequence at
`Sum.inl i` and letter `j` of the second at `Sum.inr j`. The letters indexed from `1`, the family
`fun a => Z (Sum.map Nat.succ Nat.succ a)`, are measurable and independent, and each has the law
of the first letter `Z (Sum.inl 1)`. Nothing is assumed about the letters at index `0`, which no
score reads. -/
structure IIDLetters (P : Measure Ω) (Z : ℕ ⊕ ℕ → Ω → α) : Prop where
  /-- Every letter from index `1` is measurable. -/
  measurable : ∀ a, Measurable (Z (Sum.map Nat.succ Nat.succ a))
  /-- The letters from index `1` are independent. -/
  indep : iIndepFun (fun a => Z (Sum.map Nat.succ Nat.succ a)) P
  /-- Every letter from index `1` has the law of the first letter `Z (Sum.inl 1)`. -/
  identDistrib : ∀ a, IdentDistrib (Z (Sum.map Nat.succ Nat.succ a)) (Z (Sum.inl 1)) P P

end WantedExt.Biology.ComputationalBiology.SequenceComparisonShared
