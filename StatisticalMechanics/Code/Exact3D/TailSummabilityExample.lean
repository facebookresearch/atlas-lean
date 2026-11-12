/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.TailSummabilitySkeleton

open scoped BigOperators









namespace StatMech
namespace Exact3D

namespace TailSummabilityExample



noncomputable def exampleSplit : ContributionSplit (Fin 2) where
  finiteContribution := fun _ => (1 : ℝ)
  tailContribution := fun _ => (1 : ℝ) / 10
  totalContribution := fun _ => (11 : ℝ) / 10


def exampleTable : RatInterval.CaseTable Unit where
  cases := Finset.univ
  interval := fun _ => RatInterval.point 1


def exampleClassifier (_ : Fin 2) : Unit := ()


theorem exampleSplit_additive : exampleSplit.Additive := by
  intro a
  norm_num [exampleSplit, ContributionSplit.Additive]


theorem exampleFiniteTableUpperBound :
    FiniteTableUpperBound exampleTable exampleClassifier
      exampleSplit.finiteContribution 1 where
  covers := by
    intro a
    simp [exampleTable, exampleClassifier]
  sound := by
    intro a
    norm_num [RatInterval.CaseTable.Sound, exampleTable, exampleClassifier,
      exampleSplit, RatInterval.point, RatInterval.MemR]
  intervalUpper_le := by
    intro c hc
    cases c
    norm_num [exampleTable, RatInterval.point]


theorem exampleTailEnvelopeOn :
    exampleSplit.TailEnvelopeOn (Finset.univ : Finset (Fin 2))
      (fun _ => (1 : ℝ) / 10) := by
  intro a ha
  norm_num [ContributionSplit.TailEnvelopeOn, exampleSplit]


theorem exampleTailEnvelopeSum_le :
    (∑ _a ∈ (Finset.univ : Finset (Fin 2)), ((1 : ℝ) / 10)) ≤
      (1 : ℝ) / 5 := by
  norm_num


theorem exampleTotal_zero_off_support :
    ∀ a : Fin 2, a ∉ (Finset.univ : Finset (Fin 2)) →
      exampleSplit.totalContribution a = 0 := by
  intro a ha
  simp at ha


theorem example_tsum_total_le :
    (∑' a : Fin 2, exampleSplit.totalContribution a) ≤
      ((Finset.univ : Finset (Fin 2)).card : ℝ) * 1 + (1 : ℝ) / 5 := by
  exact ContributionSplit.tsum_total_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    exampleSplit (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ) / 10)
    exampleTotal_zero_off_support exampleSplit_additive exampleFiniteTableUpperBound
    exampleTailEnvelopeOn exampleTailEnvelopeSum_le

end TailSummabilityExample

end Exact3D
end StatMech
