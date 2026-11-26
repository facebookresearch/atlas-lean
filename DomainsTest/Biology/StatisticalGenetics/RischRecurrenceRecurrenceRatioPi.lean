/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.RischRecurrenceRecurrenceRatioPi

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Tests for multiplicative recurrence-risk ratios

Two identical binary loci each have recurrence-risk ratio `2`, yielding a multilocus ratio
of `4`. The empty-locus model has recurrence-risk ratio `1`.

Source: N. Risch, "Linkage strategies for genetically complex traits. I. Multilocus models",
Am. J. Hum. Genet. 46 (1990) 222–228.
-/

open Finset WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted

namespace DomainsTest.Biology.StatisticalGenetics.RischRecurrenceRecurrenceRatioPi

private noncomputable def genotypeLaw (_g : Bool) : ℝ := 1 / 2

private noncomputable def pairLaw (g h : Bool) : ℝ := if g = h then 1 / 2 else 0

private def penetrance (g : Bool) : ℝ := if g then 1 else 0

private lemma pairLaw_valid : IsPairLaw genotypeLaw pairLaw := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g
    norm_num [genotypeLaw]
  · norm_num [genotypeLaw]
  · intro g h
    cases g <;> cases h <;> norm_num [pairLaw]
  · intro g
    cases g <;> norm_num [genotypeLaw, pairLaw]
  · intro h
    cases h <;> norm_num [genotypeLaw, pairLaw]

private lemma penetrance_bounds (g : Bool) : 0 ≤ penetrance g ∧ penetrance g ≤ 1 := by
  cases g <;> norm_num [penetrance]

private lemma prevalence_pos : 0 < prevalence genotypeLaw penetrance := by
  norm_num [prevalence, genotypeLaw, penetrance]

private lemma locus_ratio : recurrenceRatio genotypeLaw pairLaw penetrance = 2 := by
  norm_num [recurrenceRatio, prevalence, pairAffected, genotypeLaw, pairLaw, penetrance]

example :
    recurrenceRatio (fun g : Bool → Bool => ∏ i, genotypeLaw (g i))
        (fun g h : Bool → Bool => ∏ i, pairLaw (g i) (h i))
        (fun g => ∏ i, penetrance (g i)) = 4 := by
  calc
    recurrenceRatio (fun g : Bool → Bool => ∏ i, genotypeLaw (g i))
        (fun g h : Bool → Bool => ∏ i, pairLaw (g i) (h i))
        (fun g => ∏ i, penetrance (g i)) =
        ∏ _i : Bool, recurrenceRatio genotypeLaw pairLaw penetrance :=
      recurrenceRatio_pi (fun _ => genotypeLaw) (fun _ => pairLaw) (fun _ => penetrance)
        (fun _ => pairLaw_valid) (fun _ => penetrance_bounds) (fun _ => prevalence_pos)
    _ = 4 := by norm_num [locus_ratio]

example : recurrenceRatio (fun _ : Empty → Bool => 1) (fun _ _ => 1) (fun _ => 1) = 1 := by
  simpa using
    recurrenceRatio_pi (G := fun _ : Empty => Bool) (fun _ => genotypeLaw)
      (fun _ => pairLaw) (fun _ => penetrance) (fun i => nomatch i)
      (fun i => nomatch i) (fun i => nomatch i)

end DomainsTest.Biology.StatisticalGenetics.RischRecurrenceRecurrenceRatioPi
