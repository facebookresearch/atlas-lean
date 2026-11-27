/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.AbilityMLE
import Mathlib.Tactic.NormNum

/-! # Regression tests for the 2PL ability MLE criterion -/

open Set MathlibExt.Probability.Statistics.Measurement

-- Two equally difficult Rasch items with opposite responses give a unique maximum at zero.
example :
    let a : Fin 2 → ℝ := fun _ => 1
    let b : Fin 2 → ℝ := fun _ => 0
    let Y : Fin 2 → Bool := fun i => i == 0
    IsMaxOn (twoPLAbilityLogLikelihood a b Y) univ 0 ∧
      ∀ t, IsMaxOn (twoPLAbilityLogLikelihood a b Y) univ t → t = 0 := by
  intro a b Y
  have h := twoPLAbility_mle a b Y (by intro i; norm_num [a])
  rcases h with ⟨_, _, hmax, hunique, _, _, _⟩
  have hz : twoPLAbilityScore a b Y 0 = 0 := by
    norm_num [twoPLAbilityScore, twoPL_score_eq_sum, a, b, Y, Fin.sum_univ_two, Real.sigmoid_zero]
  have hY : (∃ i, Y i = true) ∧ (∃ i, Y i = false) := ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  obtain ⟨tstar, _, htstar⟩ := hunique.mpr hY
  exact ⟨(hmax 0).mpr hz, fun t ht =>
    (htstar t ((hmax t).mp ht)).trans (htstar 0 hz).symm⟩

-- Even with positive unequal discriminations, neither extreme pattern has a finite MLE.
example :
    let a : Fin 2 → ℝ := fun i => (i.val : ℝ) + 1
    let b : Fin 2 → ℝ := fun _ => 0
    (¬ ∃ t, IsMaxOn (twoPLAbilityLogLikelihood a b (fun _ => true)) univ t) ∧
      (¬ ∃ t, IsMaxOn (twoPLAbilityLogLikelihood a b (fun _ => false)) univ t) := by
  intro a b
  have ha : ∀ i, 0 < a i := by intro i; dsimp [a]; positivity
  have ht := (twoPLAbility_mle a b (fun _ => true) ha).2.2.2.2.1
  have hf := (twoPLAbility_mle a b (fun _ => false) ha).2.2.2.2.1
  exact ⟨fun H => by simpa using (ht.mp H).2, fun H => by simpa using (hf.mp H).1⟩
