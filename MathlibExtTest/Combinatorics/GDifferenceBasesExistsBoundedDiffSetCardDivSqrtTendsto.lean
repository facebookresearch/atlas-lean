/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GDifferenceBasesExistsBoundedDiffSetCardDivSqrtTendsto
namespace MathlibExtTest.Combinatorics.GDifferenceBases

open Filter Topology MetaMathlibExt

example : ∃ A : ℕ → Finset ℤ,
    A 0 = ∅ ∧
      (∀ n, A n ⊆ Finset.Icc (1 : ℤ) n ∧
        ∀ x : ℤ, x ≠ 0 → subRepCount (A n) x ≤ 1) ∧
      Tendsto (fun n : ℕ => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) := by
  obtain ⟨A, hA, hlim⟩ := exists_boundedDiffSet_card_div_sqrt_tendsto 1 (by norm_num)
  have hzero : A 0 = ∅ := by
    apply Finset.subset_empty.mp
    simpa using (hA 0).1
  exact ⟨A, hzero, hA, by simpa using hlim⟩

example : ∃ A : ℕ → Finset ℤ,
    (∀ n, A n ⊆ Finset.Icc (1 : ℤ) n ∧
      ∀ x : ℤ, x ≠ 0 → subRepCount (A n) x ≤ 2) ∧
      Tendsto (fun n : ℕ => ((A n).card : ℝ) / Real.sqrt (2 * n)) atTop (𝓝 1) := by
  exact exists_boundedDiffSet_card_div_sqrt_tendsto 2 (by norm_num)

#check @MetaMathlibExt.exists_boundedDiffSet_card_div_sqrt_tendsto
#print axioms MetaMathlibExt.exists_boundedDiffSet_card_div_sqrt_tendsto

end MathlibExtTest.Combinatorics.GDifferenceBases
