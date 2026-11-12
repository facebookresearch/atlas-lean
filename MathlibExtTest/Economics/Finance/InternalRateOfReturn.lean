/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.InternalRateOfReturn

/-!
# Tests for the internal rate of return

The flows `(-100, 110)` have the unique internal rate `1/10`; the non-conventional flows
`(-1, 5, -6)` have the two internal rates `1` and `2`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.InternalRateOfReturn

open _root_.Economics.Finance

def c1 : ℕ → ℝ := fun k => if k = 0 then -100 else 110

def c2 : ℕ → ℝ := fun k => if k = 0 then -1 else if k = 1 then 5 else -6

theorem irr_c1 : IsIRR c1 1 (1 / 10) := by
  have e1 : (∑ k ∈ Finset.range (1 + 1), c1 k / (1 + (1 / 10 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 1, c1 k / (1 + (1 / 10 : ℝ)) ^ k)
        + c1 1 / (1 + (1 / 10 : ℝ)) ^ 1 :=
    Finset.sum_range_succ _ 1
  have e0 : (∑ k ∈ Finset.range (0 + 1), c1 k / (1 + (1 / 10 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 0, c1 k / (1 + (1 / 10 : ℝ)) ^ k)
        + c1 0 / (1 + (1 / 10 : ℝ)) ^ 0 :=
    Finset.sum_range_succ _ 0
  rw [Finset.sum_range_zero] at e0
  refine ⟨by norm_num, ?_⟩
  show (∑ k ∈ Finset.range (1 + 1), c1 k / (1 + (1 / 10 : ℝ)) ^ k) = 0
  rw [e1]
  show (∑ k ∈ Finset.range (0 + 1), c1 k / (1 + (1 / 10 : ℝ)) ^ k)
      + c1 1 / (1 + (1 / 10 : ℝ)) ^ 1 = 0
  rw [e0]
  norm_num [c1]

theorem unique_c1 : ∀ r, IsIRR c1 1 r → r = 1 / 10 := by
  intro r hr
  have h0 : c1 0 < 0 := by norm_num [c1]
  have hnn : ∀ k ∈ Finset.Icc 1 1, 0 ≤ c1 k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : k = 1 := by omega
    subst hk1
    norm_num [c1]
  have hpos : ∃ k ∈ Finset.Icc 1 1, 0 < c1 k := ⟨1, by simp, by norm_num [c1]⟩
  have huniq := existsUnique_isIRR h0 hnn hpos
  exact ExistsUnique.unique huniq hr irr_c1

theorem irr_c2_1 : IsIRR c2 2 1 := by
  have e2 : (∑ k ∈ Finset.range (2 + 1), c2 k / (1 + (1 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 2, c2 k / (1 + (1 : ℝ)) ^ k)
        + c2 2 / (1 + (1 : ℝ)) ^ 2 :=
    Finset.sum_range_succ _ 2
  have e1 : (∑ k ∈ Finset.range (1 + 1), c2 k / (1 + (1 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 1, c2 k / (1 + (1 : ℝ)) ^ k)
        + c2 1 / (1 + (1 : ℝ)) ^ 1 :=
    Finset.sum_range_succ _ 1
  have e0 : (∑ k ∈ Finset.range (0 + 1), c2 k / (1 + (1 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 0, c2 k / (1 + (1 : ℝ)) ^ k)
        + c2 0 / (1 + (1 : ℝ)) ^ 0 :=
    Finset.sum_range_succ _ 0
  rw [Finset.sum_range_zero] at e0
  refine ⟨by norm_num, ?_⟩
  show (∑ k ∈ Finset.range (2 + 1), c2 k / (1 + (1 : ℝ)) ^ k) = 0
  rw [e2]
  show (∑ k ∈ Finset.range (1 + 1), c2 k / (1 + (1 : ℝ)) ^ k)
      + c2 2 / (1 + (1 : ℝ)) ^ 2 = 0
  rw [e1]
  show (∑ k ∈ Finset.range (0 + 1), c2 k / (1 + (1 : ℝ)) ^ k)
      + c2 1 / (1 + (1 : ℝ)) ^ 1 + c2 2 / (1 + (1 : ℝ)) ^ 2 = 0
  rw [e0]
  norm_num [c2]

theorem irr_c2_2 : IsIRR c2 2 2 := by
  have e2 : (∑ k ∈ Finset.range (2 + 1), c2 k / (1 + (2 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 2, c2 k / (1 + (2 : ℝ)) ^ k)
        + c2 2 / (1 + (2 : ℝ)) ^ 2 :=
    Finset.sum_range_succ _ 2
  have e1 : (∑ k ∈ Finset.range (1 + 1), c2 k / (1 + (2 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 1, c2 k / (1 + (2 : ℝ)) ^ k)
        + c2 1 / (1 + (2 : ℝ)) ^ 1 :=
    Finset.sum_range_succ _ 1
  have e0 : (∑ k ∈ Finset.range (0 + 1), c2 k / (1 + (2 : ℝ)) ^ k)
      = (∑ k ∈ Finset.range 0, c2 k / (1 + (2 : ℝ)) ^ k)
        + c2 0 / (1 + (2 : ℝ)) ^ 0 :=
    Finset.sum_range_succ _ 0
  rw [Finset.sum_range_zero] at e0
  refine ⟨by norm_num, ?_⟩
  show (∑ k ∈ Finset.range (2 + 1), c2 k / (1 + (2 : ℝ)) ^ k) = 0
  rw [e2]
  show (∑ k ∈ Finset.range (1 + 1), c2 k / (1 + (2 : ℝ)) ^ k)
      + c2 2 / (1 + (2 : ℝ)) ^ 2 = 0
  rw [e1]
  show (∑ k ∈ Finset.range (0 + 1), c2 k / (1 + (2 : ℝ)) ^ k)
      + c2 1 / (1 + (2 : ℝ)) ^ 1 + c2 2 / (1 + (2 : ℝ)) ^ 2 = 0
  rw [e0]
  norm_num [c2]

theorem not_unique_c2 : ¬∃! r, IsIRR c2 2 r := by
  intro h
  have h12 : (1 : ℝ) = 2 := ExistsUnique.unique h irr_c2_1 irr_c2_2
  norm_num at h12

end MathlibExtTest.Economics.Finance.InternalRateOfReturn
