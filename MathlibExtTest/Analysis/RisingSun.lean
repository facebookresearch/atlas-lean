/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.RisingSun
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Analysis.RisingSun` -/

namespace MathlibExtTest.RisingSun

open Set MathlibExt.Analysis.RisingSunWanted.Analysis.RisingSun

-- Test section: the rising sun set. Every point of `(0, 1)` is lower than `1` under the identity.
example : risingSunSet 0 1 id = Ioo 0 1 :=
  Set.ext fun _ => ⟨fun hx => hx.1, fun hx => ⟨hx, 1, ⟨hx.2.le, le_rfl⟩, hx.2, hx.2⟩⟩

-- A decomposition may pad with empty intervals `(2, 2)`: no condition `c n < d n` is imposed.
example : HasRisingSunDecomposition (Ioo 0 1) id := by
  refine ⟨fun n => if n = 0 then 0 else 2, fun n => if n = 0 then 1 else 2, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_iUnion]
    refine ⟨fun hx => ⟨0, by simpa using hx⟩, fun ⟨n, hn⟩ => ?_⟩
    rcases eq_or_ne n 0 with rfl | h
    · simpa using hn
    · simp [h] at hn
  · intro n _ k _ hnk
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Function.onFun, hnk.symm]
    · simp [Function.onFun, hn]
  · intro n
    dsimp only [id]
    split_ifs <;> norm_num

-- Test section: the rising sun lemma. For `x ↦ x ^ 2` on `[-1, 1]`, every point of `(-1, 1)` is
-- lower than `1`, the set is a single interval with equal endpoint values `f (-1) = f 1`, and the
-- lemma decomposes it.
example : HasRisingSunDecomposition (Ioo (-1) 1) fun x : ℝ => x ^ 2 := by
  have hE : risingSunSet (-1) 1 (fun x : ℝ => x ^ 2) = Ioo (-1) 1 := by
    refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, 1, ⟨hx.2.le, le_rfl⟩, hx.2, ?_⟩⟩
    nlinarith [hx.1, hx.2]
  have h := (rising_sun_lemma (a := -1) (b := 1) (by norm_num)
    (continuous_pow 2).continuousOn).2.2
  rw [hE] at h
  exact h (nonempty_Ioo.2 (by norm_num))

-- An antitone function has an empty rising sun set.
example {a b : ℝ} (hab : a < b) : risingSunSet a b (fun x => -x) = ∅ :=
  ((rising_sun_lemma hab continuous_neg.continuousOn).2.1).2 fun _ _ _ _ hxy => neg_le_neg hxy

-- Conversely, a continuous function with no point of `(a, b)` lower than a later point is
-- antitone on the closed interval, including at the endpoint `a` that the set does not see.
example {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (h : ∀ x ∈ Ioo a b, ∀ t ∈ Ioc x b, f t ≤ f x) : f b ≤ f a := by
  have hE : risingSunSet a b f = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x ⟨hx, t, ht, hxt, hft⟩ =>
      (h x hx t ⟨hxt, ht.2⟩).not_gt hft
  exact ((rising_sun_lemma hab hf).2.1.1 hE) (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
    hab.le

-- Test section: continuity is needed. For the step function equal to `0` on `(-∞, 1/2]` and to
-- `1` after, the rising sun set on `[0, 1]` is `(0, 1/2]`, which is not open.
example : ¬ IsOpen (risingSunSet 0 1 fun x : ℝ => if x ≤ 1 / 2 then 0 else 1) := by
  have hE : risingSunSet 0 1 (fun x : ℝ => if x ≤ 1 / 2 then 0 else 1) = Ioc 0 (1 / 2) := by
    ext x
    constructor
    · rintro ⟨hx, t, ht, hxt, hft⟩
      refine ⟨hx.1, not_lt.1 fun hx2 => ?_⟩
      simp only [hx2.not_ge, (hx2.trans hxt).not_ge, ↓reduceIte, lt_self_iff_false] at hft
    · rintro ⟨hx0, hx2⟩
      refine ⟨⟨hx0, by linarith⟩, 1, ⟨by linarith, le_rfl⟩, by linarith, ?_⟩
      norm_num [hx2]
  rw [hE]
  intro hopen
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen (1 / 2) ⟨by norm_num, le_rfl⟩
  have hmem := hball (Metric.mem_ball.2 (show dist (1 / 2 + ε / 2) (1 / 2) < ε by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε))
  linarith [hmem.2]

end MathlibExtTest.RisingSun
