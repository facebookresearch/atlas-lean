/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ContinuousTuran
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Real

open MetaMathlibExt Set MeasureTheory

namespace MetaMathlibExt.opx_translate

-- A two-point pattern can be placed at the origin, leaving only its displacement vector.
example (n : ℝ) (p q : ℝ × ℝ) : opx n {p, q} = opx n {0, q - p} := by
  simpa only [Set.image_pair, add_neg_cancel, sub_eq_add_neg] using
    (opx_translate n {p, q} (-p)).symm

-- The horizontal gap of this pair exceeds the width of the unit square.
example : ¬ PointSetContainsPattern (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) {(3, 4), (5, 4)} := by
  rintro ⟨f, g, hf, -, hmem⟩
  have hgap := hf (5, 4) (by simp) (3, 4) (by simp) (by norm_num)
  have hlo := (hmem (3, 4) (by simp)).1.1
  have hhi := (hmem (5, 4) (by simp)).1.2
  dsimp at hgap hlo hhi
  linarith

end MetaMathlibExt.opx_translate

namespace MetaMathlibExt.opx_mono_left

-- The square at zero is a singleton, so monotonicity forces every nonpositive side to give zero.
example (P : Set (ℝ × ℝ)) {m : ℝ} (hm : m ≤ 0) : opx m P = 0 := by
  refine le_antisymm ((opx_mono_left P hm).trans ?_) (opx_nonneg m P)
  apply Real.sSup_le _ le_rfl
  rintro _ ⟨S, ⟨_, hS, _⟩, rfl⟩
  have hzero : volume S = 0 := measure_mono_null hS (by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp)
  simp [hzero]

end MetaMathlibExt.opx_mono_left

namespace MetaMathlibExt.opx_mono_of_containsPattern

-- A larger pattern is harder to avoid: a subpattern has the smaller continuous Turán number.
example (n : ℝ) {P Q : Set (ℝ × ℝ)} (hPQ : P ⊆ Q) : opx n P ≤ opx n Q :=
  opx_mono_of_containsPattern n
    ⟨id, id, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => le_rfl, fun _ hp => hPQ hp⟩

-- Stretching a pattern by a factor of two can only increase its continuous Turán number.
example (n : ℝ) (P : Set (ℝ × ℝ)) : opx n P ≤ opx n ((fun p => (2 : ℝ) • p) '' P) := by
  refine opx_mono_of_containsPattern n ⟨fun x => 2 * x, fun y => 2 * y, ?_, ?_, ?_⟩
  · intro p _ q _ hlt
    linarith
  · intro p _ q _ hlt
    linarith
  · intro p hp
    exact ⟨p, hp, by ext <;> simp⟩

end MetaMathlibExt.opx_mono_of_containsPattern

namespace MetaMathlibExt.osat_singleton_and_opx_singleton

-- The point can lie outside the square.
example : osat 1 {(2, 3)} = 0 ∧ opx 1 {(2, 3)} = 0 :=
  osat_singleton_and_opx_singleton 1 (2, 3)

-- Even in an empty ambient square, the empty set witnesses saturation for a singleton.
example (p : ℝ × ℝ) : IsOpxSaturating (-1) {p} ∅ := by
  refine ⟨isOpen_empty, empty_subset _, ?_, ?_⟩
  · rintro ⟨_, _, _, _, h⟩
    exact h p (mem_singleton p)
  · intro S _ hS hne
    obtain ⟨q, hq⟩ := empty_ssubset.mp hne
    have := (hS hq).1.1.trans (hS hq).1.2
    norm_num at this

-- The empty pattern has no saturating set and uses the empty-infimum convention.
example (n : ℝ) : osat n ∅ = 0 := by
  simp [osat, IsOpxSaturating, pointSetContainsPattern_empty]

end MetaMathlibExt.osat_singleton_and_opx_singleton

namespace MetaMathlibExt.opxD_add_lt

-- At the first admissible dimension the coefficient is 8 for n = 2 and ε = 1.
example (P : Set (Fin 2 → ℝ)) :
    opxD 2 2 P ≤ opxD 2 3 P ∧ opxD 2 3 P < opxD 2 2 P + 8 := by
  convert opxD_add_lt (d := 2) le_rfl P (n := 2) (ε := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

-- In one dimension a two-point pattern with gap 4 cannot fit into an interval shorter than 4.
-- The open interval itself then attains the supremum.
private theorem opxD_interval {r : ℝ} (hr : 0 ≤ r) (hr4 : r < 4) :
    opxD 1 r {0, fun _ => 4} = r := by
  let U := univ.pi fun _ : Fin 1 => Ioo 0 r
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hUr : U ⊆ Icc (0 : Fin 1 → ℝ) (fun _ => r) := fun x hx =>
    ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2.le⟩
  unfold opxD
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨U, ⟨hU, hUr, ?_⟩, ?_⟩
    · rintro ⟨f, hgap, himg⟩
      have h := hgap 0 (fun _ => 4) (by simp) 0 (by simp) (by norm_num)
      have hlo := (hUr (himg 0 (by simp))).1 0
      have hhi := (hUr (himg (fun _ => 4) (by simp))).2 0
      change 4 - 0 ≤ f 0 4 - f 0 0 at h
      change 0 ≤ f 0 0 at hlo
      change f 0 4 ≤ r at hhi
      linarith
    · simpa [U] using
        (Real.volume_pi_Ioo_toReal (a := fun _ : Fin 1 => 0) (b := fun _ => r) (fun _ => hr))
  · rintro _ ⟨S, ⟨_, hS, _⟩, rfl⟩
    calc
      _ ≤ volume.real (Icc (0 : Fin 1 → ℝ) (fun _ => r)) :=
        measureReal_mono hS isCompact_Icc.measure_ne_top
      _ = r := by
        simpa [Measure.real] using
          (Real.volume_Icc_pi_toReal (a := (0 : Fin 1 → ℝ)) (b := fun _ => r) (fun _ => hr))

-- The increment equals ε here, so the strict upper bound would fail in dimension one.
example : opxD 1 3 {0, fun _ => 4} = opxD 1 2 {0, fun _ => 4} + 1 := by
  rw [opxD_interval (by norm_num) (by norm_num), opxD_interval (by norm_num) (by norm_num)]
  norm_num

end MetaMathlibExt.opxD_add_lt

namespace MetaMathlibExt.opxD_mono_of_containsPatternD

-- Doubling the gap from four to eight preserves the lower bound from the open interval (0, 2).
example : 2 ≤ opxD 1 2 {0, fun _ => 8} := by
  refine (opxD_add_lt.opxD_interval (r := 2) (by norm_num) (by norm_num)).ge.trans ?_
  apply opxD_mono_of_containsPatternD
  refine ⟨fun _ x => 2 * x, ?_, ?_⟩
  · intro i p hp q hq hlt
    linarith
  · rintro p (rfl | rfl)
    · left
      funext i
      norm_num
    · right
      funext i
      norm_num

end MetaMathlibExt.opxD_mono_of_containsPatternD

namespace MetaMathlibExt.opxD_plus_stack_isTheta

-- With unit arms and unit spacing, an explicit constant bounds the two-layer number by `n^(5/2)`.
example : ∃ C : ℝ, ∀ᶠ n in Filter.atTop, opxD 3 n {v | |v 0| ≤ 1 ∧ |v 1| ≤ 1 ∧
    (v 0 = 0 ∨ v 1 = 0) ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * 1} ≤ C * n ^ (5 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := (opxD_plus_stack_isTheta one_pos one_pos).1.isBigO.bound
  refine ⟨C, ?_⟩
  filter_upwards [hC, Filter.eventually_ge_atTop 0] with n hn hn0
  rwa [Real.norm_of_nonneg (opxD_nonneg _ _ _), Real.norm_of_nonneg (by positivity)] at hn

-- The lower bound makes the three-layer number unbounded.
example {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) Filter.atTop Filter.atTop := by
  have h := (opxD_plus_stack_isTheta hr hc).2.tendsto_norm_atTop_iff.2
    (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 3)))
  exact h.congr fun n => Real.norm_of_nonneg (opxD_nonneg _ _ _)

-- Combining both parts: two layers are negligible against three layers.
example {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ v 2 = i * c}) =o[Filter.atTop]
    (fun n : ℝ => opxD 3 n {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}) := by
  have hpow : (fun n : ℝ => n ^ (5 / 2 : ℝ)) =o[Filter.atTop] (fun n : ℝ => n ^ (8 / 3 : ℝ)) := by
    refine Asymptotics.isLittleO_iff_tendsto' ?_ |>.2 ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn h
      exact absurd h (by positivity)
    · refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [← Real.rpow_sub hn]
      norm_num
  exact (opxD_plus_stack_isTheta hr hc).1.isBigO.trans_isLittleO
    (hpow.trans_isBigO (opxD_plus_stack_isTheta hr hc).2.symm.isBigO)

end MetaMathlibExt.opxD_plus_stack_isTheta
