/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ContinuousTuran
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
