/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.FK.PressureDiff
import Code.FK.IVPressureConvex

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK










theorem cdl_limit_convexOn {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (glim : ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (glim x))) :
    ConvexOn ℝ univ glim :=
  ivp2_convexOn_of_tendsto gn glim hconv hlim











theorem cdl_slope_tendsto {κ : Type*} {l : Filter κ}
    (gn : κ → ℝ → ℝ) (glim : ℝ → ℝ)
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (glim x))) (a b : ℝ) :
    Tendsto (fun i => slope (gn i) a b) l (𝓝 (slope glim a b)) := by
  simp only [slope_def_field]
  exact ((hlim b).sub (hlim a)).div_const _







variable {g : ℝ → ℝ}




theorem cdl_hasDerivWithinAt_rightDeriv (hg : ConvexOn ℝ univ g) (t : ℝ) :
    HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t := by
  unfold pressureRightDeriv
  exact hg.hasDerivWithinAt_rightDeriv_of_mem_interior (by rw [interior_univ]; trivial)




theorem cdl_hasDerivWithinAt_leftDeriv (hg : ConvexOn ℝ univ g) (t : ℝ) :
    HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t := by
  unfold pressureLeftDeriv
  exact hg.hasDerivWithinAt_leftDeriv_of_mem_interior (by rw [interior_univ]; trivial)












theorem cdl_rightDeriv_tendsto_slope (hg : ConvexOn ℝ univ g) (t : ℝ) :
    Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)) := by
  have h := (cdl_hasDerivWithinAt_rightDeriv hg t)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h
  exact h





theorem cdl_leftDeriv_tendsto_slope (hg : ConvexOn ℝ univ g) (t : ℝ) :
    Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)) := by
  have h := (cdl_hasDerivWithinAt_leftDeriv hg t)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h
  exact h




theorem cdl_rightDeriv_eq_sInf_slope (hg : ConvexOn ℝ univ g) (t : ℝ) :
    pressureRightDeriv g t = sInf (slope g t '' {y | t < y}) := by
  unfold pressureRightDeriv
  have h := hg.rightDeriv_eq_sInf_slope_of_mem_interior (x := t) (by rw [interior_univ]; trivial)
  simpa using h




theorem cdl_leftDeriv_eq_sSup_slope (hg : ConvexOn ℝ univ g) (t : ℝ) :
    pressureLeftDeriv g t = sSup (slope g t '' {y | y < t}) := by
  unfold pressureLeftDeriv
  have h := hg.leftDeriv_eq_sSup_slope_of_mem_interior (x := t) (by rw [interior_univ]; trivial)
  simpa using h









theorem cdl_leftDeriv_le_rightDeriv (hg : ConvexOn ℝ univ g) (t : ℝ) :
    pressureLeftDeriv g t ≤ pressureRightDeriv g t :=
  pressureLeftDeriv_le_rightDeriv hg t


theorem cdl_rightDeriv_monotone (hg : ConvexOn ℝ univ g) :
    Monotone (pressureRightDeriv g) :=
  pressureRightDeriv_monotone hg


theorem cdl_leftDeriv_monotone (hg : ConvexOn ℝ univ g) :
    Monotone (pressureLeftDeriv g) :=
  pressureLeftDeriv_monotone hg




theorem cdl_rightDeriv_le_leftDeriv_of_lt (hg : ConvexOn ℝ univ g) {z x : ℝ} (hzx : z < x) :
    pressureRightDeriv g z ≤ pressureLeftDeriv g x :=
  pressureRightDeriv_le_leftDeriv_of_lt hg hzx





theorem cdl_countable_leftDeriv_ne_rightDeriv (hg : ConvexOn ℝ univ g) :
    {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable :=
  countable_leftDeriv_ne_rightDeriv hg































theorem cdl_convexDerivLimit {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (g : ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x))) :
    ConvexOn ℝ univ g
      ∧ (∀ t, HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t)
      ∧ (∀ t, HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t)
      ∧ (∀ t, Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)))
      ∧ (∀ t, Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)))
      ∧ (∀ a b, Tendsto (fun i => slope (gn i) a b) l (𝓝 (slope g a b)))
      ∧ (∀ t, pressureLeftDeriv g t ≤ pressureRightDeriv g t)
      ∧ Monotone (pressureRightDeriv g)
      ∧ Monotone (pressureLeftDeriv g)
      ∧ {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable := by
  have hg : ConvexOn ℝ univ g := cdl_limit_convexOn gn g hconv hlim
  exact ⟨hg,
    cdl_hasDerivWithinAt_rightDeriv hg,
    cdl_hasDerivWithinAt_leftDeriv hg,
    cdl_rightDeriv_tendsto_slope hg,
    cdl_leftDeriv_tendsto_slope hg,
    cdl_slope_tendsto gn g hlim,
    cdl_leftDeriv_le_rightDeriv hg,
    cdl_rightDeriv_monotone hg,
    cdl_leftDeriv_monotone hg,
    cdl_countable_leftDeriv_ne_rightDeriv hg⟩

end FK

end StatMech
