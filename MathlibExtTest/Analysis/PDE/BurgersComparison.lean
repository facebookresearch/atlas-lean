/-
Copyright (c) 2025–2026 the contributors.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersComparison

open ColeHopf

example {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (h : ∀ x, u x ≤ v x) (a t x : ℝ) (ht : 0 ≤ t) :
    burgersSolution ν u a t x ≤ burgersSolution ν v a t x :=
  burgersSolution_mono hu hv hbu hbv hν h a ht x

-- Distinct anchors, nonunit viscosity and a nonsmooth ordered pair.
example (a b t x : ℝ) (ht : 0 ≤ t) :
    burgersSolution (1 / 100) (fun y => -|Real.sin y|) a t x ≤
      burgersSolution (1 / 100) (fun y => |Real.sin y|) b t x := by
  apply burgersSolution_mono_of_anchors
    (show Continuous (fun y : ℝ => -|Real.sin y|) from Real.continuous_sin.abs.neg)
    Real.continuous_sin.abs
    ⟨1, fun y => by simpa only [abs_neg, abs_abs] using Real.abs_sin_le_one y⟩
    ⟨1, fun y => by simpa only [abs_abs] using Real.abs_sin_le_one y⟩ (by norm_num)
    (fun y => by linarith [abs_nonneg (Real.sin y)]) a b ht x

example {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hbu : ∃ M, ∀ x, |u x| ≤ M) (hbv : ∃ M, ∀ x, |v x| ≤ M)
    (h : ∀ x, u x ≤ v x) (a b x : ℝ) :
    burgersSolution 3 u a 0 x ≤ burgersSolution 3 v b 0 x :=
  burgersSolution_mono_of_anchors hu hv hbu hbv (by norm_num) h a b le_rfl x

-- Ordering the velocities reverses the normalized first-moment order.
example {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x, u x ≤ v x) (a y z : ℝ) (hyz : y ≤ z) :
    initialHeatProfile 3 u a y / initialHeatProfile 3 v a y ≤
      initialHeatProfile 3 u a z / initialHeatProfile 3 v a z :=
  initialHeatProfile_ratio_monotone hu hv (by norm_num) h a hyz

-- Equality is preserved even with different normalization anchors.
example {u : ℝ → ℝ} (hu : Continuous u) (hb : ∃ M, ∀ x, |u x| ≤ M)
    (a b t x : ℝ) (ht : 0 ≤ t) : burgersSolution 3 u a t x = burgersSolution 3 u b t x := by
  apply le_antisymm
  · exact burgersSolution_mono_of_anchors hu hu hb hb (by norm_num) (fun _ => le_rfl) a b ht x
  · exact burgersSolution_mono_of_anchors hu hu hb hb (by norm_num) (fun _ => le_rfl) b a ht x
