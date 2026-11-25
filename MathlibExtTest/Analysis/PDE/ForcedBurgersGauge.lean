/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.ForcedBurgersGauge
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

open Set Real
open scoped ContDiff
open ColeHopf

-- A temporal corner in the potential and cusps in the initial velocity are allowed.
example {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (a x : ℝ) :
    forcedBurgersSolution 3 (fun s _ => |s-1|) (fun y => |sin y|) a t x =
      burgersSolution 3 (fun y => |sin y|) a t x :=
  forcedBurgersSolution_time_potential (by norm_num) hT (by fun_prop)
    ⟨1,fun y => by simpa only [abs_abs] using abs_sin_le_one y⟩ (by fun_prop) ht a x

-- A nonzero spatial forcing survives the addition of a time-only correction.
example (T t a x : ℝ) (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) :
    forcedBurgersSolution 3 (fun s y => sin y+|s-1|) (fun _ => 1) a t x =
      forcedBurgersSolution 3 (fun _ y => sin y) (fun _ => 1) a t x := by
  apply forcedBurgersSolution_add_time_potential (by norm_num) hT continuous_const
    ⟨1,fun _ => by norm_num⟩ (fun _ _ => by fun_prop) ?_ ?_ (by fun_prop) ht a x
  · intro k hk
    interval_cases k <;> simp [iteratedDeriv_succ',Real.deriv_sin]
    all_goals fun_prop
  · intro k hk
    refine ⟨1,fun s hs y => ?_⟩
    interval_cases k <;> simp [iteratedDeriv_succ',Real.deriv_sin]
    · exact abs_sin_le_one y
    · exact abs_cos_le_one y
    · exact abs_sin_le_one y

-- The terminal time is included, with no ordinary endpoint time derivative.
example (a x : ℝ) :
    forcedBurgersSolution 3 (fun s _ => |s-1|) (fun _ => -2) a 3 x =
      burgersSolution 3 (fun _ => -2) a 3 x :=
  forcedBurgersSolution_time_potential (T := 3) (by norm_num) (by norm_num) continuous_const
    ⟨2,fun _ => by norm_num⟩ (by fun_prop) (by constructor <;> norm_num) a x
