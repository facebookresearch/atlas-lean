/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.Demiclosedness
public import MathlibExt.Analysis.InnerProductSpace.Opial

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for Opial's property and Browder's demiclosedness principle

Concrete checks on `ℝ`:

* Opial's property for the non-constant weakly convergent sequence
  `u n = 1 + 1 / (n + 1)` with weak limit `1` and competing point `0`;
* Opial's property (norm and squared forms) for constant sequences;
* Browder's demiclosedness principle for the nonexpansive map
  `T z = (z + 1) / 2` along the same non-constant sequence, whose
  residuals `u n - T (u n) = (1 / (n + 1)) / 2` tend to `0`;
* the weakly-sequentially-closed fixed-point set of `T` on constant
  sequences of fixed points.
-/

@[expose] public section

open Filter Topology
open MathlibExt.Analysis.InnerProductSpace.Opial
open MathlibExt.Analysis.InnerProductSpace.Demiclosedness

/-- The sequence `u n = 1 + 1 / (n + 1)` converges weakly to `1` in `ℝ`. -/
theorem weakTendsto_one_add_one_div :
    ∀ f : ℝ →L[ℝ] ℝ,
      Tendsto (fun n : ℕ => f (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (f 1)) := by
  intro f
  have h1 : ∀ n : ℕ, f (1 + 1 / ((n : ℝ) + 1)) =
      f 1 + (1 / ((n : ℝ) + 1)) * f 1 := by
    intro n
    have h2 : f (1 / ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) * f 1 := by
      have hsmul : (1 : ℝ) / ((n : ℝ) + 1) = (1 / ((n : ℝ) + 1)) • (1 : ℝ) := by
        rw [smul_eq_mul, mul_one]
      conv_lhs => rw [hsmul]
      rw [map_smul, smul_eq_mul]
    rw [map_add, h2]
  have hlim : Tendsto (fun n : ℕ => f 1 + (1 / ((n : ℝ) + 1)) * f 1) atTop
      (𝓝 (f 1)) := by
    have h := (tendsto_const_nhds (x := f 1)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul (tendsto_const_nhds (x := f 1)))
    simpa using h
  exact hlim.congr (fun n => (h1 n).symm)

/-- Opial's property for `u n = 1 + 1 / (n + 1)` with weak limit `1` and
competing point `0`. -/
example :
    liminf (fun n : ℕ => ‖(1 + 1 / ((n : ℝ) + 1)) - 1‖) atTop <
      liminf (fun n : ℕ => ‖(1 + 1 / ((n : ℝ) + 1)) - 0‖) atTop :=
  opial_liminf (𝕜 := ℝ) (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) 1 0 one_ne_zero
    weakTendsto_one_add_one_div

/-- Opial's property for the constant sequence at `0`, competing point `1`. -/
example :
    liminf (fun n : ℕ => ‖(fun _ : ℕ => (0 : ℝ)) n - 0‖) atTop <
      liminf (fun n : ℕ => ‖(fun _ : ℕ => (0 : ℝ)) n - 1‖) atTop :=
  opial_liminf (𝕜 := ℝ) (fun _ : ℕ => (0 : ℝ)) 0 1 zero_ne_one
    (fun f => tendsto_const_nhds (x := f 0))

/-- Opial's property, squared form, for the constant sequence at `0`. -/
example :
    liminf (fun n : ℕ => ‖(fun _ : ℕ => (0 : ℝ)) n - 0‖ ^ 2) atTop <
      liminf (fun n : ℕ => ‖(fun _ : ℕ => (0 : ℝ)) n - 1‖ ^ 2) atTop :=
  opial_liminf_sq (𝕜 := ℝ) (fun _ : ℕ => (0 : ℝ)) 0 1 zero_ne_one
    (fun f => tendsto_const_nhds (x := f 0))

/-- The map `T z = (z + 1) / 2` on `ℝ` is nonexpansive. -/
theorem lipschitzWith_one_half_add_half :
    LipschitzWith 1 (fun z : ℝ => (z + 1) / 2) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have h : (x + 1) / 2 - (y + 1) / 2 = (x - y) / 2 := by ring
  rw [h, norm_div]
  have h2 : ‖(2 : ℝ)‖ = 2 := by norm_num [Real.norm_eq_abs]
  rw [h2]
  have hnn := norm_nonneg (x - y)
  linarith

/-- Browder's demiclosedness principle for `T z = (z + 1) / 2` along
`u n = 1 + 1 / (n + 1)`: the residuals tend to `0`, so `T 1 = 1`. -/
example : (fun z : ℝ => (z + 1) / 2) 1 = 1 := by
  apply demiclosedness_of_lipschitzWith_one (𝕜 := ℝ) (fun z : ℝ => (z + 1) / 2)
    lipschitzWith_one_half_add_half (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) 1
    weakTendsto_one_add_one_div
  have hres : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) / 2) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (2 : ℝ)
    simpa using h
  refine hres.congr (fun n => ?_)
  have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The fixed point `1` of `T z = (z + 1) / 2` is recovered from the
constant sequence of fixed points. -/
example : (fun z : ℝ => (z + 1) / 2) 1 = 1 := by
  apply fixedPoint_of_weakly_tendsto_of_forall_fixedPoint (𝕜 := ℝ)
    (fun z : ℝ => (z + 1) / 2) lipschitzWith_one_half_add_half
    (fun _ : ℕ => (1 : ℝ)) 1 (fun f => tendsto_const_nhds (x := f 1))
  intro n
  simp

#print axioms opial_liminf
#print axioms opial_liminf_sq
#print axioms demiclosedness_of_lipschitzWith_one
#print axioms fixedPoint_of_weakly_tendsto_of_forall_fixedPoint
