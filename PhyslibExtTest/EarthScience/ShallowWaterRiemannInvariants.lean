/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWaterRiemannInvariants
import PhyslibExt.EarthScience.ShallowWaterNonlinear
import PhyslibExt.EarthScience.ShallowWaterCharacteristics
import MathlibExt.Analysis.ODE.ContinuumBalances
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Shallow-water Riemann-invariant checks

Consumers of `PhyslibExt.EarthScience.ShallowWaterRiemannInvariants`:
the conservative-to-primitive producer chain, the characteristic-speed
identification, the constant state, a nonzero witness whose mass equation
is used non-trivially, both mismatched-sign failures, the negative-gravity
control, and the nonpositive-depth control at zero and negative depth.

## i. Overview

These are elaboration and boundary checks, not new results. The nonzero
witness at `(t, x)` has depth and velocity `1`, partials
`hₜ = -1`, `hₓ = 0`, `uₜ = -1`, `uₓ = 1`, and gravity `1`, so the mass
equation `-1 + 1 * 1 = 0` is not the trivial `0 = 0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Producer chains and the constant state
- B. Nonzero witness and sign pairing
- C. Gravity and depth controls

## iv. References

- `PhyslibExt.EarthScience.ShallowWaterRiemannInvariants`
- `PhyslibExt.EarthScience.ShallowWaterNonlinear`
- `PhyslibExt.EarthScience.ShallowWaterCharacteristics`
-/

open EarthScience MathlibExt.Analysis.ODE.ContinuumBalances

/-! ## A. Producer chains and the constant state -/

/-- A conservative solution at a wet point feeds the transport theorem
through the conservative-primitive equivalence. -/
example
    {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ}
    (hg : 0 < g) (hpos : 0 < h t x)
    (dht : HasDerivAt (fun τ => h τ x) hₜ t)
    (dhx : HasDerivAt (h t) hₓ x)
    (dut : HasDerivAt (fun τ => u τ x) uₜ t)
    (dux : HasDerivAt (u t) uₓ x)
    (hcons : localConservation h (fun τ y => h τ y * u τ y) 0 t x ∧
      localConservation (fun τ y => h τ y * u τ y)
        (fun τ y => h τ y * u τ y ^ 2 + g * h τ y ^ 2 / 2) 0 t x) :
    deriv (fun τ => u τ x + 2 * √(g * h τ x)) t +
        (u t x + √(g * h t x)) *
          deriv (fun y => u t y + 2 * √(g * h t y)) x = 0 ∧
      deriv (fun τ => u τ x - 2 * √(g * h τ x)) t +
        (u t x - √(g * h t x)) *
          deriv (fun y => u t y - 2 * √(g * h t y)) x = 0 :=
  shallow_water_riemann_invariant_transport hg hpos dht dhx dut dux
    ((shallow_water_conservative_iff_primitive hpos dht dhx dut dux).mp hcons)

/-- The transport speeds are the characteristic speeds `u ± √(g h)`. -/
example
    {h u : ℝ → ℝ → ℝ} {g t x : ℝ}
    (hg : 0 < g) (hpos : 0 < h t x) :
    (shallowWaterPrimitiveMatrix g (h t x) (u t x)).charpoly.roots =
      {u t x - √(g * h t x), u t x + √(g * h t x)} :=
  shallow_water_characteristic_speeds (mul_pos hg hpos).le

/-- The constant state, as an instance of the transport theorem. -/
example {g H U t x : ℝ} (hg : 0 < g) (hH : 0 < H) :
    deriv (fun τ => (fun _ _ => U) τ x + 2 * √(g * (fun _ _ => H) τ x)) t +
        ((fun _ _ => U) t x + √(g * (fun _ _ => H) t x)) *
          deriv (fun y => (fun _ _ => U) t y + 2 * √(g * (fun _ _ => H) t y)) x = 0 ∧
      deriv (fun τ => (fun _ _ => U) τ x - 2 * √(g * (fun _ _ => H) τ x)) t +
        ((fun _ _ => U) t x - √(g * (fun _ _ => H) t x)) *
          deriv (fun y => (fun _ _ => U) t y - 2 * √(g * (fun _ _ => H) t y)) x = 0 :=
  shallow_water_riemann_invariant_transport (h := fun _ _ => H) (u := fun _ _ => U)
    (hₜ := 0) (hₓ := 0) (uₜ := 0) (uₓ := 0) hg hH (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) (hasDerivAt_const _ _) (by constructor <;> ring)

/-! ## B. Nonzero witness and sign pairing -/

/-- Nonzero witness with `h τ y = 1 - (τ - t)` and
`u τ y = 1 + (y - x) - (τ - t)` at gravity `1`: the paired transports
vanish, the operator derivatives take the forced values
`-2, 1, 0, 1`, and both mismatched pairings are nonzero (`-2` and `2`). -/
example (t x : ℝ) :
    deriv (fun τ => (1 + (x - x) - (τ - t)) + 2 * √(1 * (1 - (τ - t)))) t = -2 ∧
    deriv (fun y => (1 + (y - x) - (t - t)) + 2 * √(1 * (1 - (t - t)))) x = 1 ∧
    deriv (fun τ => (1 + (x - x) - (τ - t)) - 2 * √(1 * (1 - (τ - t)))) t = 0 ∧
    deriv (fun y => (1 + (y - x) - (t - t)) - 2 * √(1 * (1 - (t - t)))) x = 1 ∧
    deriv (fun τ => (1 + (x - x) - (τ - t)) + 2 * √(1 * (1 - (τ - t)))) t +
      (1 - √(1 * (1 : ℝ))) *
        deriv (fun y => (1 + (y - x) - (t - t)) + 2 * √(1 * (1 - (t - t)))) x = -2 ∧
    deriv (fun τ => (1 + (x - x) - (τ - t)) - 2 * √(1 * (1 - (τ - t)))) t +
      (1 + √(1 * (1 : ℝ))) *
        deriv (fun y => (1 + (y - x) - (t - t)) - 2 * √(1 * (1 - (t - t)))) x = 2 := by
  have dht : HasDerivAt (fun τ : ℝ => 1 - (τ - t)) (-1) t := by
    simpa using ((hasDerivAt_id t).sub_const t).const_sub 1
  have dhx : HasDerivAt (fun _ : ℝ => 1 - (t - t)) 0 x :=
    hasDerivAt_const x _
  have dut : HasDerivAt (fun τ : ℝ => 1 + (x - x) - (τ - t)) (-1) t := by
    simpa using ((hasDerivAt_id t).sub_const t).const_sub (1 + (x - x))
  have dux : HasDerivAt (fun y : ℝ => 1 + (y - x) - (t - t)) 1 x :=
    (((hasDerivAt_id x).sub_const x).const_add 1).sub_const (t - t)
  have sT : HasDerivAt (fun τ : ℝ => √(1 * (1 - (τ - t))))
      (1 * (-1) / (2 * √(1 * (1 - (t - t))))) t :=
    (dht.const_mul 1).sqrt (by norm_num)
  have sX : HasDerivAt (fun y : ℝ => √(1 * (1 - (t - t))))
      (1 * 0 / (2 * √(1 * (1 - (t - t))))) x :=
    (dhx.const_mul 1).sqrt (by norm_num)
  have pT : HasDerivAt (fun τ : ℝ => (1 + (x - x) - (τ - t)) + 2 * √(1 * (1 - (τ - t)))) _ t :=
    dut.fun_add (sT.const_mul 2)
  have pX : HasDerivAt (fun y : ℝ => (1 + (y - x) - (t - t)) + 2 * √(1 * (1 - (t - t)))) _ x :=
    dux.fun_add (sX.const_mul 2)
  have mT : HasDerivAt (fun τ : ℝ => (1 + (x - x) - (τ - t)) - 2 * √(1 * (1 - (τ - t)))) _ t :=
    dut.fun_sub (sT.const_mul 2)
  have mX : HasDerivAt (fun y : ℝ => (1 + (y - x) - (t - t)) - 2 * √(1 * (1 - (t - t)))) _ x :=
    dux.fun_sub (sX.const_mul 2)
  rw [pT.deriv, pX.deriv, mT.deriv, mX.deriv]
  norm_num [Real.sqrt_one]

/-- The same witness satisfies the primitive pair non-trivially, so the
transport theorem applies to it. -/
example (t x : ℝ) :
    deriv (fun τ => (fun τ y => 1 + (y - x) - (τ - t)) τ x +
        2 * √(1 * (fun τ _y => 1 - (τ - t)) τ x)) t +
        ((fun τ y => 1 + (y - x) - (τ - t)) t x +
          √(1 * (fun τ _y => 1 - (τ - t)) t x)) *
          deriv (fun y => (fun τ y => 1 + (y - x) - (τ - t)) t y +
            2 * √(1 * (fun τ _y => 1 - (τ - t)) t y)) x = 0 ∧
      deriv (fun τ => (fun τ y => 1 + (y - x) - (τ - t)) τ x -
          2 * √(1 * (fun τ _y => 1 - (τ - t)) τ x)) t +
        ((fun τ y => 1 + (y - x) - (τ - t)) t x -
          √(1 * (fun τ _y => 1 - (τ - t)) t x)) *
          deriv (fun y => (fun τ y => 1 + (y - x) - (τ - t)) t y -
            2 * √(1 * (fun τ _y => 1 - (τ - t)) t y)) x = 0 := by
  have dht : HasDerivAt (fun τ => (fun τ _y => 1 - (τ - t)) τ x) (-1) t := by
    show HasDerivAt (fun τ : ℝ => 1 - (τ - t)) (-1) t
    simpa using ((hasDerivAt_id t).sub_const t).const_sub 1
  have dhx : HasDerivAt ((fun τ _y => 1 - (τ - t)) t) 0 x := by
    show HasDerivAt (fun _ : ℝ => 1 - (t - t)) 0 x
    exact hasDerivAt_const x _
  have dut : HasDerivAt (fun τ => (fun τ y => 1 + (y - x) - (τ - t)) τ x) (-1) t := by
    show HasDerivAt (fun τ : ℝ => 1 + (x - x) - (τ - t)) (-1) t
    simpa using ((hasDerivAt_id t).sub_const t).const_sub (1 + (x - x))
  have dux : HasDerivAt ((fun τ y => 1 + (y - x) - (τ - t)) t) 1 x := by
    show HasDerivAt (fun y : ℝ => 1 + (y - x) - (t - t)) 1 x
    exact (((hasDerivAt_id x).sub_const x).const_add 1).sub_const (t - t)
  exact shallow_water_riemann_invariant_transport
    (h := fun τ _y => 1 - (τ - t)) (u := fun τ y => 1 + (y - x) - (τ - t)) (g := 1) one_pos
    (by show (0 : ℝ) < 1 - (t - t); norm_num)
    dht dhx dut dux
    (by show (-1 : ℝ) + (1 + (x - x) - (t - t)) * 0 + (1 - (t - t)) * 1 = 0 ∧
          (-1 : ℝ) + (1 + (x - x) - (t - t)) * 1 + 1 * 0 = 0
        constructor <;> ring)

/-! ## C. Gravity and depth controls -/

/-- Negative gravity: with `g = -1`, `h τ y = 1 + (y - x)` and
`u τ y = τ - t`, the slice witnesses and primitive pair hold at `(t, x)`,
but the plus transport equals `1`, not `0`. -/
example (t x : ℝ) :
    HasDerivAt (fun _τ : ℝ => 1 + (x - x)) 0 t ∧
    HasDerivAt (fun y : ℝ => 1 + (y - x)) 1 x ∧
    HasDerivAt (fun τ : ℝ => τ - t) 1 t ∧
    HasDerivAt (fun _ : ℝ => t - t) 0 x ∧
    ((0 : ℝ) + (t - t) * 1 + (1 + (x - x)) * 0 = 0 ∧
      (1 : ℝ) + (t - t) * 0 + (-1) * 1 = 0) ∧
    deriv (fun τ => (τ - t) + 2 * √((-1) * (1 + (x - x)))) t +
      ((t - t) + √((-1) * (1 + (x - x)))) *
        deriv (fun y => (t - t) + 2 * √((-1) * (1 + (y - x)))) x = 1 := by
  have hsqrt : √((-1 : ℝ) * (1 + (x - x))) = 0 := by
    rw [show (1 : ℝ) + (x - x) = 1 by ring]
    exact Real.sqrt_eq_zero_of_nonpos (by norm_num)
  have hT : deriv (fun τ : ℝ => (τ - t) + 2 * √((-1) * (1 + (x - x)))) t = 1 := by
    have h : HasDerivAt (fun τ : ℝ => (τ - t) + 2 * √((-1 : ℝ) * (1 + (x - x)))) 1 t := by
      simpa using ((hasDerivAt_id t).sub_const t).add_const
        (2 * √((-1 : ℝ) * (1 + (x - x))))
    exact h.deriv
  refine ⟨hasDerivAt_const t _, by simpa using ((hasDerivAt_id x).sub_const x).const_add 1,
    by simpa using (hasDerivAt_id t).sub_const t, hasDerivAt_const x _,
    ⟨by ring, by ring⟩, ?_⟩
  rw [hT, hsqrt]
  simp

/-- The nonpositive-depth control at depth `0`. -/
example (t x : ℝ) : ∃ h _u : ℝ → ℝ → ℝ, h t x = 0 := by
  obtain ⟨h, u, -, -, -, -, hh, -⟩ :=
    exists_nonpos_depth_primitive_not_riemann_transport (g := 1) one_pos t x 0 le_rfl
  exact ⟨h, u, hh⟩

/-- The nonpositive-depth control at depth `-1`. -/
example (t x : ℝ) : ∃ h _u : ℝ → ℝ → ℝ, h t x = -1 := by
  obtain ⟨h, u, -, -, -, -, hh, -⟩ :=
    exists_nonpos_depth_primitive_not_riemann_transport (g := 1) one_pos t x (-1) (by norm_num)
  exact ⟨h, u, hh⟩
