/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Order.Hom.Basic
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open scoped NNReal Topology
open Filter

/-!
# Hausdorff dimension functions (gauges)

Tushar Das and David Simmons, *Exact dimensions of the prime continued
fraction Cantor set* (arXiv:2305.11829v1), line 211:

> To define these quantities, let ψ:(0,∞) → (0,∞) be a dimension function,
> i.e. a continuous increasing function such that lim_{r→0} ψ(r) = 0.

We extend the source gauge to `ℝ≥0 → ℝ≥0` via `ContinuousOrderHom`,
preserving the source codomain on positive radii and the zero limit.
-/

/-- **Hausdorff dimension function.** A Hausdorff dimension function (gauge) is a continuous,
non-decreasing function $\psi : [0,\infty) \to [0,\infty)$ with $\psi(0) = 0$ and $\psi(r) > 0$
for every $r > 0$. In particular $\psi(r) \to 0$ as $r \to 0^+$.

Source: Das and Simmons, arXiv:2305.11829v1, line 211; the source gauge on $(0,\infty)$ is
extended by $\psi(0) = 0$, and "increasing" is read as non-decreasing. -/
structure HausdorffDimensionFunction : Type extends (ℝ≥0 →Co ℝ≥0) where
  map_zero' : toFun 0 = 0
  map_pos' : ∀ {r : ℝ≥0}, 0 < r → 0 < toFun r

instance : FunLike HausdorffDimensionFunction ℝ≥0 ℝ≥0 where
  coe ψ := ψ.toContinuousOrderHom
  coe_injective ψ φ h := by
    cases ψ
    cases φ
    simp only [HausdorffDimensionFunction.mk.injEq]
    exact ContinuousOrderHom.ext fun r ↦ congrFun h r

instance : ContinuousOrderHomClass HausdorffDimensionFunction ℝ≥0 ℝ≥0 where
  map_monotone ψ := ψ.toContinuousOrderHom.monotone
  map_continuous ψ := ψ.toContinuousOrderHom.continuous_toFun

namespace HausdorffDimensionFunction

@[ext]
theorem ext {ψ₁ ψ₂ : HausdorffDimensionFunction} (h : ∀ x, ψ₁ x = ψ₂ x) : ψ₁ = ψ₂ :=
  DFunLike.ext ψ₁ ψ₂ h

/-- **Continuity of a Hausdorff dimension function.** Every Hausdorff dimension function
$\psi : [0,\infty) \to [0,\infty)$ is continuous. -/
theorem continuous (ψ : HausdorffDimensionFunction) : Continuous (ψ : ℝ≥0 → ℝ≥0) :=
  ψ.toContinuousOrderHom.continuous_toFun

/-- **Monotonicity of a Hausdorff dimension function.** Every Hausdorff dimension function
$\psi : [0,\infty) \to [0,\infty)$ is non-decreasing: if $r \le s$ then $\psi(r) \le \psi(s)$. -/
theorem monotone (ψ : HausdorffDimensionFunction) : Monotone (ψ : ℝ≥0 → ℝ≥0) :=
  ψ.toContinuousOrderHom.monotone

/-- **A Hausdorff dimension function vanishes at zero.** Every Hausdorff dimension function
$\psi$ satisfies $\psi(0) = 0$. -/
@[simp]
theorem map_zero (ψ : HausdorffDimensionFunction) : ψ (0 : ℝ≥0) = 0 :=
  ψ.map_zero'

/-- **A Hausdorff dimension function is positive at positive radii.** If $\psi$ is a Hausdorff
dimension function and $r > 0$ is a real number, then $\psi(r) > 0$. -/
theorem map_pos (ψ : HausdorffDimensionFunction) {r : ℝ≥0} (hr : 0 < r) : 0 < ψ r :=
  ψ.map_pos' hr

/-- **A Hausdorff dimension function vanishes only at zero.** If $\psi$ is a Hausdorff dimension
function and $r \ge 0$, then $\psi(r) = 0$ if and only if $r = 0$. -/
theorem map_eq_zero_iff (ψ : HausdorffDimensionFunction) {r : ℝ≥0} : ψ r = 0 ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    have hrpos : 0 < r := pos_iff_ne_zero.mpr hr
    have hpos : 0 < ψ r := ψ.map_pos hrpos
    exact ne_of_gt hpos h
  · rintro rfl
    exact ψ.map_zero

/-- **A Hausdorff dimension function tends to zero at zero.** Every Hausdorff dimension function
$\psi$ satisfies $\psi(r) \to 0$ as $r \to 0^+$, that is, as $r$ tends to $0$ through positive
values. -/
theorem tendsto_zero (ψ : HausdorffDimensionFunction) :
    Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  have h : Tendsto (ψ : ℝ≥0 → ℝ≥0) (𝓝 (0 : ℝ≥0)) (𝓝 (ψ (0 : ℝ≥0))) :=
    ψ.continuous.continuousAt
  rw [ψ.map_zero] at h
  exact h.mono_left inf_le_left

end HausdorffDimensionFunction
