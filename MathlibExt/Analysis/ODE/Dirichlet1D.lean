/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# The one-dimensional Dirichlet problem

We prove existence of a global `C²` solution of `u'' = f` on the open unit interval
with zero boundary values when `f` is continuous on the closed unit interval, and that, for any
`f`, two such solutions agree on the closed unit interval.

## Main statements

* `dirichlet_1d_exists`: existence. Integrate twice the extension of `f` by its values at the
  endpoints, then subtract a linear term to enforce the boundary condition at `1`.
* `dirichlet_1d_unique`: uniqueness on `[0, 1]`. The difference of two solutions has zero
  second derivative on `(0, 1)`, so it is both convex and concave on `[0, 1]`; as it vanishes at
  both endpoints, it vanishes on `[0, 1]`.

## References

* L. Evans, *Partial Differential Equations*, Ch. 6.
-/

namespace MathlibExt.Analysis.Distribution.Dirichlet1DWanted

/--
**Existence for the one-dimensional Dirichlet problem.** Let $f : \mathbb{R} \to \mathbb{R}$ be
continuous on $[0, 1]$. Then there is a twice continuously differentiable function
$u : \mathbb{R} \to \mathbb{R}$ with $u(0) = u(1) = 0$ and $u''(x) = f(x)$ for every
$x \in (0, 1)$.

Sources: Mathlib `docs/undergrad.yaml`, section "Topology" / "Hilbert spaces" /
entry "H^1_0([0,1]) and its application to the one-dimensional Dirichlet problem";
L. Evans, *Partial Differential Equations*, Ch. 6.
-/
public theorem dirichlet_1d_exists {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u) x = f x := by
  -- Extend by the endpoint values so that both primitives are defined on all of ℝ.
  let g := Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fun x => f x)
  have hg : Continuous g :=
    continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_domRestrict.mp hf)
  let p (x : ℝ) := ∫ t in 0..x, g t
  have hp (x : ℝ) : HasDerivAt p (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hp_diff : Differentiable ℝ p := fun x => (hp x).differentiableAt
  have hp_cont : Continuous p := hp_diff.continuous
  let v (x : ℝ) := ∫ t in 0..x, p t
  have hv (x : ℝ) : HasDerivAt v (p x) x :=
    intervalIntegral.integral_hasDerivAt_right (hp_cont.intervalIntegrable 0 x)
      hp_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hp_cont.continuousAt
  -- The linear correction enforces the boundary condition at 1.
  let u (x : ℝ) := v x - v 1 * x
  have hu (x : ℝ) : HasDerivAt u (p x - v 1) x :=
    (hv x).fun_sub (hasDerivAt_const_mul (v 1))
  have hderiv : deriv u = fun x => p x - v 1 := funext fun x => (hu x).deriv
  have hsecond (x : ℝ) : HasDerivAt (deriv u) (g x) x := by
    rw [hderiv]
    exact (hp x).sub_const (v 1)
  have hsecond_eq : deriv (deriv u) = g := funext fun x => (hsecond x).deriv
  refine ⟨u, ?_, by simp [u, v], by simp [u], ?_⟩
  · change ContDiff ℝ (1 + 1) u
    rw [contDiff_succ_iff_deriv, contDiff_one_iff_deriv]
    refine ⟨fun x => (hu x).differentiableAt, by simp, ?_, ?_⟩
    · exact fun x => (hsecond x).differentiableAt
    · rwa [hsecond_eq]
  · intro x hx
    rw [(hsecond x).deriv]
    exact Set.IccExtend_of_mem _ _ (Set.Ioo_subset_Icc_self hx)

/--
**Uniqueness for the one-dimensional Dirichlet problem.** Let $f : \mathbb{R} \to \mathbb{R}$ be
any function, and let $u_1, u_2 : \mathbb{R} \to \mathbb{R}$ be twice continuously
differentiable functions such that, for $i = 1, 2$, $u_i(0) = u_i(1) = 0$ and
$u_i''(x) = f(x)$ for every $x \in (0, 1)$. Then $u_1(x) = u_2(x)$ for every $x \in [0, 1]$.

Sources: Mathlib `docs/undergrad.yaml`, section "Topology" / "Hilbert spaces" /
entry "H^1_0([0,1]) and its application to the one-dimensional Dirichlet problem";
L. Evans, *Partial Differential Equations*, Ch. 6.
-/
public theorem dirichlet_1d_unique {f : ℝ → ℝ} {u₁ u₂ : ℝ → ℝ}
    (h₁ : ContDiff ℝ 2 u₁ ∧ u₁ 0 = 0 ∧ u₁ 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u₁) x = f x)
    (h₂ : ContDiff ℝ 2 u₂ ∧ u₂ 0 = 0 ∧ u₂ 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u₂) x = f x) :
    ∀ x ∈ Set.Icc 0 1, u₁ x = u₂ x := by
  obtain ⟨hu₁, hu₁0, hu₁1, hf₁⟩ := h₁
  obtain ⟨hu₂, hu₂0, hu₂1, hf₂⟩ := h₂
  -- A `C²` function and its derivative are differentiable everywhere.
  have hd {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (x : ℝ) : HasDerivAt u (deriv u x) x :=
    (hu.differentiable two_ne_zero x).hasDerivAt
  have hdd {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (x : ℝ) :
      HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    (hu.differentiable_deriv_two x).hasDerivAt
  -- On `interior [0, 1] = (0, 1)`, the difference `u₁ - u₂` has second derivative `f - f = 0`,
  -- so it is both convex and concave on `[0, 1]`.
  have hcont : ContinuousOn (u₁ - u₂) (Set.Icc 0 1) :=
    (hu₁.continuous.sub hu₂.continuous).continuousOn
  have h' (x : ℝ) (_ : x ∈ interior (Set.Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u₁ - u₂) (deriv u₁ x - deriv u₂ x) (interior (Set.Icc 0 1)) x :=
    ((hd hu₁ x).sub (hd hu₂ x)).hasDerivWithinAt
  have h'' (x : ℝ) (_ : x ∈ interior (Set.Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (fun y => deriv u₁ y - deriv u₂ y)
        (deriv (deriv u₁) x - deriv (deriv u₂) x) (interior (Set.Icc 0 1)) x :=
    ((hdd hu₁ x).fun_sub (hdd hu₂ x)).hasDerivWithinAt
  have h''0 (x : ℝ) (hx : x ∈ interior (Set.Icc (0 : ℝ) 1)) :
      deriv (deriv u₁) x - deriv (deriv u₂) x = 0 := by
    rw [interior_Icc] at hx
    rw [hf₁ x hx, hf₂ x hx, sub_self]
  have hconv : ConvexOn ℝ (Set.Icc 0 1) (u₁ - u₂) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont h' h''
      fun x hx => (h''0 x hx).ge
  have hconc : ConcaveOn ℝ (Set.Icc 0 1) (u₁ - u₂) :=
    concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) hcont h' h''
      fun x hx => (h''0 x hx).le
  -- Bounded above and below by its endpoint values `0`, the difference vanishes on `[0, 1]`.
  intro x hx
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  rw [← segment_eq_Icc zero_le_one] at hx
  have hle := hconv.le_on_segment h0 h1 hx
  have hge := hconc.ge_on_segment h0 h1 hx
  simp only [Pi.sub_apply, hu₁0, hu₂0, hu₁1, hu₂1, sub_self, max_self, min_self] at hle hge
  exact sub_eq_zero.mp (le_antisymm hle hge)

end MathlibExt.Analysis.Distribution.Dirichlet1DWanted
