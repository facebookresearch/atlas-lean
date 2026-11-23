/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# The one-dimensional Dirichlet problem

We prove existence of a global `C²` solution of `u'' = f` on the open unit interval
with zero boundary values when `f` is continuous on the closed unit interval.
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

end MathlibExt.Analysis.Distribution.Dirichlet1DWanted
