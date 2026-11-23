/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fundamental theorem of contour integration

The contour integral of a complex derivative along a continuously differentiable path is the
difference of its primitive at the endpoints.
-/

public section

namespace MathlibExt.Analysis.Complex.ContourIntegralWanted

open Set

/--
**Fundamental theorem of contour integration.** Let $U \subseteq \mathbb{C}$ be open and let
$F, f : \mathbb{C} \to \mathbb{C}$ be such that $F$ is complex-differentiable at every $z \in U$
with $F'(z) = f(z)$. Let $\gamma : [0, 1] \to \mathbb{C}$ be a path from $a$ to $b$ whose image
lies in $U$ and which is continuously differentiable on $[0, 1]$, with derivative $\gamma'$
(one-sided at the endpoints). If $t \mapsto f(\gamma(t))\,\gamma'(t)$ is integrable on $[0, 1]$,
then $\int_\gamma f(z)\,dz = F(b) - F(a)$, where
$\int_\gamma f(z)\,dz = \int_0^1 f(\gamma(t))\,\gamma'(t)\,dt$.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "contour integrals of continuous functions in ℂ";
L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §1.1 to §1.3 (line integrals).
-/
theorem contourIntegral_of_hasDerivAt
    {F f : ℂ → ℂ} {a b : ℂ} {γ : Path a b} {U : Set ℂ}
    (hU : IsOpen U) (hγU : Set.range γ ⊆ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (h_int : CurveIntegrable (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = F b - F a := by
  have hmem (t : ℝ) : γ.extend t ∈ U := hγU (γ.extend_range.subset (mem_range_self t))
  have hcont : ContinuousOn F U := hU.continuousOn_iff.mpr fun z hz => (hF z hz).continuousAt
  rw [curveIntegral_def]
  calc
    _ = (F ∘ γ.extend) 1 - (F ∘ γ.extend) 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
        (hcont.comp γ.continuous_extend.continuousOn fun t _ => hmem t) ?_ h_int
      intro t ht
      rw [curveIntegralFun_def]
      exact (hF _ (hmem t)).comp t
        ((hγ.differentiableOn one_ne_zero t (mem_Icc_of_Ioo ht)).hasDerivWithinAt.hasDerivAt
          (Icc_mem_nhds ht.1 ht.2))
    _ = F b - F a := by simp only [Function.comp_apply, Path.extend_one, Path.extend_zero]

end MathlibExt.Analysis.Complex.ContourIntegralWanted
