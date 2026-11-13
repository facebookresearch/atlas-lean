/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Euler's identity on the positive orthant

A function positively homogeneous of real degree `r` on the open positive orthant satisfies
Euler's identity `∑ i, x i * ∂ᵢ f x = r * f x` at every orthant point where it is differentiable.

## i. Overview

`IsHomogeneousOnPosOrthant r f` asks `f (t • x) = t ^ r * f x` only for `x` with positive
coordinates and `t > 0`, the domain of Cobb–Douglas and CES functions. Ray homogeneity near
`t = 1` is all that Mathlib's `HasFDerivAt.apply_self_eq_smul_of_eventuallyEq` needs, with
`w t = t ^ r`. `MetaMathlibExt.IsHomogeneousDegreeOne` in
`MathlibExt.Analysis.Calculus.HomogeneousEuler` is the degree-one case on the whole space.

## ii. Main results

* `MetaMathlibExt.IsHomogeneousOnPosOrthant.hasFDerivAt_apply_self`: `L x = r * f x`.
* `MetaMathlibExt.IsHomogeneousOnPosOrthant.sum_mul_fderiv_single`: the coordinate form.

## iii. References

* C. P. Simon and L. Blume, *Mathematics for Economists*, Theorem 20.4.
-/

@[expose] public section

namespace MetaMathlibExt

/-- `f` is positively homogeneous of degree `r` on the open positive orthant: for every `x` with
all coordinates positive and every `t > 0`, `f (t • x) = t ^ r * f x` (real power). Nothing is
assumed outside the orthant. -/
def IsHomogeneousOnPosOrthant {ι : Type*} (r : ℝ) (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x : ι → ℝ, (∀ i, 0 < x i) → ∀ t : ℝ, 0 < t → f (t • x) = t ^ r * f x

/-- **Euler's identity, coordinate-free.** If `f` is homogeneous of degree `r` on the positive
orthant and has derivative `L` at a point `x` of the orthant, then `L x = r * f x`. -/
theorem IsHomogeneousOnPosOrthant.hasFDerivAt_apply_self {ι : Type*} [Fintype ι] {r : ℝ}
    {f : (ι → ℝ) → ℝ} (hf : IsHomogeneousOnPosOrthant r f) {x : ι → ℝ} (hx : ∀ i, 0 < x i)
    {L : (ι → ℝ) →L[ℝ] ℝ} (hL : HasFDerivAt f L x) : L x = r * f x := by
  have hw : HasDerivAt (fun t : ℝ => t ^ r) r 1 := by
    have h := Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := r) (Or.inl one_ne_zero)
    rwa [Real.one_rpow, mul_one] at h
  have hev : (fun t : ℝ => f (t • x)) =ᶠ[nhds 1] fun t => (t ^ r) • f x := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)] with t ht
    show f (t • x) = (t ^ r) • f x
    rw [smul_eq_mul]
    exact hf x hx t ht
  have h := hL.apply_self_eq_smul_of_eventuallyEq hw hev
  rwa [smul_eq_mul] at h

/-- **Euler's identity in coordinates.** `∑ i, x i * ∂ᵢ f x = r * f x`, where
`∂ᵢ f x = fderiv ℝ f x (Pi.single i 1)` is the `i`-th partial derivative. -/
theorem IsHomogeneousOnPosOrthant.sum_mul_fderiv_single {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℝ} {f : (ι → ℝ) → ℝ} (hf : IsHomogeneousOnPosOrthant r f)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) (hd : DifferentiableAt ℝ f x) :
    ∑ i, x i * fderiv ℝ f x (Pi.single i 1) = r * f x := by
  have heuler := hf.hasFDerivAt_apply_self hx hd.hasFDerivAt
  have hsingle : ∀ i, x i • Pi.single i (1 : ℝ) = Pi.single i (x i) := by
    intro i
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have hx2 : (∑ i, x i • Pi.single i (1 : ℝ)) = x :=
    (Finset.sum_congr rfl (fun i _ => hsingle i)).trans (Finset.univ_sum_single x)
  calc ∑ i, x i * fderiv ℝ f x (Pi.single i 1)
      = (fderiv ℝ f x) (∑ i, x i • Pi.single i (1 : ℝ)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
    _ = (fderiv ℝ f x) x := by rw [hx2]
    _ = r * f x := heuler

end MetaMathlibExt
