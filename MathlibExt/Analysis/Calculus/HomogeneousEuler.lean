/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.Analysis.Calculus.HigherPartials

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Euler's identity for positively homogeneous functions

A differentiable function `f : (Fin n → ℝ) → ℝ` that is positively homogeneous of degree one
satisfies `fderiv ℝ f x x = f x`, and the second derivative of a `C^2` such function annihilates
the position vector.

## i. Overview

The predicate `IsHomogeneousDegreeOne f` asserts `f (t • x) = t * f x` for every `t > 0`.
Differentiating `t ↦ f (t • x)` at `t = 1` gives Euler's identity in coordinate-free form; the
coordinate form expresses the same identity through the axis-slice partial derivatives
`deriv (fun t => f (x + t • Pi.single i 1)) 0`. Differentiating Euler's identity once more, under
an explicit `C^2` hypothesis at the point, gives the differentiated Euler identity: the Hessian of
`f` at `x` maps `x` to `0`.

Differentiability is always an explicit hypothesis. Homogeneity alone does not give
differentiability: the Euclidean norm is homogeneous of degree one but not differentiable at `0`.
The `C^2` hypothesis is local, `ContDiffAt ℝ 2 f x`: a homogeneous function of degree one that is
differentiable at the origin is linear, so a global `C^2` hypothesis only admits linear functions.

No integrability or path-independence statement is made; such statements are only claimed on
explicitly declared domains, and this file declares none.

## ii. Key results

* `IsHomogeneousDegreeOne.fderiv_apply_self`: Euler's identity `fderiv ℝ f x x = f x`.
* `IsHomogeneousDegreeOne.sum_mul_deriv_axis`: Euler's identity in coordinates,
  `∑ i, x i * deriv (fun t => f (x + t • Pi.single i 1)) 0 = f x`.
* `IsHomogeneousDegreeOne.fderiv_fderiv_apply_self`: the differentiated Euler identity
  `fderiv ℝ (fderiv ℝ f) x x = 0`.
* `IsHomogeneousDegreeOne.sum_mul_deriv_deriv_axis`: the differentiated Euler identity in
  coordinates, `∑ i, x i * ∂ⱼ (∂ᵢ f) x = 0` for every coordinate `j`, where `∂ᵢ` is the
  axis-slice partial derivative in direction `i`.

## iii. Table of contents

* A. Positive homogeneity of degree one: `IsHomogeneousDegreeOne`.
* B. Euler's identity: `IsHomogeneousDegreeOne.fderiv_apply_self`,
  `IsHomogeneousDegreeOne.sum_mul_deriv_axis`.
* C. The differentiated Euler identity: `IsHomogeneousDegreeOne.fderiv_fderiv_apply_self`,
  `IsHomogeneousDegreeOne.sum_mul_deriv_deriv_axis`.

## iv. References

* W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., Ch. 9.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open Filter Topology

/-! ## A. Positive homogeneity of degree one -/

/-- `f` is positively homogeneous of degree one: `f (t • x) = t * f x` for every `t > 0`. This is
the hypothesis of Euler's homogeneous function theorem; it does not assert differentiability.
Sources: the hypothesis of Euler's homogeneous function theorem;
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9. -/
def IsHomogeneousDegreeOne {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : Fin n → ℝ, f (t • x) = t * f x

/-! ## B. Euler's identity -/

/-- **Euler's homogeneous function theorem**: a positively homogeneous function of degree one
that is differentiable at `x` satisfies `fderiv ℝ f x x = f x`.
Sources: W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9 (chain rule, Theorem 9.15).

Proof: homogeneity identifies `t ↦ f (t • x)` with `t ↦ t * f x` on a neighbourhood of `t = 1`,
so Mathlib's `HasFDerivAt.apply_self_eq_smul_of_eventuallyEq` applies with `w = id`. -/
theorem IsHomogeneousDegreeOne.fderiv_apply_self {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsHomogeneousDegreeOne f) {x : Fin n → ℝ} (hx : DifferentiableAt ℝ f x) :
    fderiv ℝ f x x = f x := by
  have hhom : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] fun t => id t • f x :=
    (eventually_gt_nhds one_pos).mono fun t ht => hf t ht x
  simpa using hx.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq (hasDerivAt_id 1) hhom

/-- **Euler's homogeneous function theorem**, coordinate form: the coordinates of `x` weighted by
the axis-slice partial derivatives of `f` at `x` sum to `f x`. The `i`-th axis-slice partial
derivative `deriv (fun t => f (x + t • Pi.single i 1)) 0` varies only the `i`-th coordinate.
Sources: W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.

Proof: each axis-slice derivative is `partialDeriv f i x` (`partialDeriv_spec`), which is
`fderiv ℝ f x (Pi.single i 1)` by `partialDeriv_eq_fderiv_apply` from
`MathlibExt.Analysis.Calculus.HigherPartials`; linearity and `pi_eq_sum_univ'` reduce the sum to
`fderiv ℝ f x x`, and `IsHomogeneousDegreeOne.fderiv_apply_self` concludes. -/
theorem IsHomogeneousDegreeOne.sum_mul_deriv_axis {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsHomogeneousDegreeOne f) {x : Fin n → ℝ} (hx : DifferentiableAt ℝ f x) :
    ∑ i, x i * deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 = f x := by
  have hslice (i : Fin n) : deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 =
      fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
    rw [← partialDeriv_spec]
    exact partialDeriv_eq_fderiv_apply f i x hx
  calc ∑ i, x i * deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0
      = fderiv ℝ f x (∑ i, x i • Pi.single i (1 : ℝ)) := by
        simp only [hslice, map_sum, map_smul, smul_eq_mul]
    _ = f x := by rw [← pi_eq_sum_univ' x, hf.fderiv_apply_self hx]

/-! ## C. The differentiated Euler identity -/

private lemma eventually_differentiableAt_and_differentiableAt_fderiv {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : ContDiffAt ℝ 2 f x) :
    (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧ DifferentiableAt ℝ (fderiv ℝ f) x :=
  ⟨(hx.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp),
    (hx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)⟩

private lemma IsHomogeneousDegreeOne.fderiv_fderiv_apply_apply_self {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : IsHomogeneousDegreeOne f) {x : Fin n → ℝ}
    (hx : ContDiffAt ℝ 2 f x) (v : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ f) x v x = 0 := by
  obtain ⟨hdiff, hdd⟩ := eventually_differentiableAt_and_differentiableAt_fderiv hx
  have heuler : (fun y => fderiv ℝ f y y) =ᶠ[𝓝 x] f :=
    hdiff.mono fun y hy => hf.fderiv_apply_self hy
  have h₁ : HasFDerivAt (fun y => fderiv ℝ f y y) (fderiv ℝ f x) x :=
    hdiff.self_of_nhds.hasFDerivAt.congr_of_eventuallyEq heuler
  have h₂ := hdd.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  simpa using congrArg (fun L => L v) (h₂.unique h₁)

/-- **Differentiated Euler identity**, coordinate-free form: if `f` is positively homogeneous of
degree one and `C^2` at `x`, then the second Fréchet derivative of `f` at `x` vanishes once its
first argument is `x`, i.e. `fderiv ℝ (fderiv ℝ f) x x v = 0` for every `v`. Equivalently, by
Mathlib's `iteratedFDeriv_two_apply`, `iteratedFDeriv ℝ 2 f x ![x, v] = 0` for every `v`.
Sources: W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9 (Theorem 9.41).

Proof: differentiate Euler's identity `fderiv ℝ f y y = f y`, valid near `x`, by the product rule
`HasFDerivAt.clm_apply`; this gives `fderiv ℝ (fderiv ℝ f) x v x = 0`, and the symmetry of the
second derivative (`ContDiffAt.isSymmSndFDerivAt`) swaps the two arguments. -/
lemma IsHomogeneousDegreeOne.fderiv_fderiv_apply_self {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsHomogeneousDegreeOne f) {x : Fin n → ℝ} (hx : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ f) x x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [(hx.isSymmSndFDerivAt (by simp)).eq x v]
  exact hf.fderiv_fderiv_apply_apply_self hx v

/-- **Differentiated Euler identity**, coordinate form: if `f` is positively homogeneous of degree
one and `C^2` at `x`, then for every coordinate `j`,
`∑ i, x i * deriv (fun s => deriv (fun t => f (x + s • Pi.single j 1 + t • Pi.single i 1)) 0) 0`
vanishes. The summand is the iterated axis-slice partial derivative of `f` at `x` in direction
`i` (inner slice, variable `t`) and then in direction `j` (outer slice, variable `s`); each slice
varies exactly one coordinate.
Sources: W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.

Proof: the iterated axis-slice derivative is `fderiv ℝ (fderiv ℝ f) x (Pi.single j 1)
(Pi.single i 1)` by Mathlib's `DifferentiableAt.lineDeriv_eq_fderiv` (applied near `x` to `f`
and at `x` to `fun y => fderiv ℝ f y (Pi.single i 1)`) and `HasFDerivAt.clm_apply`; by linearity
the sum is `fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) x`, which vanishes by differentiating Euler's
identity. No symmetry of mixed partials is used.

Relation to `MathlibExt.Analysis.Calculus.HigherPartials`: the summand is
`partialDeriv (partialDeriv f i) j x`. The bridge `partialDeriv_partialDeriv_eq_fderiv_fderiv`
there identifies it with `fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single i 1)` but needs
global `ContDiff ℝ 2 f`; the mixed-partial step of this proof is its localization to
`ContDiffAt ℝ 2 f x`, and the global case follows from this lemma via `ContDiff.contDiffAt`. -/
lemma IsHomogeneousDegreeOne.sum_mul_deriv_deriv_axis {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsHomogeneousDegreeOne f) {x : Fin n → ℝ} (hx : ContDiffAt ℝ 2 f x) (j : Fin n) :
    ∑ i, x i * deriv (fun s : ℝ => deriv (fun t : ℝ =>
      f (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) 0 = 0 := by
  obtain ⟨hdiff, hdd⟩ := eventually_differentiableAt_and_differentiableAt_fderiv hx
  have hline : Tendsto (fun s : ℝ => x + s • Pi.single j (1 : ℝ)) (𝓝 0) (𝓝 x) := by
    have hcont : ContinuousAt (fun s : ℝ => x + s • Pi.single j (1 : ℝ)) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto
  have hmixed (i : Fin n) :
      deriv (fun s : ℝ => deriv (fun t : ℝ =>
        f (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) 0 =
        fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
    have hinner : (fun s : ℝ => deriv (fun t : ℝ =>
        f (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) =ᶠ[𝓝 0]
        fun s => fderiv ℝ f (x + s • Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) :=
      (hline.eventually hdiff).mono fun s hs => hs.lineDeriv_eq_fderiv
    have houter : HasFDerivAt (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ)))
        ((fderiv ℝ (fderiv ℝ f) x).flip (Pi.single i (1 : ℝ))) x := by
      simpa using hdd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) x)
    have hslice : deriv (fun s : ℝ => fderiv ℝ f (x + s • Pi.single j (1 : ℝ))
        (Pi.single i (1 : ℝ))) 0 =
        fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) x (Pi.single j (1 : ℝ)) :=
      houter.differentiableAt.lineDeriv_eq_fderiv
    rw [hinner.deriv_eq, hslice, houter.fderiv, ContinuousLinearMap.flip_apply]
  calc ∑ i, x i * deriv (fun s : ℝ => deriv (fun t : ℝ =>
        f (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) 0
      = fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (∑ i, x i • Pi.single i (1 : ℝ)) := by
        simp only [hmixed, map_sum, map_smul, smul_eq_mul]
    _ = 0 := by
      rw [← pi_eq_sum_univ' x]
      exact hf.fderiv_fderiv_apply_apply_self hx _

end MetaMathlibExt
