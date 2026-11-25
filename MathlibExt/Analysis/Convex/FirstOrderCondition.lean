/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_95.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029; MA-ProofBench, L. Pu et al., arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

The adapted portion is the statement of `convexOn_iff_forall_le_add_fderivWithin` (formerly the
`theorem_wanted` of the same name in `WantedExt/Analysis/FunctionalAnalysis/`), now proved.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Module

/-!
# First-order conditions for convexity and optimality

For a function `f` on a real normed space that is differentiable at `a`, convexity on a set
containing `a` gives the tangent-plane (first-order) inequality `f a + Df(a)(x - a) ≤ f x`; and
conversely a function lying above an affine minorant that is exact at every point of a convex set
is convex there. On an open convex set on which `f` is differentiable this is an equivalence. The
first-order condition gives the optimality criterion for convex problems: a point `a` of a convex
feasible set minimizes a convex differentiable `f` there iff `Df(a)(x - a) ≥ 0` for every
feasible `x`, and in particular a stationary point is a global minimizer.

## Main results

* `add_fderiv_le_of_convexOn`: the first-order condition (Boyd–Vandenberghe, *Convex
  Optimization*, §3.1.3, eq. (3.2)).
* `convexOn_of_forall_add_le`: a function with a supporting affine minorant at every point of a
  convex set is convex there.
* `convexOn_iff_forall_add_fderiv_le`: the equivalence on an open convex set.
* `isMinOn_iff_forall_fderiv_nonneg`: the optimality criterion for convex problems
  (Boyd–Vandenberghe §4.2.3, eq. (4.21)).
* `isMinOn_of_hasFDerivAt_eq_zero`: stationary points of convex functions are global minimizers.
* `convexOn_iff_forall_le_add_fderivWithin`: the MA-ProofBench `C²` formulation.

## Relation to `MathlibExt.Analysis.Convex.SupportingGradient`

That module states the first-order condition for `fderiv ℝ f x`, as `isSupportingGradient_fderiv`
from Mathlib's `ConvexOn.add_fderiv_sub_le`; `add_fderiv_le_of_convexOn` is the same inequality
for a derivative given by `HasFDerivAt`. Its `isMinOn_of_convexOn_of_fderiv_nonneg` is the
sufficient direction of `isMinOn_iff_forall_fderiv_nonneg`. The converse direction, the
characterization of convexity and the `C²` formulation are only here.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.FirstOrderCondition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of `f` along the segment from `a` towards `x`, at the starting point. -/
private theorem hasDerivAt_line {f : E → ℝ} {f' : E →L[ℝ] ℝ} {a : E} (hf : HasFDerivAt f f' a)
    (x : E) : HasDerivAt (fun t : ℝ => f (a + t • (x - a))) (f' (x - a)) 0 := by
  have hpath : HasDerivAt (fun t : ℝ => a + t • (x - a)) (x - a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add a
  have hf0 : HasFDerivAt f f' (a + (0 : ℝ) • (x - a)) := by simpa using hf
  simpa [Function.comp_def] using (hf0.comp (0 : ℝ) hpath.hasFDerivAt).hasDerivAt

/-- The right-hand difference quotients of `f` along the segment from `a` to `x` converge to the
directional derivative `f' (x - a)`. -/
private theorem tendsto_slope_line {f : E → ℝ} {f' : E →L[ℝ] ℝ} {a : E}
    (hf : HasFDerivAt f f' a) (x : E) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ * (f (a + t • (x - a)) - f a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f' (x - a))) := by
  have h := (hasDerivAt_line hf x).tendsto_slope_zero_right
  simpa [smul_eq_mul] using h

/-- **First-order condition for convexity.** If `f` is convex on `s`, `a, x ∈ s`, and `f` has
Fréchet derivative `f'` at `a`, then `f a + f' (x - a) ≤ f x`: the first-order Taylor
approximation is a global underestimator.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.3, eq. (3.2). -/
theorem add_fderiv_le_of_convexOn {s : Set E} {f : E → ℝ} {f' : E →L[ℝ] ℝ} {a x : E}
    (hf : ConvexOn ℝ s f) (ha : a ∈ s) (hx : x ∈ s) (hf' : HasFDerivAt f f' a) :
    f a + f' (x - a) ≤ f x := by
  have hlim := tendsto_slope_line hf' x
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t⁻¹ * (f (a + t • (x - a)) - f a) ≤ f x - f a := by
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hmem] with t ht
    have ht0 : 0 < t := ht.1
    have hconv := hf.2 ha hx (sub_nonneg.2 ht.2.le) ht0.le (by ring)
    have hpt : (1 - t) • a + t • x = a + t • (x - a) := by module
    rw [hpt, smul_eq_mul, smul_eq_mul] at hconv
    rw [inv_mul_le_iff₀ ht0]
    linarith
  have := le_of_tendsto hlim hev
  linarith

/-- **Supporting affine minorants imply convexity.** If `s` is convex and at every `a ∈ s` there
is a continuous linear functional `g a` with `f a + g a (x - a) ≤ f x` for all `x ∈ s`, then `f`
is convex on `s`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.3 (the converse direction of the first-order condition). -/
theorem convexOn_of_forall_add_le {s : Set E} {f : E → ℝ} (hs : Convex ℝ s)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ a ∈ s, ∀ x ∈ s, f a + g a (x - a) ≤ f x) :
    ConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy α β hα hβ hαβ => ?_⟩
  set z := α • x + β • y with hz
  have hzs : z ∈ s := hs hx hy hα hβ hαβ
  have h1 := hg z hzs x hx
  have h2 := hg z hzs y hy
  have hzero : α • (x - z) + β • (y - z) = 0 := by
    calc α • (x - z) + β • (y - z) = (α • x + β • y) - (α + β) • z := by module
      _ = 0 := by rw [hαβ, one_smul, ← hz, sub_self]
  have hlin : α * g z (x - z) + β * g z (y - z) = 0 := by
    have := congrArg (g z) hzero
    simpa [map_add, map_smul, smul_eq_mul] using this
  rw [smul_eq_mul, smul_eq_mul]
  have hfz : f z = α * f z + β * f z := by rw [← add_mul, hαβ, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hα, mul_le_mul_of_nonneg_left h2 hβ]

/-- **First-order characterization of convexity.** On an open convex set `s` on which `f` is
differentiable, `f` is convex iff `f a + Df(a)(x - a) ≤ f x` for all `a, x ∈ s`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.3, eq. (3.2). -/
theorem convexOn_iff_forall_add_fderiv_le {s : Set E} {f : E → ℝ} (hso : IsOpen s)
    (hs : Convex ℝ s) (hf : DifferentiableOn ℝ f s) :
    ConvexOn ℝ s f ↔ ∀ a ∈ s, ∀ x ∈ s, f a + fderiv ℝ f a (x - a) ≤ f x := by
  constructor
  · intro hconv a ha x hx
    exact add_fderiv_le_of_convexOn hconv ha hx
      ((hf a ha).differentiableAt (hso.mem_nhds ha)).hasFDerivAt
  · intro h
    exact convexOn_of_forall_add_le hs (fderiv ℝ f) h

/-- **Optimality criterion for convex problems.** Let `f` be convex on `s` and differentiable at
`a ∈ s`. Then `a` minimizes `f` over `s` iff `Df(a)(x - a) ≥ 0` for every `x ∈ s`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§4.2.3, eq. (4.21). -/
theorem isMinOn_iff_forall_fderiv_nonneg {s : Set E} {f : E → ℝ} {f' : E →L[ℝ] ℝ} {a : E}
    (hf : ConvexOn ℝ s f) (ha : a ∈ s) (hf' : HasFDerivAt f f' a) :
    IsMinOn f s a ↔ ∀ x ∈ s, 0 ≤ f' (x - a) := by
  constructor
  · intro hmin x hx
    have hlim := tendsto_slope_line hf' x
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 ≤ t⁻¹ * (f (a + t • (x - a)) - f a) := by
      have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        Ioo_mem_nhdsGT zero_lt_one
      filter_upwards [hmem] with t ht
      have hpt : a + t • (x - a) = (1 - t) • a + t • x := by module
      have hmemt : a + t • (x - a) ∈ s := by
        rw [hpt]; exact hf.1 ha hx (sub_nonneg.2 ht.2.le) ht.1.le (by ring)
      have := hmin hmemt
      exact mul_nonneg (inv_nonneg.2 ht.1.le) (sub_nonneg.2 this)
    exact ge_of_tendsto hlim hev
  · intro h x hx
    have := add_fderiv_le_of_convexOn hf ha hx hf'
    change f a ≤ f x
    linarith [h x hx]

/-- **Stationary points of convex functions are global minimizers.** If `f` is convex on `s`,
`a ∈ s`, and `f` has zero derivative at `a`, then `a` minimizes `f` over `s`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§4.2.3, eq. (4.22) (unconstrained problems). -/
theorem isMinOn_of_hasFDerivAt_eq_zero {s : Set E} {f : E → ℝ} {a : E}
    (hf : ConvexOn ℝ s f) (ha : a ∈ s) (hf' : HasFDerivAt f (0 : E →L[ℝ] ℝ) a) :
    IsMinOn f s a :=
  (isMinOn_iff_forall_fderiv_nonneg hf ha hf').2 fun _ _ => by simp

/-- Suppose $X$ is an open convex subset of a Banach space $E$ and $f\in C^2(X,\mathbb R)$.
Then $f$ is convex on $X$ iff $f(x)\ge f(a)+\partial f(a)(x-a)$ for all $a,x\in X$. (Only
differentiability on $X$ is used; see `convexOn_iff_forall_add_fderiv_le`.)

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Measures,
integration, derivative, holomorphy), `benchmark/level1/ma_proofbench_l1_95.lean` at
openbmb/ma-proofbench@31bab4c; the result is S. Boyd and L. Vandenberghe, *Convex
Optimization*, §3.1.3. -/
theorem convexOn_iff_forall_le_add_fderivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Set E} (hXopen : IsOpen X) (hXconv : Convex ℝ X)
    {f : E → ℝ} (hf : ContDiffOn ℝ 2 f X) :
    ConvexOn ℝ X f ↔
      ∀ ⦃a⦄, a ∈ X → ∀ ⦃x⦄, x ∈ X →
        f x ≥ f a + (fderivWithin ℝ f X a) (x - a) := by
  have hd : DifferentiableOn ℝ f X := hf.differentiableOn (by norm_num)
  rw [convexOn_iff_forall_add_fderiv_le hXopen hXconv hd]
  constructor
  · intro h a ha x hx
    rw [fderivWithin_of_isOpen hXopen ha]
    exact h a ha x hx
  · intro h a ha x hx
    have := h ha hx
    rw [fderivWithin_of_isOpen hXopen ha] at this
    exact this

end MathlibExt.Analysis.Convex.FirstOrderCondition
