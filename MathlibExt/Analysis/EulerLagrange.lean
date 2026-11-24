/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/EulerLagrange.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `euler_lagrange_equation`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/euler_lagrange_equation.toml`, rev 1, submitter Kim Morrison, status
archived): the definitions `lagrangianPartialX`, `lagrangianPartialV` and `IsVariationalExtremum`
and the statement of `euler_lagrange_equation`, with the docstrings and comments they had in the
former wanted module `WantedExt/Analysis/EulerLagrangeWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Analysis.EulerLagrangeWanted` namespace. Mathematical statements are unchanged.
Later changes (ATLAS, 2026): the docstrings were restated to match the Lean statements; then the
`theorem_wanted` was proved, and it and the three definitions moved from
`WantedExt/Analysis/EulerLagrangeWanted.lean` to this `MathlibExt` module with unchanged names,
statements, definition bodies and docstrings, and the imports of `Batteries.Util.ProofWanted` and
of all of Mathlib were replaced by narrower Mathlib imports.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`euler_lagrange_equation`, the private lemmas it uses, the module documentation and the linter
options.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Euler–Lagrange equation

For a Lagrangian `L t y v` and a path `x : ℝ → ℝ`, `lagrangianPartialX L x t` and
`lagrangianPartialV L x t` are the partial derivatives `∂L/∂y` and `∂L/∂v` at
`(t, x t, x' t)`, each the derivative of a one-variable section of `L`. The path `x` is a
variational extremum of the action `∫_(a, b) L(t, x(t), x'(t)) dt` (`IsVariationalExtremum`) when
it is `C¹` and the derivative at `ε = 0` of the action of `x + ε h` vanishes for every smooth `h`
whose support is compact and contained in `(a, b)`.

## Main definitions

* `lagrangianPartialX`: the partial derivative `∂L/∂y (t, x t, x' t)`.
* `lagrangianPartialV`: the partial derivative `∂L/∂v (t, x t, x' t)`.
* `IsVariationalExtremum`: the first variation of the action on `(a, b)` vanishes.

## Main statements

* `euler_lagrange_equation` (L. Euler, 1744; J.-L. Lagrange, 1755): if `a < b`, `L` is `C²` on
  `ℝ³` and `x` is a `C²` variational extremum of the action of `L` on `(a, b)`, then
  `∂L/∂y (t, x t, x' t) = d/dt ∂L/∂v (t, x t, x' t)` for every `t ∈ (a, b)`.

## Proof outline

Write `DL` for the derivative of the uncurried Lagrangian `(t, y, v) ↦ L t y v`, so that the two
partial derivatives along `x` are `DL (t, x t, x' t)` applied to `(0, 1, 0)` and `(0, 0, 1)`. Fix
a test function `h`.

* The integrand `L t (x t + ε h t) (x' t + ε h' t)` has derivative
  `DL (t, x t + ε h t, x' t + ε h' t) (0, h t, h' t)` in `ε`. It is continuous in `(ε, t)`, so
  it is bounded for `|ε| ≤ 1` and `t ∈ [a, b]`, and differentiation under the integral sign
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) turns the hypothesis into
  `∫_(a, b) (∂L/∂y · h + ∂L/∂v · h') = 0`.
* Since `L` and `x` are `C²`, `t ↦ ∂L/∂v (t, x t, x' t)` is `C¹`, and `h a = h b = 0`, so an
  integration by parts gives `∫_(a, b) (∂L/∂y - d/dt ∂L/∂v) · h = 0`.
* By the fundamental lemma of the calculus of variations
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), the continuous function
  `∂L/∂y - d/dt ∂L/∂v` vanishes almost everywhere on `(a, b)`, hence everywhere on `(a, b)`.

## Implementation notes

The definitions and the statement keep the full names they had in the former wanted module
`WantedExt/Analysis/EulerLagrangeWanted.lean`, so the namespace still reads
`EulerLagrangeWanted` and repeats `Analysis`; the `dupNamespace` linter is turned off for these
four declarations only.

## References

* L. Euler (1744) and J.-L. Lagrange (1755). Listed as §44 in O. Knill, *Some Fundamental
  Theorems in Mathematics*
  (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf); this is the
  source cited by problem `euler_lagrange_equation` of the lean-eval benchmark
  (leanprover/lean-eval), from which the definitions and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.Analysis.EulerLagrangeWanted
namespace Analysis

open MeasureTheory Set
open scoped ContDiff

set_option linter.dupNamespace false in
/-- **Partial derivative of the Lagrangian in position.** For a real function $L(t, y, v)$
of three real variables, a function $x : \mathbb{R} \to \mathbb{R}$ and a real number $t$, this
is the value $\frac{\partial L}{\partial y}(t, x(t), x'(t))$, the derivative at $y = x(t)$ of
the function $y \mapsto L(t, y, x'(t))$.

By convention, a derivative that does not exist is taken to be $0$, both for $x'(t)$ and for
the derivative in $y$. -/
noncomputable def lagrangianPartialX
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t)) (x t)

set_option linter.dupNamespace false in
/-- **Partial derivative of the Lagrangian in velocity.** For a real function $L(t, y, v)$
of three real variables, a function $x : \mathbb{R} \to \mathbb{R}$ and a real number $t$, this
is the value $\frac{\partial L}{\partial v}(t, x(t), x'(t))$, the derivative at $v = x'(t)$ of
the function $v \mapsto L(t, x(t), v)$.

By convention, a derivative that does not exist is taken to be $0$, both for $x'(t)$ and for
the derivative in $v$. -/
noncomputable def lagrangianPartialV
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun z => L t (x t) z) (deriv x t)

set_option linter.dupNamespace false in
/-- **Variational extremum.** Let $a, b$ be real numbers and let $L(t, y, v)$
be a real function of three real variables. A function $x : \mathbb{R} \to \mathbb{R}$ is a
variational extremum of the action of $L$ on $(a, b)$ if $x$ is continuously differentiable and,
for every infinitely differentiable function $h : \mathbb{R} \to \mathbb{R}$ of compact support
whose closed support lies in the open interval $(a, b)$, the derivative at $\varepsilon = 0$ of
$$
\varepsilon \mapsto \int_{(a, b)}
L\big(t, x(t) + \varepsilon h(t), x'(t) + \varepsilon h'(t)\big)\,dt
$$
is $0$.

By convention, a derivative that does not exist is taken to be $0$, and so is the integral of a
function that is not integrable. -/
def IsVariationalExtremum
    (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 x ∧
  ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
    tsupport h ⊆ Set.Ioo a b →
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0 = 0

/-- Along any path, `lagrangianPartialX` is the derivative of the uncurried Lagrangian in the
direction `(0, 1, 0)`. -/
private theorem lagrangianPartialX_eq_fderiv {L : ℝ → ℝ → ℝ → ℝ}
    (hL : Differentiable ℝ (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)) (x : ℝ → ℝ) (t : ℝ) :
    lagrangianPartialX L x t =
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2) (t, x t, deriv x t) (0, 1, 0) :=
  ((hL _).hasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => ((t, y, deriv x t) : ℝ × ℝ × ℝ)) (x t)
    ((hasDerivAt_const _ t).prodMk ((hasDerivAt_id' _).prodMk (hasDerivAt_const _ _)))).deriv

/-- Along any path, `lagrangianPartialV` is the derivative of the uncurried Lagrangian in the
direction `(0, 0, 1)`. -/
private theorem lagrangianPartialV_eq_fderiv {L : ℝ → ℝ → ℝ → ℝ}
    (hL : Differentiable ℝ (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)) (x : ℝ → ℝ) (t : ℝ) :
    lagrangianPartialV L x t =
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2) (t, x t, deriv x t) (0, 0, 1) :=
  ((hL _).hasFDerivAt.comp_hasDerivAt (f := fun v : ℝ => ((t, x t, v) : ℝ × ℝ × ℝ)) (deriv x t)
    ((hasDerivAt_const _ t).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id' _)))).deriv

/-- Along a `C²` path, the partial derivative in position of a `C²` Lagrangian is continuous. -/
private theorem continuous_lagrangianPartialX {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)) (hx : ContDiff ℝ 2 x) :
    Continuous (lagrangianPartialX L x) := by
  rw [funext (lagrangianPartialX_eq_fderiv (hL.differentiable (by norm_num)) x)]
  have hγ : Continuous fun t => ((t, x t, deriv x t) : ℝ × ℝ × ℝ) :=
    continuous_id.prodMk (hx.continuous.prodMk (hx.continuous_deriv (by norm_num)))
  exact ((hL.continuous_fderiv (by norm_num)).comp hγ).clm_apply continuous_const

/-- Along a `C²` path, the partial derivative in velocity of a `C²` Lagrangian is `C¹`: it is
`DL (t, x t, x' t) (0, 0, 1)`, where the derivative `DL` of the Lagrangian and the curve
`t ↦ (t, x t, x' t)` are both `C¹`. -/
private theorem contDiff_lagrangianPartialV {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)) (hx : ContDiff ℝ 2 x) :
    ContDiff ℝ 1 (lagrangianPartialV L x) := by
  rw [funext (lagrangianPartialV_eq_fderiv (hL.differentiable (by norm_num)) x)]
  have hγ : ContDiff ℝ 1 fun t => ((t, x t, deriv x t) : ℝ × ℝ × ℝ) :=
    contDiff_id.prodMk ((hx.of_le (by norm_num)).prodMk hx.deriv')
  exact ((hL.fderiv_right le_rfl).comp hγ).clm_apply contDiff_const

/-- At a variational extremum, the first variation of the action along a test function `h`
vanishes: differentiating under the integral sign at `ε = 0`,
`∫_(a, b) (∂L/∂y · h + ∂L/∂v · h') = 0`. -/
private theorem integral_first_variation_eq_zero {a b : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2)) (hx : ContDiff ℝ 2 x)
    (hxe : IsVariationalExtremum a b L x) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (hhs : tsupport h ⊆ Ioo a b) :
    ∫ t in Ioo a b, (lagrangianPartialX L x t * h t + lagrangianPartialV L x t * deriv h t) =
      0 := by
  set Lf : ℝ × ℝ × ℝ → ℝ := fun p => L p.1 p.2.1 p.2.2
  have hLd : Differentiable ℝ Lf := hL.differentiable (by norm_num)
  have hdL : Continuous (fderiv ℝ Lf) := hL.continuous_fderiv (by norm_num)
  have hxcont : Continuous x := hx.continuous
  have hx'cont : Continuous (deriv x) := hx.continuous_deriv (by norm_num)
  have hhcont : Continuous h := hh.continuous
  have hh'cont : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  -- The integrand of the action along `x + ε h`, and its derivative in `ε`.
  set F : ℝ → ℝ → ℝ := fun ε t => L t (x t + ε * h t) (deriv x t + ε * deriv h t)
  set F' : ℝ → ℝ → ℝ := fun ε t =>
    fderiv ℝ Lf (t, x t + ε * h t, deriv x t + ε * deriv h t) (0, h t, deriv h t) with hF'
  have hFc (ε : ℝ) : Continuous (F ε) :=
    (hLd.continuous.comp (by fun_prop) :
      Continuous fun t => Lf (t, x t + ε * h t, deriv x t + ε * deriv h t))
  have hF'c : Continuous fun p : ℝ × ℝ => F' p.1 p.2 := by
    have hγ : Continuous fun p : ℝ × ℝ =>
        ((p.2, x p.2 + p.1 * h p.2, deriv x p.2 + p.1 * deriv h p.2) : ℝ × ℝ × ℝ) := by
      fun_prop
    exact (hdL.comp hγ).clm_apply (by fun_prop)
  have hderiv (t ε : ℝ) : HasDerivAt (fun ε => F ε t) (F' ε t) ε := by
    have hγ : HasDerivAt
        (fun ε : ℝ => ((t, x t + ε * h t, deriv x t + ε * deriv h t) : ℝ × ℝ × ℝ))
        (0, h t, deriv h t) ε :=
      (hasDerivAt_const ε t).prodMk (((hasDerivAt_mul_const (h t)).const_add (x t)).prodMk
        ((hasDerivAt_mul_const (deriv h t)).const_add (deriv x t)))
    exact (hLd _).hasFDerivAt.comp_hasDerivAt ε hγ
  -- `F'` is bounded by some `C` on the compact set `[-1, 1] × [a, b]`, and this constant
  -- dominates the derivatives in `ε` for `|ε| ≤ 1`.
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod (isCompact_Icc (a := a) (b := b))
    ).exists_bound_of_continuousOn hF'c.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioo a b))
    (F := F) (F' := F') (x₀ := 0) (bound := fun _ => C) (Metric.closedBall_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun ε => (hFc ε).aestronglyMeasurable)
    ((hFc 0).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (hF'c.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
      fun t ht ε hε => hC (ε, t) ⟨hε, Ioo_subset_Icc_self ht⟩))
    (integrable_const C) (Filter.Eventually.of_forall fun t ε _ => hderiv t ε)
  have h0 : ∫ t in Ioo a b, F' 0 t = 0 := key.2.deriv.symm.trans (hxe.2 h hh hhc hhs)
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)) h0
  -- At `ε = 0` and `p = (t, x t, x' t)`, linearity gives
  -- `DL p (0, h t, h' t) = h t · DL p (0, 1, 0) + h' t · DL p (0, 0, 1)`.
  have hv : ((0 : ℝ), h t, deriv h t) =
      h t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + deriv h t • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  simp only [hF', zero_mul, add_zero, hv, map_add, map_smul, smul_eq_mul]
  rw [lagrangianPartialX_eq_fderiv hLd, lagrangianPartialV_eq_fderiv hLd]
  ring

/-- Integrating the velocity term by parts, the Euler–Lagrange expression
`∂L/∂y - d/dt ∂L/∂v` integrates to zero against every test function. -/
private theorem integral_eulerLagrange_mul_eq_zero {a b : ℝ} {L : ℝ → ℝ → ℝ → ℝ} {x : ℝ → ℝ}
    (hab : a < b) (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (hx : ContDiff ℝ 2 x) (hxe : IsVariationalExtremum a b L x) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) (hhs : tsupport h ⊆ Ioo a b) :
    ∫ t in Ioo a b, (lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t) * h t = 0 := by
  have hV := contDiff_lagrangianPartialV hL hx
  have hXcont := continuous_lagrangianPartialX hL hx
  have hV'cont : Continuous (deriv (lagrangianPartialV L x)) := hV.continuous_deriv le_rfl
  have hhcont : Continuous h := hh.continuous
  have hh'cont : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  -- `h` vanishes at both endpoints, which lie outside its support.
  have ha : h a = 0 := image_eq_zero_of_notMem_tsupport fun hmem => lt_irrefl a (hhs hmem).1
  have hb : h b = 0 := image_eq_zero_of_notMem_tsupport fun hmem => lt_irrefl b (hhs hmem).2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (fun t _ => (hV.differentiable_one t).hasDerivAt)
    (fun t _ => (hh.differentiable (by simp) t).hasDerivAt)
    (hV'cont.intervalIntegrable a b) (hh'cont.intervalIntegrable a b)
  have hi₁ : IntervalIntegrable (fun t => lagrangianPartialX L x t * h t) volume a b :=
    (hXcont.mul hhcont).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun t => lagrangianPartialV L x t * deriv h t) volume a b :=
    (hV.continuous.mul hh'cont).intervalIntegrable a b
  have hi₃ : IntervalIntegrable (fun t => deriv (lagrangianPartialV L x) t * h t) volume a b :=
    (hV'cont.mul hhcont).intervalIntegrable a b
  have h0 := integral_first_variation_eq_zero hL hx hxe hh hhc hhs
  have hIoo (f : ℝ → ℝ) : ∫ t in Ioo a b, f t = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rw [hIoo] at h0 ⊢
  rw [intervalIntegral.integral_add hi₁ hi₂, hibp, ha, hb] at h0
  simp only [sub_mul]
  rw [intervalIntegral.integral_sub hi₁ hi₃]
  linarith

set_option linter.dupNamespace false in
/- **Euler–Lagrange equation** (§44). On an interval `a < b`, every `C²`
variational extremum `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt`, with
`C²` Lagrangian `L`, satisfies the pointwise equation
`∂L/∂x (t, x(t), x'(t)) = (d/dt)(∂L/∂x' (t, x(t), x'(t)))` on `(a, b)`. -/
/-- **Euler–Lagrange equation.** Let $a < b$ be real numbers, let $L(t, y, v)$ be a real function
of three real variables that is twice continuously differentiable on $\mathbb{R}^3$, and let
$x : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable. Write
$\partial L / \partial y$ and $\partial L / \partial v$ for the partial derivatives of $L$ in its
second and third arguments. If $x$ is a variational extremum of the action of $L$ on $(a, b)$,
then for every $t \in (a, b)$
$$
\frac{\partial L}{\partial y}(t, x(t), x'(t))
= \frac{d}{ds}\Big|_{s = t} \frac{\partial L}{\partial v}(s, x(s), x'(s)).
$$

Source: L. Euler (1744) and J.-L. Lagrange (1755). Listed as §44 in O. Knill, Some Fundamental
Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `euler_lagrange_equation`. -/
public theorem euler_lagrange_equation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (_hab : a < b)
    (_hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (_hx : ContDiff ℝ 2 x)
    (_hxe : IsVariationalExtremum a b L x) :
    ∀ t ∈ Set.Ioo a b,
      lagrangianPartialX L x t = deriv (lagrangianPartialV L x) t := by
  set f : ℝ → ℝ := fun t => lagrangianPartialX L x t - deriv (lagrangianPartialV L x) t with hf
  have hfc : Continuous f := (continuous_lagrangianPartialX _hL _hx).sub
    ((contDiff_lagrangianPartialV _hL _hx).continuous_deriv le_rfl)
  -- `f` integrates to zero against every test function supported in `(a, b)`.
  have hint (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
      (hgs : tsupport g ⊆ Ioo a b) : ∫ t, g t • f t = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b) fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport fun hmem => ht (hgs hmem), zero_smul]]
    simp_rw [hf, smul_eq_mul, mul_comm (g _)]
    exact integral_eulerLagrange_mul_eq_zero _hab _hL _hx _hxe hg hgc hgs
  -- By the fundamental lemma of the calculus of variations, `f = 0` almost everywhere on
  -- `(a, b)`, hence everywhere on `(a, b)` since `f` is continuous.
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hfc.locallyIntegrable.locallyIntegrableOn _) hint
  have heq := Measure.eqOn_open_of_ae_eq (f := f) (g := fun _ => 0)
    ((ae_restrict_iff' measurableSet_Ioo).2 hae) isOpen_Ioo hfc.continuousOn continuousOn_const
  intro t ht
  exact sub_eq_zero.1 (heq ht)

end Analysis

end MathlibExt.Analysis.EulerLagrangeWanted
