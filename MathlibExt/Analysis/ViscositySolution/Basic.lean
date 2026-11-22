/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Viscosity solutions of first-order equations

The Crandall–Lions notion of viscosity sub- and supersolution of a first-order equation
`F(x, u(x), Du(x)) = 0` on a set `Ω` of a real normed space, defined through `C¹` test
functions touching `u` from above or below, and its consistency with classical solutions.

## Main definitions

* `IsViscositySubsolution F Ω u`: `u` is upper semicontinuous on `Ω` and
  `F(x, u(x), Dφ(x)) ≤ 0` whenever `φ` is `C¹` and `u - φ` has a local maximum relative to `Ω`
  at `x ∈ Ω`.
* `IsViscositySupersolution F Ω u`: the mirror notion (lower semicontinuous, local minima, `≥ 0`).
* `IsViscositySolution F Ω u`: both.

## Main results

* `isViscositySubsolution_of_classical`, `isViscositySupersolution_of_classical`,
  `isViscositySolution_of_classical`: on an open set, a pointwise differentiable classical
  sub/super/solution is a viscosity one.
* `IsViscositySubsolution.le_of_contDiff`, `IsViscositySupersolution.le_of_contDiff`,
  `isViscositySolution_iff_of_contDiff`: a `C¹` viscosity solution is classical.
* `not_isViscositySupersolution_abs`, `isViscositySolution_neg_abs`: Remark 2.5 of the user's
  guide: `-|x|` solves `(u')² - 1 = 0` on `ℝ` in the viscosity sense, while `|x|` does not.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992) 1–67, arXiv:math/9207212,
  §2 (Definition 2.2, Remarks 2.3 and 2.5).
* J. Calder, *Lecture notes on viscosity solutions*, version of 30 July 2024, Chapter 2
  (Definition 2.1, Remark 2.7, Exercise 2.10).
-/

@[expose] public section

namespace MathlibExt.Analysis.ViscositySolution

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Viscosity subsolution of a first-order equation** (Crandall–Lions; Crandall, Ishii and
Lions, *User's guide*, Bull. AMS 1992, Definition 2.2 and the test-function form (2.2) of
Remarks 2.3, specialised to first order; Calder, *Lecture notes on viscosity solutions*,
Definition 2.1). A function `u` is a viscosity subsolution of `F(x, u, Du) = 0` on `Ω` if it is
upper semicontinuous on `Ω` and `F(x, u(x), Dφ(x)) ≤ 0` whenever `φ` is a `C¹` function and
`u - φ` has a local maximum relative to `Ω` at `x ∈ Ω`. The Hamiltonian takes the gradient as a
continuous linear functional `p : E →L[ℝ] ℝ`. Calder uses `C^∞` test functions and notes in his
Remark 2.7 that `C¹` (indeed, differentiable-at-the-point) test functions give the same notion;
the `C¹` class is the one used here. -/
def IsViscositySubsolution (F : E → ℝ → (E →L[ℝ] ℝ) → ℝ) (Ω : Set E) (u : E → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧
    ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ 1 φ → IsLocalMaxOn (fun y => u y - φ y) Ω x →
      F x (u x) (fderiv ℝ φ x) ≤ 0

/-- **Viscosity supersolution of a first-order equation** (Crandall, Ishii and Lions, *User's
guide*, Definition 2.2, first-order test-function form; Calder, Definition 2.1). A function `u`
is a viscosity supersolution of `F(x, u, Du) = 0` on `Ω` if it is lower semicontinuous on `Ω`
and `F(x, u(x), Dφ(x)) ≥ 0` whenever `φ` is `C¹` and `u - φ` has a local minimum relative to
`Ω` at `x ∈ Ω`. -/
def IsViscositySupersolution (F : E → ℝ → (E →L[ℝ] ℝ) → ℝ) (Ω : Set E) (u : E → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧
    ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ 1 φ → IsLocalMinOn (fun y => u y - φ y) Ω x →
      0 ≤ F x (u x) (fderiv ℝ φ x)

/-- **Viscosity solution of a first-order equation** (Crandall, Ishii and Lions, *User's guide*,
Definition 2.2; Calder, Definition 2.1): a function that is both a viscosity subsolution and a
viscosity supersolution of `F(x, u, Du) = 0` on `Ω`. Such a function is continuous on `Ω`
(being upper and lower semicontinuous there). -/
def IsViscositySolution (F : E → ℝ → (E →L[ℝ] ℝ) → ℝ) (Ω : Set E) (u : E → ℝ) : Prop :=
  IsViscositySubsolution F Ω u ∧ IsViscositySupersolution F Ω u

variable {F : E → ℝ → (E →L[ℝ] ℝ) → ℝ} {Ω : Set E} {u : E → ℝ}

/-- At an interior local extremum of `u - φ` with `u` differentiable, the test function has the
same derivative as `u`. -/
private theorem fderiv_eq_of_isLocalExtrOn (hΩ : IsOpen Ω) {x : E} (hx : x ∈ Ω)
    (hu : DifferentiableAt ℝ u x) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hext : IsLocalExtrOn (fun y => u y - φ y) Ω x) : fderiv ℝ φ x = fderiv ℝ u x := by
  have hloc : IsLocalExtr (fun y => u y - φ y) x := hext.isLocalExtr (hΩ.mem_nhds hx)
  have h0 := hloc.fderiv_eq_zero
  rw [fderiv_fun_sub hu ((hφ.differentiable one_ne_zero) x), sub_eq_zero] at h0
  exact h0.symm

/-- **Classical subsolutions are viscosity subsolutions** (Crandall, Ishii and Lions, *User's
guide*, the computation (2.1) preceding Definition 2.2, first order; Calder, Exercise 2.10). On an
open set `Ω`, if `u` is differentiable at every point of `Ω` and `F(x, u(x), Du(x)) ≤ 0` there,
then `u` is a viscosity subsolution of `F = 0` on `Ω`. -/
theorem isViscositySubsolution_of_classical (hΩ : IsOpen Ω)
    (hu : ∀ x ∈ Ω, DifferentiableAt ℝ u x) (hF : ∀ x ∈ Ω, F x (u x) (fderiv ℝ u x) ≤ 0) :
    IsViscositySubsolution F Ω u := by
  refine ⟨fun x hx => (hu x hx).continuousAt.continuousWithinAt.upperSemicontinuousWithinAt,
    fun x hx φ hφ hmax => ?_⟩
  rw [fderiv_eq_of_isLocalExtrOn hΩ hx (hu x hx) hφ (Or.inr hmax)]
  exact hF x hx

/-- **Classical supersolutions are viscosity supersolutions** (Crandall, Ishii and Lions,
*User's guide*, §2, first order; Calder, Exercise 2.10). On an open set `Ω`, if `u` is
differentiable at every point of `Ω` and `F(x, u(x), Du(x)) ≥ 0` there, then `u` is a viscosity
supersolution of `F = 0` on `Ω`. -/
theorem isViscositySupersolution_of_classical (hΩ : IsOpen Ω)
    (hu : ∀ x ∈ Ω, DifferentiableAt ℝ u x) (hF : ∀ x ∈ Ω, 0 ≤ F x (u x) (fderiv ℝ u x)) :
    IsViscositySupersolution F Ω u := by
  refine ⟨fun x hx => (hu x hx).continuousAt.continuousWithinAt.lowerSemicontinuousWithinAt,
    fun x hx φ hφ hmin => ?_⟩
  rw [fderiv_eq_of_isLocalExtrOn hΩ hx (hu x hx) hφ (Or.inl hmin)]
  exact hF x hx

/-- **Classical solutions are viscosity solutions** (Crandall, Ishii and Lions, *User's guide*,
§2, first order; Calder, Exercise 2.10). On an open set `Ω`, a function differentiable at every
point of `Ω` with `F(x, u(x), Du(x)) = 0` there is a viscosity solution of `F = 0` on `Ω`. -/
theorem isViscositySolution_of_classical (hΩ : IsOpen Ω)
    (hu : ∀ x ∈ Ω, DifferentiableAt ℝ u x) (hF : ∀ x ∈ Ω, F x (u x) (fderiv ℝ u x) = 0) :
    IsViscositySolution F Ω u :=
  ⟨isViscositySubsolution_of_classical hΩ hu fun x hx => (hF x hx).le,
    isViscositySupersolution_of_classical hΩ hu fun x hx => (hF x hx).ge⟩

/-- **A `C¹` viscosity subsolution is a classical subsolution** (Calder, *Lecture notes on
viscosity solutions*, Remark 2.7: take `φ = u`). If `u` is `C¹` and a viscosity subsolution of
`F = 0` on `Ω`, then `F(x, u(x), Du(x)) ≤ 0` at every `x ∈ Ω`. -/
theorem IsViscositySubsolution.le_of_contDiff (h : IsViscositySubsolution F Ω u)
    (hu : ContDiff ℝ 1 u) {x : E} (hx : x ∈ Ω) : F x (u x) (fderiv ℝ u x) ≤ 0 :=
  h.2 x hx u hu (Eventually.of_forall fun y => by simp)

/-- **A `C¹` viscosity supersolution is a classical supersolution** (Calder, Remark 2.7). If `u`
is `C¹` and a viscosity supersolution of `F = 0` on `Ω`, then `F(x, u(x), Du(x)) ≥ 0` at every
`x ∈ Ω`. -/
theorem IsViscositySupersolution.le_of_contDiff (h : IsViscositySupersolution F Ω u)
    (hu : ContDiff ℝ 1 u) {x : E} (hx : x ∈ Ω) : 0 ≤ F x (u x) (fderiv ℝ u x) :=
  h.2 x hx u hu (Eventually.of_forall fun y => by simp)

/-- **Consistency of viscosity and classical solutions** (Crandall, Ishii and Lions, *User's
guide*, §2; Calder, Remark 2.7 and Exercise 2.10). On an open set `Ω`, a `C¹` function is a
viscosity solution of `F(x, u, Du) = 0` if and only if it solves the equation pointwise on `Ω`. -/
theorem isViscositySolution_iff_of_contDiff (hΩ : IsOpen Ω) (hu : ContDiff ℝ 1 u) :
    IsViscositySolution F Ω u ↔ ∀ x ∈ Ω, F x (u x) (fderiv ℝ u x) = 0 := by
  refine ⟨fun h x hx => le_antisymm (h.1.le_of_contDiff hu hx) (h.2.le_of_contDiff hu hx),
    fun h => isViscositySolution_of_classical hΩ (fun x _ => hu.differentiable one_ne_zero x) h⟩

/-! ### The eikonal example of Remark 2.5 -/

/-- **The one-dimensional eikonal Hamiltonian** `F(x, r, p) = p(1)² - 1`, i.e. the equation
`(u')² - 1 = 0` on `ℝ` (Crandall, Ishii and Lions, *User's guide*, Remark 2.5). -/
def eikonal : ℝ → ℝ → (ℝ →L[ℝ] ℝ) → ℝ := fun _ _ p => p 1 ^ 2 - 1

/-- If `g` is differentiable at `0` with derivative `d` and `c |t| ≤ g t - g 0` near `0`, then
`c ≤ d ≤ -c`. -/
private theorem le_deriv_of_abs_le {g : ℝ → ℝ} {d c : ℝ} (hg : HasDerivAt g d 0)
    (hc : ∀ᶠ t in 𝓝 0, c * |t| ≤ g t - g 0) : c ≤ d ∧ d ≤ -c := by
  have hright := hg.tendsto_slope_zero_right
  have hleft := hg.tendsto_slope_zero_left
  simp only [zero_add, smul_eq_mul] at hright hleft
  constructor
  · refine ge_of_tendsto hright ?_
    filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht htpos
    have htpos : (0 : ℝ) < t := htpos
    rw [abs_of_pos htpos] at ht
    rw [inv_mul_eq_div, le_div_iff₀ htpos]
    linarith
  · refine le_of_tendsto hleft ?_
    filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht htneg
    have htneg : t < (0 : ℝ) := htneg
    rw [abs_of_neg htneg] at ht
    rw [inv_mul_eq_div, div_le_iff_of_neg htneg]
    linarith [show c * -t = -c * t by ring]

/-- **`|x|` is not a viscosity supersolution of `(u')² - 1 = 0`** (Crandall, Ishii and Lions,
*User's guide*, Remark 2.5): the constant test function `0` touches `|x|` from below at `0`,
where `0² - 1 < 0`. Hence `|x|` is not a viscosity solution, although it solves the equation
classically on `ℝ \ {0}`. -/
theorem not_isViscositySupersolution_abs : ¬ IsViscositySupersolution eikonal univ (|·|) := by
  intro h
  have := h.2 0 (mem_univ _) (fun _ => 0) contDiff_const
    (Eventually.of_forall fun y => by simp)
  simp [eikonal] at this
  linarith

/-- **`-|x|` is a viscosity solution of `(u')² - 1 = 0` on `ℝ`** (Crandall, Ishii and Lions,
*User's guide*, Remark 2.5). At `x ≠ 0` it is a classical solution; at `0` every `C¹` function
touching it from above has slope in `[-1, 1]`, and no `C¹` function touches it from below. So
a viscosity solution of `F = 0` need not be one of `-F = 0`, and the notion is not symmetric in
the sign of the equation. -/
theorem isViscositySolution_neg_abs : IsViscositySolution eikonal univ (fun x => -|x|) := by
  have hcont : Continuous fun x : ℝ => -|x| := continuous_abs.neg
  -- away from `0`, `-|x|` is differentiable with derivative `∓1`
  have hdiff : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x : ℝ => -|x|) (-SignType.sign x : ℝ) x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have : (fun y : ℝ => -|y|) =ᶠ[𝓝 x] fun y => y := by
        filter_upwards [eventually_lt_nhds hneg] with y hy
        rw [abs_of_neg hy, neg_neg]
      simpa [sign_neg hneg] using (hasDerivAt_id x).congr_of_eventuallyEq this
    · have : (fun y : ℝ => -|y|) =ᶠ[𝓝 x] fun y => -y := by
        filter_upwards [eventually_gt_nhds hpos] with y hy
        rw [abs_of_pos hy]
      simpa [sign_pos hpos] using (hasDerivAt_neg x).congr_of_eventuallyEq this
  -- a test function touching at `x ≠ 0` has derivative `∓1`, so the equation holds with equality
  have hclass : ∀ x : ℝ, x ≠ 0 → ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ →
      IsLocalExtrOn (fun y => -|y| - φ y) univ x → eikonal x (-|x|) (fderiv ℝ φ x) = 0 := by
    intro x hx φ hφ hext
    rw [fderiv_eq_of_isLocalExtrOn isOpen_univ (mem_univ x) (hdiff x hx).differentiableAt hφ hext,
      (hdiff x hx).hasFDerivAt.fderiv]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · simp [eikonal, sign_neg hneg]
    · simp [eikonal, sign_pos hpos]
  refine ⟨⟨hcont.continuousOn.upperSemicontinuousOn, fun x _ φ hφ hmax => ?_⟩,
    ⟨hcont.continuousOn.lowerSemicontinuousOn, fun x _ φ hφ hmin => ?_⟩⟩
  · by_cases hx : x = 0
    · subst hx
      have hd : HasDerivAt φ (fderiv ℝ φ 0 1) 0 :=
        ((hφ.differentiable one_ne_zero) 0).hasFDerivAt.hasDerivAt
      have hloc : ∀ᶠ t in 𝓝 (0 : ℝ), -1 * |t| ≤ φ t - φ 0 := by
        filter_upwards [hmax.isLocalMax Filter.univ_mem] with t ht
        simp only [abs_zero, neg_zero, zero_sub] at ht
        linarith
      obtain ⟨h1, h2⟩ := le_deriv_of_abs_le hd hloc
      have : fderiv ℝ φ 0 1 ^ 2 ≤ 1 := by nlinarith
      simp only [eikonal]
      linarith
    · exact (hclass x hx φ hφ (Or.inr hmax)).le
  · by_cases hx : x = 0
    · subst hx
      exfalso
      have hd : HasDerivAt (fun t => -φ t) (-fderiv ℝ φ 0 1) 0 :=
        ((hφ.differentiable one_ne_zero) 0).hasFDerivAt.hasDerivAt.neg
      have hloc : ∀ᶠ t in 𝓝 (0 : ℝ), 1 * |t| ≤ -φ t - -φ 0 := by
        filter_upwards [hmin.isLocalMin Filter.univ_mem] with t ht
        simp only [abs_zero, neg_zero, zero_sub] at ht
        linarith
      obtain ⟨h1, h2⟩ := le_deriv_of_abs_le hd hloc
      linarith
    · exact (hclass x hx φ hφ (Or.inl hmin)).ge

end MathlibExt.Analysis.ViscositySolution
