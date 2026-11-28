/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.RatIntervalOps

/-!
# Interval expressions and the fundamental theorem

Expression syntax (`Expr`) over rational interval arithmetic, with interval
evaluation (`Expr.evalI`) and pointwise real evaluation (`Expr.eval`).

The fundamental theorem (`Expr.encloses_eval`): for expressions satisfying
`Expr.WellDefined` (every denominator interval excludes zero), interval
evaluation encloses every pointwise value over enclosed inputs. The dependency
witness (`Expr.sub_self_dependency`): `x - x` over `[0, 1]` evaluates to
`⟨-1, 1⟩` although every pointwise value is `0`. Width facts (`width_add`,
`width_sub`, `width_neg`, `width_mul_le`).

Moore, Kearfott and Cloud, Introduction to Interval Analysis, SIAM, 2009,
Chapters 2 and 3; van Emden and Moa, The Fundamental Theorems of Interval Analysis,
arXiv, 2007.
-/

@[expose] public section

namespace MathlibExt.Analysis.Numerical.Certified

namespace RatInterval

/-- Syntax of arithmetic expressions with variables of type `α`. -/
inductive Expr (α : Type*) where
  | var (a : α)
  | const (q : ℚ)
  | neg (e : Expr α)
  | add (e₁ e₂ : Expr α)
  | sub (e₁ e₂ : Expr α)
  | mul (e₁ e₂ : Expr α)
  | div (e₁ e₂ : Expr α)
deriving DecidableEq, Repr

/-- Interval evaluation of an expression: variables via `valI`, constants as
point intervals, and compound expressions via the corresponding `RatInterval`
operations. -/
def Expr.evalI {α : Type*} (valI : α → RatInterval) : Expr α → RatInterval
  | .var a => valI a
  | .const q => ofRat q
  | .neg e => (e.evalI valI).neg
  | .add e₁ e₂ => (e₁.evalI valI).add (e₂.evalI valI)
  | .sub e₁ e₂ => (e₁.evalI valI).sub (e₂.evalI valI)
  | .mul e₁ e₂ => (e₁.evalI valI).mul (e₂.evalI valI)
  | .div e₁ e₂ => (e₁.evalI valI).div (e₂.evalI valI)

/-- Pointwise real evaluation of an expression with the ordinary real
operations (Lean's total division). -/
noncomputable def Expr.eval {α : Type*} (val : α → ℝ) : Expr α → ℝ
  | .var a => val a
  | .const q => (q : ℝ)
  | .neg e => -(e.eval val)
  | .add e₁ e₂ => e₁.eval val + e₂.eval val
  | .sub e₁ e₂ => e₁.eval val - e₂.eval val
  | .mul e₁ e₂ => e₁.eval val * e₂.eval val
  | .div e₁ e₂ => e₁.eval val / e₂.eval val

/-- Domain condition for interval evaluation: every division's denominator
interval excludes zero. -/
def Expr.WellDefined {α : Type*} (valI : α → RatInterval) : Expr α → Bool
  | .var _ => true
  | .const _ => true
  | .neg e => e.WellDefined valI
  | .add e₁ e₂ => e₁.WellDefined valI && e₂.WellDefined valI
  | .sub e₁ e₂ => e₁.WellDefined valI && e₂.WellDefined valI
  | .mul e₁ e₂ => e₁.WellDefined valI && e₂.WellDefined valI
  | .div e₁ e₂ => e₁.WellDefined valI && e₂.WellDefined valI &&
      decide ((e₂.evalI valI).upper < 0 ∨ 0 < (e₂.evalI valI).lower)

/-- Fundamental theorem of interval arithmetic: for expressions satisfying
`Expr.WellDefined` (every denominator interval excludes zero), interval
evaluation encloses every pointwise value over enclosed inputs. -/
theorem Expr.encloses_eval {α : Type*} {valI : α → RatInterval} {val : α → ℝ}
    (hval : ∀ a, (valI a).Encloses (val a)) (e : Expr α) (hw : e.WellDefined valI = true) :
    (e.evalI valI).Encloses (e.eval val) := by
  revert hw
  induction e with
  | var a =>
    intro _
    exact hval a
  | const q =>
    intro _
    exact encloses_ofRat q
  | neg e ih =>
    intro hw
    exact Encloses.neg (ih hw)
  | add e₁ e₂ ih₁ ih₂ =>
    intro hw
    have hw' : (e₁.WellDefined valI && e₂.WellDefined valI) = true := hw
    simp only [Bool.and_eq_true] at hw'
    exact Encloses.add (ih₁ hw'.1) (ih₂ hw'.2)
  | sub e₁ e₂ ih₁ ih₂ =>
    intro hw
    have hw' : (e₁.WellDefined valI && e₂.WellDefined valI) = true := hw
    simp only [Bool.and_eq_true] at hw'
    exact Encloses.sub (ih₁ hw'.1) (ih₂ hw'.2)
  | mul e₁ e₂ ih₁ ih₂ =>
    intro hw
    have hw' : (e₁.WellDefined valI && e₂.WellDefined valI) = true := hw
    simp only [Bool.and_eq_true] at hw'
    exact Encloses.mul (ih₁ hw'.1) (ih₂ hw'.2)
  | div e₁ e₂ ih₁ ih₂ =>
    intro hw
    have hw' : (e₁.WellDefined valI && e₂.WellDefined valI &&
        decide ((e₂.evalI valI).upper < 0 ∨ 0 < (e₂.evalI valI).lower)) = true := hw
    simp only [Bool.and_eq_true] at hw'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw'
    exact Encloses.div (of_decide_eq_true h3) (ih₁ h1) (ih₂ h2)

/-- Corollary of the fundamental theorem: for expressions satisfying
`Expr.WellDefined` and enclosed inputs, the pointwise value lies in the
closed real interval spanned by the endpoints of the interval
evaluation. -/
theorem Expr.eval_mem_Icc {α : Type*} {valI : α → RatInterval} {val : α → ℝ}
    (hval : ∀ a, (valI a).Encloses (val a)) (e : Expr α) (hw : e.WellDefined valI = true) :
    e.eval val ∈ Set.Icc ((e.evalI valI).lower : ℝ) (e.evalI valI).upper :=
  Set.mem_Icc.mpr (encloses_iff.mp (Expr.encloses_eval hval e hw))

/-- Dependency witness with variable type `Unit` (interval evaluation is not
tight): `x - x` over `[0, 1]` gives `⟨-1, 1⟩` (width 2) although every
pointwise value is `0`. -/
theorem Expr.sub_self_dependency :
    (Expr.sub (Expr.var ()) (Expr.var ())).evalI
        (fun _ => (⟨0, 1⟩ : RatInterval)) = ⟨-1, 1⟩ ∧
    ∀ val : Unit → ℝ, (Expr.sub (Expr.var ()) (Expr.var ())).eval val = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [Expr.evalI, RatInterval.sub]
    congr 1 <;> norm_num
  · intro val
    simp only [Expr.eval, sub_self]

/-- Width of a sum of intervals. -/
theorem width_add (I J : RatInterval) : (I.add J).width = I.width + J.width := by
  simp only [RatInterval.width, RatInterval.add]
  ring

/-- Width of a difference of intervals. -/
theorem width_sub (I J : RatInterval) : (I.sub J).width = I.width + J.width := by
  simp only [RatInterval.width, RatInterval.sub]
  ring

/-- Width of a negated interval. -/
theorem width_neg (I : RatInterval) : I.neg.width = I.width := by
  simp only [RatInterval.width, RatInterval.neg]
  ring

/-- Magnitude of an interval: the maximum absolute endpoint. -/
def mag (I : RatInterval) : ℚ := max |I.lower| |I.upper|

/-- Width of a product bounded by magnitudes times widths for intervals with `lower ≤ upper`. -/
theorem width_mul_le {I J : RatInterval} (hI : I.lower ≤ I.upper) (hJ : J.lower ≤ J.upper) :
    (I.mul J).width ≤ I.mag * J.width + J.mag * I.width := by
  set MI := I.mag with hMI
  set MJ := J.mag with hMJ
  set WI := I.width with hWI
  set WJ := J.width with hWJ
  have hMI0 : 0 ≤ MI := by
    rw [hMI]
    simp only [RatInterval.mag]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hMJ0 : 0 ≤ MJ := by
    rw [hMJ]
    simp only [RatInterval.mag]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  have hM : ∀ (x x' y y' : ℚ), |x| ≤ MI → |y'| ≤ MJ → |y - y'| ≤ WJ → |x - x'| ≤ WI →
      x * y ≤ MI * WJ + MJ * WI + x' * y' := by
    intro x x' y y' hx hy' hyy hxx
    have e : x * y - x' * y' = x * (y - y') + y' * (x - x') := by ring
    have hle : x * y - x' * y' ≤ MI * WJ + MJ * WI := by
      calc x * y - x' * y' = x * (y - y') + y' * (x - x') := e
        _ ≤ |x * (y - y')| + |y' * (x - x')| := add_le_add (le_abs_self _) (le_abs_self _)
        _ = |x| * |y - y'| + |y'| * |x - x'| := by rw [abs_mul, abs_mul]
        _ ≤ MI * WJ + MJ * WI :=
            add_le_add (mul_le_mul hx hyy (abs_nonneg _) hMI0)
              (mul_le_mul hy' hxx (abs_nonneg _) hMJ0)
    linarith
  simp only [RatInterval.width, RatInterval.mul]
  rw [sub_le_iff_le_add]
  simp only [add_min]
  simp only [max_le_iff, le_min_iff]
  refine ⟨?_, ?_⟩ <;> refine ⟨?_, ?_⟩ <;> refine ⟨?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  all_goals
    (refine hM _ _ _ _ ?_ ?_ ?_ ?_ <;>
      simp only [hMI, hMJ, hWI, hWJ, RatInterval.mag, RatInterval.width] <;>
      first
        | exact le_max_left _ _
        | exact le_max_right _ _
        | (rw [abs_le]; constructor <;> linarith))

end RatInterval

end MathlibExt.Analysis.Numerical.Certified

end
