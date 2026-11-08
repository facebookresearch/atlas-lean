/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.GradientDescent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Uniform exponents for predetermined gradient-descent schedules

The optimization is over one infinite schedule before all finite-dimensional smooth
convex objectives and horizons. The rate concerns the last iterate and is normalized
by squared distance to an actual minimizer.

Source: OptimizationProblems, `constants/35a.md`. The attained-minimum and distance
normalization follow Altschuler and Parrilo, *Acceleration by Stepsize Hedging*.
-/

@[expose] public section

/-- Gradient descent with a predetermined, possibly varying, real step schedule. -/
noncomputable def gradientDescentTrajectory
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (s : ℕ → ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => gradientDescentTrajectory f s x₀ k -
      s k • gradient f (gradientDescentTrajectory f s x₀ k)

@[simp] theorem gradientDescentTrajectory_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (s : ℕ → ℝ) (x₀ : E) :
    gradientDescentTrajectory f s x₀ 0 = x₀ := rfl

theorem gradientDescentTrajectory_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (s : ℕ → ℝ) (x₀ : E) (k : ℕ) :
    gradientDescentTrajectory f s x₀ (k + 1) = gradientDescentTrajectory f s x₀ k -
      s k • gradient f (gradientDescentTrajectory f s x₀ k) := rfl

/-- Convex differentiable objectives with an actual one-Lipschitz gradient. -/
def IsUnitSmoothConvex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f ∧ LipschitzWith 1 (gradient f)

/-- Uniform last-iterate rate: the positive constant and cutoff precede every
dimension, objective, minimizer, initialization and horizon. -/
def GradientDescentUniformRate (s : ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧
    ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsUnitSmoothConvex f →
      ∀ xstar : EuclideanSpace ℝ (Fin d), (∀ x, f xstar ≤ f x) →
        ∀ x₀ : EuclideanSpace ℝ (Fin d), ∀ k : ℕ, K ≤ k →
          f (gradientDescentTrajectory f s x₀ k) - f xstar ≤
            C * ‖x₀ - xstar‖ ^ 2 / (k : ℝ) ^ c

/-- C35: the supremum of real exponents achievable by one predetermined schedule.
The supremum is taken in EReal, including its empty and unbounded conventions. -/
noncomputable def gradientDescentExponent : EReal :=
  sSup {r | ∃ c : ℝ, r = (c : EReal) ∧ ∃ s : ℕ → ℝ, GradientDescentUniformRate s c}

/-- The exact silver ratio used by the stepsize-hedging schedule. -/
noncomputable def gradientDescentSilverRatio : ℝ := 1 + Real.sqrt 2

/-- The catalogue's proposed optimal exponent, without decimal truncation. -/
noncomputable def silverGradientDescentExponent : ℝ :=
  Real.log gradientDescentSilverRatio / Real.log 2

/-- The zero-indexed silver schedule. Integer subtraction preserves the
negative exponent at even t, as in the primary construction. -/
noncomputable def silverGradientDescentSchedule (t : ℕ) : ℝ :=
  1 + gradientDescentSilverRatio ^ ((padicValNat 2 (t + 1) : ℤ) - 1)

/-- The existing fixed-step descent theorem supplies a uniform exponent-one
member of the optimization family, not its claimed optimum. -/
theorem gradientDescentUniformRate_one : GradientDescentUniformRate (fun _ => 1) 1 := by
  refine ⟨1 / 2, by norm_num, 1, by decide, ?_⟩
  intro d f hf xstar hmin x₀ k hk
  have h := MetaMathlibExt.gradient_descent_convex_sublinear_rate
    (f := f) (L := 1) (by norm_num) hf.1 hf.2.1 hf.2.2 hmin
    (η := 1) (by norm_num) (X := gradientDescentTrajectory f (fun _ => 1) x₀)
    (fun j => gradientDescentTrajectory_succ f (fun _ => 1) x₀ j)
    k (lt_of_lt_of_le (by decide : 0 < 1) hk)
  convert h using 1
  simp only [gradientDescentTrajectory_zero, Real.rpow_one]
  ring

/-- The actual optimization family is nonempty and C35 is at least one. -/
theorem one_le_gradientDescentExponent : (1 : EReal) ≤ gradientDescentExponent := by
  apply le_sSup
  exact ⟨1, by norm_num, fun _ => 1, gradientDescentUniformRate_one⟩

/-- Zero steps leave every initial point unchanged. -/
@[simp] theorem gradientDescentTrajectory_zeroSchedule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x₀ : E) (k : ℕ) :
    gradientDescentTrajectory f (fun _ => 0) x₀ k = x₀ := by
  induction k with
  | zero => rfl
  | succ k hk => simp [gradientDescentTrajectory_succ, hk]
