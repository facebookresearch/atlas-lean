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

/-- **Gradient descent with a step schedule.** Let $E$ be a real Hilbert space,
$f : E \to \mathbb{R}$, $s : \mathbb{N} \to \mathbb{R}$ a sequence of step sizes and $x_0 \in E$.
The gradient descent trajectory of $f$ from $x_0$ with steps $s$ is the sequence
$(x_k)_{k \in \mathbb{N}}$ in $E$ starting at $x_0$ with $x_{k+1} = x_k - s_k \nabla f(x_k)$.

Here $\nabla f(x)$ is taken to be $0$ at points $x$ where $f$ is not differentiable. -/
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

/-- **Convex functions with $1$-Lipschitz gradient.** A function $f : E \to \mathbb{R}$ on a real
Hilbert space $E$ is unit-smooth convex if it is convex, differentiable, and its gradient is
$1$-Lipschitz: $\lVert \nabla f(x) - \nabla f(y) \rVert \le \lVert x - y \rVert$ for all
$x, y \in E$. -/
def IsUnitSmoothConvex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f ∧ LipschitzWith 1 (gradient f)

/-- **Uniform last-iterate rate of a step schedule.** A step schedule
$s : \mathbb{N} \to \mathbb{R}$ achieves a uniform last-iterate rate with exponent
$c \in \mathbb{R}$ if there are a real number $C > 0$ and an integer $K \ge 1$ with the following
property. For every $d \in \mathbb{N}$, every convex differentiable function
$f : \mathbb{R}^d \to \mathbb{R}$ whose gradient is $1$-Lipschitz for the Euclidean norm, every
$x^\star \in \mathbb{R}^d$ with $f(x^\star) \le f(x)$ for all $x$, every $x_0 \in \mathbb{R}^d$ and
every integer $k \ge K$, the $k$-th gradient descent iterate $x_k$ of $f$ from $x_0$ with steps
$s$ satisfies
$$f(x_k) - f(x^\star) \le \frac{C \lVert x_0 - x^\star \rVert^2}{k^c}.$$

The constants $C$ and $K$ are chosen before, and do not depend on, $d$, $f$, $x^\star$, $x_0$
and $k$. -/
def GradientDescentUniformRate (s : ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧
    ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsUnitSmoothConvex f →
      ∀ xstar : EuclideanSpace ℝ (Fin d), (∀ x, f xstar ≤ f x) →
        ∀ x₀ : EuclideanSpace ℝ (Fin d), ∀ k : ℕ, K ≤ k →
          f (gradientDescentTrajectory f s x₀ k) - f xstar ≤
            C * ‖x₀ - xstar‖ ^ 2 / (k : ℝ) ^ c

/-- **The gradient descent exponent.** The gradient descent exponent is the supremum, in the
extended reals $[-\infty, +\infty]$, of the set of real numbers $c$ such that some step schedule
$s : \mathbb{N} \to \mathbb{R}$ achieves a uniform last-iterate rate with exponent $c$. In
particular, it is $-\infty$ if there is no such $c$, and $+\infty$ if these exponents are
unbounded above.

Source: OptimizationProblems, `constants/35a.md` (constant C35). -/
noncomputable def gradientDescentExponent : EReal :=
  sSup {r | ∃ c : ℝ, r = (c : EReal) ∧ ∃ s : ℕ → ℝ, GradientDescentUniformRate s c}

/-- **Silver ratio.** The silver ratio is the real number $\rho = 1 + \sqrt{2}$.

It is the ratio used by the stepsize-hedging (silver) step schedule. -/
noncomputable def gradientDescentSilverRatio : ℝ := 1 + Real.sqrt 2

/-- **Silver exponent.** The silver exponent is $\log_2 \rho = \log \rho / \log 2$, where
$\rho = 1 + \sqrt{2}$ is the silver ratio.

It is the catalogue's proposed optimal value of the gradient descent exponent. -/
noncomputable def silverGradientDescentExponent : ℝ :=
  Real.log gradientDescentSilverRatio / Real.log 2

/-- **Silver step schedule.** The silver step schedule is the sequence
$s_t = 1 + \rho^{\nu_2(t + 1) - 1}$ for $t \in \mathbb{N}$, where $\rho = 1 + \sqrt{2}$ is the
silver ratio and $\nu_2(n)$ is the exponent of $2$ in the prime factorization of $n$.

The exponent $\nu_2(t + 1) - 1$ is an integer and equals $-1$ for even $t$, where
$s_t = 1 + \rho^{-1} = \sqrt{2}$. -/
noncomputable def silverGradientDescentSchedule (t : ℕ) : ℝ :=
  1 + gradientDescentSilverRatio ^ ((padicValNat 2 (t + 1) : ℤ) - 1)

/-- **Constant unit steps achieve exponent one.** The step schedule with every step size equal to
$1$ achieves a uniform last-iterate rate with exponent $1$.

This follows from the fixed-step descent theorem; it is a lower bound for the gradient descent
exponent, not its conjectured optimal value. -/
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

/-- **The gradient descent exponent is at least one.** The gradient descent exponent is at
least $1$. -/
theorem one_le_gradientDescentExponent : (1 : EReal) ≤ gradientDescentExponent := by
  apply le_sSup
  exact ⟨1, by norm_num, fun _ => 1, gradientDescentUniformRate_one⟩

/-- **Gradient descent with zero step sizes stays put.** Let $E$ be a real Hilbert space,
$f : E \to \mathbb{R}$ and $x_0 \in E$. If every step size is $0$, then for every $k \in \mathbb{N}$
the $k$-th gradient descent iterate of $f$ from $x_0$ equals $x_0$. -/
@[simp] theorem gradientDescentTrajectory_zeroSchedule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x₀ : E) (k : ℕ) :
    gradientDescentTrajectory f (fun _ => 0) x₀ k = x₀ := by
  induction k with
  | zero => rfl
  | succ k hk => simp [gradientDescentTrajectory_succ, hk]
