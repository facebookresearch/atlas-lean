/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-1016 (W. K. Hayman): for `f` meromorphic in the plane, with
`n(r) = sup_a` (number of roots of `f(z) = a` in `|z| < r`, counted with
multiplicity) and `A(r)` the normalized spherical-area integral, it is
known that `1 ≤ liminf_{r → ∞} n(r)/A(r) ≤ e`. Can `e` be replaced by
`1`, i.e. is `liminf_{r → ∞} n(r)/A(r) = 1`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.Analysis.HaymanSphericalAreaRatioWanted

/-! Source record `AMR-022-1016`. -/

/-- **Root count.** For $f\colon \mathbb{C} \to \mathbb{C}$, $a \in \mathbb{C}$ and real $r$, the
root count of $f$ at $a$ in radius $r$ is the number of roots of $f(z) = a$ in the open disk
$|z| < r$, counted with multiplicity: the sum over $z \in \mathbb{C}$ of the positive part of
the divisor of $f - a$ on that disk at $z$ (the sum is taken to be $0$ if infinitely many terms
are nonzero). -/
noncomputable def rootCount (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, (MeromorphicOn.divisor (fun z => f z - a) (Metric.ball 0 r) z).toNat

/-- **Maximum valence.** For $f\colon \mathbb{C} \to \mathbb{C}$ and real $r$, $n(f, r)$ is the
supremum in $\mathbb{R}$, over all $a \in \mathbb{C}$, of the root count of $f$ at $a$ in radius
$r$, that is, of the number of roots of $f(z) = a$ in $|z| < r$ counted with multiplicity.

This is a conditional supremum of real numbers, so it is meaningful only when these root counts
are bounded above as $a$ varies; see bounded root counts. -/
noncomputable def n (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range (fun a : ℂ => (rootCount f a r : ℝ)))

/-- **Spherical density.** For $f\colon \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$, the
spherical density of $f$ at $z$ is $|f'(z)|^2 / (1 + |f(z)|^2)^2$, where $f'(z)$ is the complex
derivative of $f$ at $z$, taken to be $0$ where $f$ is not differentiable. -/
noncomputable def sphericalDensity (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2

/-- **Normalized spherical area.** For $f\colon \mathbb{C} \to \mathbb{C}$ and real $r$, the
normalized spherical area $A(f, r)$ of $f$ on the disk $|z| < r$ is $\frac{1}{\pi}$ times the
Lebesgue integral of the spherical density of $f$ over the open disk
$\{z \in \mathbb{C} : |z| < r\}$ (the integral is taken to be $0$ if the density is not
integrable there). -/
noncomputable def A (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ z in Metric.ball (0 : ℂ) r, sphericalDensity f z

/-- **Germ-wise nonconstant function.** A function $f\colon \mathbb{C} \to \mathbb{C}$ is
nonconstant if there are points $u, v \in \mathbb{C}$ at which $f$ is complex differentiable and
$f(u) \ne f(v)$.

This excludes pointwise-modified constant functions (for example $f(0) = 1$ and $f(z) = 0$ for
$z \ne 0$), which are meromorphic with zero derivative density but represent the constant zero
germ. -/
def IsNonconstant (f : ℂ → ℂ) : Prop :=
  ∃ u v : ℂ, DifferentiableAt ℂ f u ∧ DifferentiableAt ℂ f v ∧ f u ≠ f v

/-- **Bounded root counts.** A function $f\colon \mathbb{C} \to \mathbb{C}$ has bounded root
counts if for every real $r$ the root counts of $f$ in radius $r$, that is, the numbers of roots
of $f(z) = a$ in $|z| < r$ counted with multiplicity, are bounded above as $a$ ranges over
$\mathbb{C}$.

This guarantees that the supremum over $a$ defining the maximum valence of $f$ in radius $r$ is
taken over a bounded set. -/
def HasBoundedRootCounts (f : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, BddAbove (Set.range (fun a : ℂ => (rootCount f a r : ℝ)))

/-- **Hayman's spherical-area ratio conjecture.** The statement that every function
$f\colon \mathbb{C} \to \mathbb{C}$ that is meromorphic on all of $\mathbb{C}$ and nonconstant
(complex differentiable at two points where it takes different values) has bounded root counts
(for every real $r$, the numbers of roots of $f(z) = a$ in $|z| < r$, counted with
multiplicity, are bounded above as $a$ ranges over $\mathbb{C}$) and satisfies
$$\liminf_{r \to \infty} \frac{n(f, r)}{A(f, r)} = 1,$$
where $n(f, r)$ is the supremum over $a \in \mathbb{C}$ of the number of roots of $f(z) = a$ in
$|z| < r$ counted with multiplicity, and $A(f, r)$ is the normalized spherical area of $f$ on
$|z| < r$.

For such $f$ it is known that $1 \le \liminf_{r \to \infty} n(f, r)/A(f, r) \le e$; Hayman asked
whether $e$ can be replaced by $1$. The statement is recorded as a proposition and is not
asserted.

Source: problem record AMR-022-1016 (W. K. Hayman). -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, MeromorphicOn f Set.univ → IsNonconstant f →
    HasBoundedRootCounts f ∧
      Filter.liminf (fun r : ℝ => n f r / A f r) Filter.atTop = 1

/--
**Hayman's spherical-area ratio conjecture is false.** Not every function
$f\colon \mathbb{C} \to \mathbb{C}$ that is meromorphic on all of $\mathbb{C}$ and nonconstant
(complex differentiable at two points where it takes different values) has bounded root counts
and satisfies $\liminf_{r \to \infty} n(f, r)/A(f, r) = 1$, where $n(f, r)$ is the maximum
valence and $A(f, r)$ the normalized spherical area of $f$ on the disk $|z| < r$.

Toppila constructed a nonconstant meromorphic function $f$ with
$\liminf_{r \to \infty} n(f, r)/A(f, r) \ge 80/79$, and Hinkkanen and Miles (arXiv:2401.13808,
2024, Theorem 1.1) give one with $\liminf_{r \to \infty} n(f, r)/A(f, r) \ge 1.07328$.

Source: A. Hinkkanen and J.
Miles, Maximum and Average Valence of Meromorphic Functions, arXiv preprint (2024),
arXiv:2401.13808, https://arxiv.org/abs/2401.13808. Moved from
`OpenConjectures/Analysis/HaymanSphericalAreaRatio`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.HaymanSphericalAreaRatioWanted
