/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minkowski boundary and KLS constants
-/
module

public import MathlibExt.Probability.Geometry.ThinShell
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

open MeasureTheory
open scoped ENNReal Topology ContDiff
open MathlibExt.Probability.ThinShell

namespace MathlibExt.Probability.KLS

/-- **Outer Minkowski boundary measure.** Let $\mu$ be a measure on a pseudometric space $E$ and
let $A \subseteq E$. For $\varepsilon > 0$ let
$A_\varepsilon = \{x \in E : \inf_{a \in A} d(x, a) \le \varepsilon\}$ be the closed
$\varepsilon$-neighbourhood of $A$, with $\inf \emptyset = \infty$. The outer Minkowski boundary
measure of $A$ with respect to $\mu$ is
$$\mu^+(A) = \liminf_{\varepsilon \to 0^+} \frac{\mu(A_\varepsilon) - \mu(A)}{\varepsilon},$$
where the difference and the quotient are computed in $[0, \infty]$, with $\infty - \infty = 0$. -/
noncomputable def outerMinkowskiBoundary {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) (A : Set E) : ℝ≥0∞ :=
  Filter.liminf (fun ε : ℝ => (μ (Metric.cthickening ε A) - μ A) / ENNReal.ofReal ε)
    (nhdsWithin 0 (Set.Ioi 0))

/-- **Cheeger coefficient.** For a measure $\mu$ on a pseudometric space $E$ equipped with a
σ-algebra, the Cheeger coefficient of $\mu$ is the infimum in $[0, \infty]$ of
$\mu^+(A) / \min(\mu(A), 1 - \mu(A))$ over all measurable sets $A \subseteq E$ with
$0 < \mu(A) < 1$, where
$\mu^+(A) = \liminf_{\varepsilon \to 0^+} (\mu(A_\varepsilon) - \mu(A)) / \varepsilon$ is the
outer Minkowski boundary measure of $A$ and $A_\varepsilon$ is the closed
$\varepsilon$-neighbourhood of $A$. The infimum of the empty family is $\infty$; the measure
$\mu$ is not required to be a probability measure. -/
noncomputable def cheegerCoefficient {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) : ℝ≥0∞ :=
  sInf {v | ∃ A : Set E, MeasurableSet A ∧ 0 < μ A ∧ μ A < 1 ∧
    outerMinkowskiBoundary μ A / min (μ A) (1 - μ A) = v}

/-- **Inverse Cheeger constant.** For a measure $\mu$ on a pseudometric space $E$ equipped with a
σ-algebra, the inverse Cheeger constant of $\mu$ is $1 / h(\mu) \in [0, \infty]$, where $h(\mu)$
is the Cheeger coefficient of $\mu$, with the conventions $1 / 0 = \infty$ and
$1 / \infty = 0$. -/
noncomputable def inverseCheegerConstant {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) : ℝ≥0∞ :=
  (cheegerCoefficient μ)⁻¹

/-- **Half-spaces.** A set $A \subseteq \mathbb{R}^n$ is a half-space if there are a nonzero
vector $v \in \mathbb{R}^n$ and a real number $a$ such that
$A = \{x \in \mathbb{R}^n : \langle v, x \rangle \le a\}$. -/
def IsHalfspace {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ a : ℝ, A = {x | inner ℝ v x ≤ a}

/-- **Half-space Cheeger coefficient.** For a measure $\mu$ on $\mathbb{R}^n$ with the Euclidean
metric, the half-space Cheeger coefficient of $\mu$ is the infimum in $[0, \infty]$ of
$\mu^+(H) / \min(\mu(H), 1 - \mu(H))$ over all closed half-spaces
$H = \{x : \langle v, x \rangle \le a\}$ with $v \ne 0$ and $a \in \mathbb{R}$ such that
$0 < \mu(H) < 1$, where $\mu^+(H)$ is the outer Minkowski boundary measure of $H$. The infimum
of the empty family is $\infty$. -/
noncomputable def halfspaceCheegerCoefficient {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  sInf {v | ∃ A : Set (EuclideanSpace ℝ (Fin n)),
    MeasurableSet A ∧ IsHalfspace A ∧ 0 < μ A ∧ μ A < 1 ∧
      outerMinkowskiBoundary μ A / min (μ A) (1 - μ A) = v}

/-- **Inverse half-space Cheeger constant.** For a measure $\mu$ on $\mathbb{R}^n$, the inverse
half-space Cheeger constant of $\mu$ is $h^{-1}$, where $h \in [0, \infty]$ is the half-space
Cheeger coefficient of $\mu$ and the inverse is taken in $[0, \infty]$, so that
$0^{-1} = \infty$ and $\infty^{-1} = 0$. -/
noncomputable def inverseHalfspaceCheegerConstant {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  (halfspaceCheegerCoefficient μ)⁻¹

/-- **Dimensional KLS constant.** For $n \in \mathbb{N}$, the dimensional KLS constant in
dimension $n$ is the supremum in $[0, \infty]$ of the inverse Cheeger constants of all isotropic
log-concave probability measures on $\mathbb{R}^n$ with the Euclidean metric. -/
noncomputable def dimensionalKlsConstant (n : ℕ) : ℝ≥0∞ :=
  sSup {v | ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
    IsIsotropicLogConcave μ ∧ inverseCheegerConstant μ = v}

/-- **KLS constant.** The KLS constant is the supremum in $[0, \infty]$ of the dimensional KLS
constants in dimension $n$, taken over all positive integers $n$. -/
noncomputable def klsConstant : ℝ≥0∞ :=
  sSup {v | ∃ n : ℕ, 0 < n ∧ dimensionalKlsConstant n = v}

/-- **Smooth Poincaré bounds.** Let $\mu$ be a measure on $\mathbb{R}^n$ and let
$C \in [0, \infty]$. For a differentiable $g : \mathbb{R}^n \to \mathbb{R}$ write
$\|\nabla g(x)\|$ for the Euclidean norm of the gradient of $g$ at $x$ (equivalently, the
operator norm of the derivative of $g$ at $x$). Then $C$ is a smooth Poincaré bound for $\mu$
if for every infinitely differentiable function $f : \mathbb{R}^n \to \mathbb{R}$ such that
$f$, $f^2$ and $\|\nabla f\|^2$ are $\mu$-integrable,
$$\int \Big(f(x) - \int f \, d\mu\Big)^2 \, d\mu(x) \le C \int \|\nabla f(x)\|^2 \, d\mu(x),$$
where the outer integral on the left and the integral on the right are computed in
$[0, \infty]$ with $0 \cdot \infty = 0$, and the inner integral $\int f \, d\mu$ is the usual
real integral. The measure $\mu$ need not be a probability measure. -/
def IsSmoothPoincareBound {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → Integrable f μ →
    Integrable (fun x => (f x) ^ 2) μ →
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ →
    (∫⁻ x, ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2) ∂μ) ≤
      C * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂μ

/-- **Smooth Poincaré constant.** The smooth Poincaré constant of a measure $\mu$ on $\mathbb{R}^n$
is the infimum in $[0, \infty]$ of all $C \in [0, \infty]$ that are smooth Poincaré bounds for
$\mu$; it is $\infty$ when $\mu$ has no smooth Poincaré bound. -/
noncomputable def smoothPoincareConstant {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  sInf {C | IsSmoothPoincareBound μ C}

/-- **The empty set has zero outer Minkowski boundary.** For every measure $\mu$ on a
pseudometric space $E$, the outer Minkowski boundary measure of the empty set with respect to
$\mu$ is $0$. -/
theorem outerMinkowskiBoundary_empty {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) : outerMinkowskiBoundary μ ∅ = 0 := by
  simp [outerMinkowskiBoundary]

/-- **Cheeger coefficient of the zero measure.** On every pseudometric space $E$ equipped with a
σ-algebra, the zero measure has Cheeger coefficient $\infty$.

No set has measure strictly between $0$ and $1$ under the zero measure, so the infimum is taken
over the empty family. -/
theorem cheegerCoefficient_zero {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] :
    cheegerCoefficient (0 : Measure E) = ⊤ := by
  simp [cheegerCoefficient]

/-- **Inverse Cheeger constant of the zero measure.** On every pseudometric space $E$ equipped
with a σ-algebra, the zero measure has inverse Cheeger constant $0$. -/
theorem inverseCheegerConstant_zero {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] :
    inverseCheegerConstant (0 : Measure E) = 0 := by
  simp [inverseCheegerConstant, cheegerCoefficient_zero]

/-- **The Cheeger coefficient is at most the half-space Cheeger coefficient.** For every measure
$\mu$ on $\mathbb{R}^n$ with the Euclidean metric, the Cheeger coefficient of $\mu$ is at most
its half-space Cheeger coefficient. -/
theorem cheegerCoefficient_le_halfspace {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    cheegerCoefficient μ ≤ halfspaceCheegerCoefficient μ := by
  apply sInf_le_sInf
  rintro v ⟨A, hA, _, hpos, hlt, rfl⟩
  exact ⟨A, hA, hpos, hlt, rfl⟩

/-- **Inverse Cheeger constant bounded by the dimensional KLS constant.** For every
$n \in \mathbb{N}$ and every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$
with the Euclidean metric, the inverse Cheeger constant of $\mu$ is at most the dimensional KLS
constant in dimension $n$. -/
theorem inverseCheegerConstant_le_dimensional {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    inverseCheegerConstant μ ≤ dimensionalKlsConstant n := by
  exact le_sSup ⟨μ, hμ, rfl⟩

/-- **Dimensional KLS constants are bounded by the KLS constant.** For every positive integer
$n$, the dimensional KLS constant in dimension $n$ is at most the KLS constant. -/
theorem dimensionalKlsConstant_le_constant {n : ℕ} (hn : 0 < n) :
    dimensionalKlsConstant n ≤ klsConstant := by
  exact le_sSup ⟨n, hn, rfl⟩

/-- **Inverse Cheeger constant bounded by the KLS constant.** For every positive integer $n$ and
every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$ with the Euclidean
metric, the inverse Cheeger constant of $\mu$ is at most the KLS constant. -/
theorem inverseCheegerConstant_le_constant {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    inverseCheegerConstant μ ≤ klsConstant := by
  exact (inverseCheegerConstant_le_dimensional hμ).trans
    (dimensionalKlsConstant_le_constant hn)

/-- **Bounding the KLS constant dimension by dimension.** For every $C \in [0, \infty]$, the KLS
constant is at most $C$ if and only if, for every positive integer $n$, the dimensional KLS
constant in dimension $n$ is at most $C$. -/
theorem klsConstant_le_iff {C : ℝ≥0∞} :
    klsConstant ≤ C ↔ ∀ n : ℕ, 0 < n → dimensionalKlsConstant n ≤ C := by
  constructor
  · intro h n hn
    exact (dimensionalKlsConstant_le_constant hn).trans h
  · intro h
    apply sSup_le
    rintro v ⟨n, hn, rfl⟩
    exact h n hn

/-- **Bounding the KLS constant measure by measure.** For every $C \in [0, \infty]$, the KLS
constant is at most $C$ if and only if, for every positive integer $n$ and every isotropic
log-concave probability measure $\mu$ on $\mathbb{R}^n$, the inverse Cheeger constant of $\mu$ is
at most $C$. -/
theorem klsConstant_le_iff_measures {C : ℝ≥0∞} :
    klsConstant ≤ C ↔ ∀ n : ℕ, 0 < n →
      ∀ μ : Measure (EuclideanSpace ℝ (Fin n)), IsIsotropicLogConcave μ →
        inverseCheegerConstant μ ≤ C := by
  constructor
  · intro h n hn μ hμ
    exact (inverseCheegerConstant_le_constant hn hμ).trans h
  · intro h
    apply klsConstant_le_iff.mpr
    intro n hn
    apply sSup_le
    rintro v ⟨μ, hμ, rfl⟩
    exact h n hn μ hμ

/-- **Finiteness of the KLS constant.** The KLS constant is finite if and only if there is a real
number $C$ such that, for every positive integer $n$ and every isotropic log-concave probability
measure $\mu$ on $\mathbb{R}^n$, the inverse Cheeger constant of $\mu$ is at most $\max(C, 0)$.

The right-hand side is the Kannan–Lovász–Simonovits (KLS) conjecture. -/
theorem klsConstant_lt_top_iff : klsConstant < ⊤ ↔
    ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      ∀ μ : Measure (EuclideanSpace ℝ (Fin n)), IsIsotropicLogConcave μ →
        inverseCheegerConstant μ ≤ ENNReal.ofReal C := by
  constructor
  · intro h
    refine ⟨klsConstant.toReal, ?_⟩
    apply klsConstant_le_iff_measures.mp
    rw [ENNReal.ofReal_toReal (ne_of_lt h)]
  · rintro ⟨C, hC⟩
    exact lt_of_le_of_lt (klsConstant_le_iff_measures.mpr hC) ENNReal.ofReal_lt_top

/-- **Smooth Poincaré bounds are upward closed.** Let $\mu$ be a measure on $\mathbb{R}^n$ and let
$C \le D$ in $[0, \infty]$. If $C$ is a smooth Poincaré bound for $\mu$, then so is $D$. -/
theorem IsSmoothPoincareBound.mono {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} {C D : ℝ≥0∞}
    (hC : IsSmoothPoincareBound μ C) (hCD : C ≤ D) : IsSmoothPoincareBound μ D := by
  intro f hf hi hi2 he
  exact (hC f hf hi hi2 he).trans (mul_le_mul hCD le_rfl bot_le bot_le)

/-- **The smooth Poincaré constant is at most every smooth Poincaré bound.** Let $\mu$ be a
measure on $\mathbb{R}^n$ and let $C \in [0, \infty]$. If $C$ is a smooth Poincaré bound for
$\mu$, then the smooth Poincaré constant of $\mu$ is at most $C$. -/
theorem smoothPoincareConstant_le_of_bound {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} {C : ℝ≥0∞}
    (hC : IsSmoothPoincareBound μ C) : smoothPoincareConstant μ ≤ C := by
  exact sInf_le hC

end MathlibExt.Probability.KLS
