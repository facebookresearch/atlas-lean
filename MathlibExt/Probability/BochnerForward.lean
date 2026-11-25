/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import MathlibExt.Analysis.Fourier.Bochner

/-!
# Bochner forward compatibility

The characteristic-function predicates follow the v1 TheoryOfProbability development.
The positive-definiteness predicate includes reality of the quadratic form, correcting the
v1 definition's missing imaginary-part condition. The complex and real forward implications
use `MathlibExt.Analysis.Fourier.BochnerWanted.bochner`, the existing full Bochner theorem.
-/

@[expose] public section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace ProbabilityTheory

/-- **Positive definite functions.** A function $\varphi : \mathbb{R} \to \mathbb{C}$ is
positive definite when for every $n \in \mathbb{N}$, all $t_1, \dots, t_n \in \mathbb{R}$ and all
$z_1, \dots, z_n \in \mathbb{C}$, the sum
$S = \sum_{i=1}^{n} \sum_{j=1}^{n} \varphi(t_i - t_j) \, z_i \, \overline{z_j}$ is real and
nonnegative, that is, $\operatorname{Im} S = 0$ and $\operatorname{Re} S \ge 0$. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (z : Fin n → ℂ),
    let S := ∑ i, ∑ j, φ (t i - t j) * z i * starRingEnd ℂ (z j)
    S.im = 0 ∧ 0 ≤ S.re

/-- **Positive definite real-valued functions.** A function $\varphi : \mathbb{R} \to \mathbb{R}$
is positive definite when its composition with the inclusion $\mathbb{R} \to \mathbb{C}$ is
positive definite, that is, when for every $n \in \mathbb{N}$, all
$t_1, \dots, t_n \in \mathbb{R}$ and all $z_1, \dots, z_n \in \mathbb{C}$, the sum
$\sum_{i=1}^{n} \sum_{j=1}^{n} \varphi(t_i - t_j) \, z_i \, \overline{z_j}$ is a nonnegative
real number. -/
def IsPositiveDefiniteReal (φ : ℝ → ℝ) : Prop :=
  IsPositiveDefinite ((↑) ∘ φ)

/-- **Characteristic functions.** A function $\varphi : \mathbb{R} \to \mathbb{C}$ is a
characteristic function when there is a probability measure $\mu$ on $\mathbb{R}$ whose
characteristic function equals $\varphi$, that is,
$\int_{\mathbb{R}} e^{itx} \, d\mu(x) = \varphi(t)$ for every $t \in \mathbb{R}$. -/
def IsCharacteristicFun (φ : ℝ → ℂ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = φ t

/-- **Real-valued characteristic functions.** A function $\varphi : \mathbb{R} \to \mathbb{R}$
is a real-valued characteristic function when its composition with the inclusion
$\mathbb{R} \to \mathbb{C}$ is a characteristic function, that is, when there is a probability
measure $\mu$ on $\mathbb{R}$ with $\int_{\mathbb{R}} e^{itx} \, d\mu(x) = \varphi(t)$ for every
$t \in \mathbb{R}$. -/
def IsCharacteristicFunReal (φ : ℝ → ℝ) : Prop :=
  IsCharacteristicFun ((↑) ∘ φ)

/-- **Forward direction of Bochner's theorem.** Let $\varphi : \mathbb{R} \to \mathbb{C}$ be the
characteristic function of a probability measure on $\mathbb{R}$. Then $\varphi$ is continuous,
positive definite, and satisfies $\varphi(0) = 1$. -/
theorem bochner_forward (φ : ℝ → ℂ) (hφ : IsCharacteristicFun φ) :
    Continuous φ ∧ IsPositiveDefinite φ ∧ φ 0 = 1 := by
  obtain ⟨μ, hμ, hμφ⟩ := hφ
  obtain ⟨hcont, h0, hpd⟩ :=
    (MathlibExt.Analysis.Fourier.BochnerWanted.bochner (f := φ)).mpr
      ⟨μ, hμ, fun t => (hμφ t).symm⟩
  refine ⟨hcont, ?_, h0⟩
  intro n t z
  simpa only [starRingEnd_apply, star_star, mul_assoc, mul_comm, mul_left_comm]
    using hpd n t (fun i => star (z i))

/-- **Characteristic functions are positive definite.** Let $\mu$ be a probability measure on
$\mathbb{R}$ with characteristic function $\varphi_\mu(t) = \int_{\mathbb{R}} e^{itx} \, d\mu(x)$.
Then $\varphi_\mu$ is positive definite: for every $n \in \mathbb{N}$, all
$t_1, \dots, t_n \in \mathbb{R}$ and all $z_1, \dots, z_n \in \mathbb{C}$, the sum
$\sum_{i=1}^{n} \sum_{j=1}^{n} \varphi_\mu(t_i - t_j) \, z_i \, \overline{z_j}$ is a nonnegative
real number. -/
theorem charFun_isPositiveDefinite (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsPositiveDefinite (charFun μ) :=
  (bochner_forward (charFun μ) ⟨μ, inferInstance, fun _ => rfl⟩).2.1

/-- **Real-valued characteristic functions are continuous and positive definite.** Let
$\varphi : \mathbb{R} \to \mathbb{R}$ be a real-valued characteristic function, that is, a
function whose composition with the inclusion $\mathbb{R} \to \mathbb{C}$ is the
characteristic function of a probability measure on $\mathbb{R}$. Then $\varphi$ is
continuous, $\varphi$ is positive definite in the sense that its composition with the
inclusion $\mathbb{R} \to \mathbb{C}$ is positive definite, and $\varphi(0) = 1$. -/
theorem bochner_forward_real (φ : ℝ → ℝ) (hφ : IsCharacteristicFunReal φ) :
    Continuous φ ∧ IsPositiveDefiniteReal φ ∧ φ 0 = 1 := by
  have hφ' : IsCharacteristicFun ((↑) ∘ φ) := hφ
  obtain ⟨hcont, hpd, h0⟩ := bochner_forward ((↑) ∘ φ) hφ'
  refine ⟨?_, hpd, ?_⟩
  · have hEq : φ = fun x => (Complex.ofReal (φ x)).re := by
      funext x
      simp
    rw [hEq]
    exact Complex.continuous_re.comp hcont
  · have h1 : Complex.ofReal (φ 0) = Complex.ofReal 1 := by
      simpa using h0
    exact Complex.ofReal_injective h1

end ProbabilityTheory
