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

/-- Outer boundary measured by the right-hand growth of actual closed neighbourhoods. -/
noncomputable def outerMinkowskiBoundary {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) (A : Set E) : ℝ≥0∞ :=
  Filter.liminf (fun ε : ℝ => (μ (Metric.cthickening ε A) - μ A) / ENNReal.ofReal ε)
    (nhdsWithin 0 (Set.Ioi 0))

/-- The infimum over Borel cuts of strictly positive, non-full probability mass. -/
noncomputable def cheegerCoefficient {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) : ℝ≥0∞ :=
  sInf {v | ∃ A : Set E, MeasurableSet A ∧ 0 < μ A ∧ μ A < 1 ∧
    outerMinkowskiBoundary μ A / min (μ A) (1 - μ A) = v}

/-- The inverse Cheeger coefficient; zero coefficient gives infinity. -/
noncomputable def inverseCheegerConstant {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) : ℝ≥0∞ :=
  (cheegerCoefficient μ)⁻¹

/-- A genuine closed affine half-space with a nonzero normal vector. -/
def IsHalfspace {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ a : ℝ, A = {x | inner ℝ v x ≤ a}

/-- The same boundary quotient with cuts restricted to actual affine half-spaces. -/
noncomputable def halfspaceCheegerCoefficient {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  sInf {v | ∃ A : Set (EuclideanSpace ℝ (Fin n)),
    MeasurableSet A ∧ IsHalfspace A ∧ 0 < μ A ∧ μ A < 1 ∧
      outerMinkowskiBoundary μ A / min (μ A) (1 - μ A) = v}

/-- The inverse half-space coefficient, again retaining infinity. -/
noncomputable def inverseHalfspaceCheegerConstant {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  (halfspaceCheegerCoefficient μ)⁻¹

/-- The worst inverse coefficient among actual isotropic log-concave laws in dimension `n`. -/
noncomputable def dimensionalKlsConstant (n : ℕ) : ℝ≥0∞ :=
  sSup {v | ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
    IsIsotropicLogConcave μ ∧ inverseCheegerConstant μ = v}

/-- The KLS constant is the supremum over every positive dimension. -/
noncomputable def klsConstant : ℝ≥0∞ :=
  sSup {v | ∃ n : ℕ, 0 < n ∧ dimensionalKlsConstant n = v}

/-- A simultaneous variance bound for smooth functions with finite mean, variance and energy. -/
def IsSmoothPoincareBound {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → Integrable f μ →
    Integrable (fun x => (f x) ^ 2) μ →
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ →
    (∫⁻ x, ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2) ∂μ) ≤
      C * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂μ

/-- The least simultaneous smooth-function Poincare bound, with infinity retained. -/
noncomputable def smoothPoincareConstant {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  sInf {C | IsSmoothPoincareBound μ C}

/-- The empty set has no outer Minkowski boundary. -/
theorem outerMinkowskiBoundary_empty {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) : outerMinkowskiBoundary μ ∅ = 0 := by
  simp [outerMinkowskiBoundary]

/-- The zero measure has no positive-mass cuts, so its Cheeger infimum is infinity. -/
theorem cheegerCoefficient_zero {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] :
    cheegerCoefficient (0 : Measure E) = ⊤ := by
  simp [cheegerCoefficient]

/-- Inversion does not mistake the empty cut family for an admissible probability law. -/
theorem inverseCheegerConstant_zero {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] :
    inverseCheegerConstant (0 : Measure E) = 0 := by
  simp [inverseCheegerConstant, cheegerCoefficient_zero]

/-- Restricting the cuts to half-spaces can only increase their infimum. -/
theorem cheegerCoefficient_le_halfspace {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    cheegerCoefficient μ ≤ halfspaceCheegerCoefficient μ := by
  apply sInf_le_sInf
  rintro v ⟨A, hA, _, hpos, hlt, rfl⟩
  exact ⟨A, hA, hpos, hlt, rfl⟩

/-- Every admissible law contributes its inverse coefficient to the dimensional supremum. -/
theorem inverseCheegerConstant_le_dimensional {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    inverseCheegerConstant μ ≤ dimensionalKlsConstant n := by
  exact le_sSup ⟨μ, hμ, rfl⟩

/-- Each positive dimension contributes its actual supremum to the global constant. -/
theorem dimensionalKlsConstant_le_constant {n : ℕ} (hn : 0 < n) :
    dimensionalKlsConstant n ≤ klsConstant := by
  exact le_sSup ⟨n, hn, rfl⟩

/-- A law in positive dimension is bounded by the global KLS constant. -/
theorem inverseCheegerConstant_le_constant {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    inverseCheegerConstant μ ≤ klsConstant := by
  exact (inverseCheegerConstant_le_dimensional hμ).trans
    (dimensionalKlsConstant_le_constant hn)

/-- The global constant is exactly the least bound for all positive dimensions. -/
theorem klsConstant_le_iff {C : ℝ≥0∞} :
    klsConstant ≤ C ↔ ∀ n : ℕ, 0 < n → dimensionalKlsConstant n ≤ C := by
  constructor
  · intro h n hn
    exact (dimensionalKlsConstant_le_constant hn).trans h
  · intro h
    apply sSup_le
    rintro v ⟨n, hn, rfl⟩
    exact h n hn

/-- The least-bound characterization quantifies over actual laws, not supplied numerical data. -/
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

/-- The KLS conjecture is equivalent to a finite real simultaneous bound. -/
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

/-- Increasing a supplied Poincare bound preserves its variance inequalities. -/
theorem IsSmoothPoincareBound.mono {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} {C D : ℝ≥0∞}
    (hC : IsSmoothPoincareBound μ C) (hCD : C ≤ D) : IsSmoothPoincareBound μ D := by
  intro f hf hi hi2 he
  exact (hC f hf hi hi2 he).trans (mul_le_mul hCD le_rfl bot_le bot_le)

/-- Every genuine simultaneous Poincare bound bounds the variational infimum. -/
theorem smoothPoincareConstant_le_of_bound {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} {C : ℝ≥0∞}
    (hC : IsSmoothPoincareBound μ C) : smoothPoincareConstant μ ≤ C := by
  exact sInf_le hC

end MathlibExt.Probability.KLS
