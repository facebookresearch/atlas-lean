/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.KLS
public import MathlibExt.Probability.Geometry.UniformInterval

@[expose] public section

open MeasureTheory
open scoped ENNReal ContDiff
open MathlibExt.Probability.ThinShell
open MathlibExt.Probability.KLS

example (f : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ContDiff ℝ ∞ f ↔ ∀ m : ℕ, ContDiff ℝ m f := contDiff_infty

example (μ : Measure (EuclideanSpace ℝ (Fin 1))) : outerMinkowskiBoundary μ ∅ = 0 :=
  outerMinkowskiBoundary_empty μ

example : cheegerCoefficient (0 : Measure (EuclideanSpace ℝ (Fin 1))) = ⊤ :=
  cheegerCoefficient_zero

example : inverseCheegerConstant (0 : Measure (EuclideanSpace ℝ (Fin 1))) = 0 :=
  inverseCheegerConstant_zero

example (μ : Measure (EuclideanSpace ℝ (Fin 1))) :
    cheegerCoefficient μ ≤ halfspaceCheegerCoefficient μ :=
  cheegerCoefficient_le_halfspace μ

example {C D : ℝ≥0∞} {μ : Measure (EuclideanSpace ℝ (Fin 1))}
    (h : IsSmoothPoincareBound μ C) (hCD : C ≤ D) : IsSmoothPoincareBound μ D :=
  h.mono hCD

example {C : ℝ≥0∞} {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ)
    (h : klsConstant ≤ C) : inverseCheegerConstant μ ≤ C :=
  klsConstant_le_iff_measures.mp h n hn μ hμ

example : inverseCheegerConstant (uniformInterval (Real.sqrt 3)) ≤ klsConstant :=
  inverseCheegerConstant_le_constant (by decide)
    uniformInterval_sqrt_three_isIsotropicLogConcave
