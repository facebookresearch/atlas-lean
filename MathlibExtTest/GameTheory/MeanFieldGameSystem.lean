/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MeanFieldGameSystem
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open MeasureTheory Set MathlibExt.Probability.FokkerPlanck
  MathlibExt.GameTheory.MeanFieldGameSystem

namespace MathlibExtTest.GameTheory.MeanFieldGameSystem

/-- The unique probability measure on the one-point space `ℝ⁰ = Fin 0 → ℝ`. -/
noncomputable def pt : ProbabilityMeasure (Fin 0 → ℝ) :=
  ⟨Measure.dirac 0, inferInstance⟩

/-- Non-vacuity of `IsMFGClassicalSolution`, in the degenerate dimension `d = 0` (one state)
only:
with `F = G = 0` and `m₀ = 1`, the pair `u = 0`, `m = 1` is a classical solution on `[0, 1]`.
In this dimension the Lasry–Lions monotonicity condition of the wanted uniqueness theorem is
vacuous, as there is only one probability measure; a nondegenerate instance (a Gaussian
convolution coupling `F(x, m) = (ρ * m)(x)`) needs positive-definiteness of the Gaussian kernel
and is not formalised. -/
example : IsMFGClassicalSolution (d := 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1) 1
    (fun _ _ => 0) (fun _ _ => 1) (fun _ => pt) := by
  have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac 0 := by
    rw [Measure.volume_pi_eq_dirac]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨continuousOn_const, continuousOn_const, fun _ _ => ⟨contDiff_const, contDiff_const⟩,
    fun _ => ⟨contDiffOn_const, contDiffOn_const⟩, fun _ _ => ⟨fun _ => zero_le_one, ?_, ?_⟩, fun _ _ x => ?_,
    fun _ _ x => ?_, fun _ => rfl, fun _ => rfl⟩
  · simp [pt, hvol]
  · have : (fun x : Fin 0 → ℝ => ‖x‖) = fun _ => 0 := by
      funext x
      rw [Subsingleton.elim x 0, norm_zero]
    rw [this]
    exact integrable_zero _ _ _
  · simp [divergence]
  · simp [fokkerPlanckOp, divergence]

end MathlibExtTest.GameTheory.MeanFieldGameSystem
