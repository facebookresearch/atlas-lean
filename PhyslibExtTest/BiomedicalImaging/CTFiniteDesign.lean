/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalImaging.CTFiniteDesign

/-! Tests: design linearity under a zero measure is `0 = 0`. -/

namespace PhyslibExtTest.BiomedicalImaging.CTFiniteDesign

open PhyslibExt.BiomedicalImaging.CTFiniteDesign

/-- Under the zero measure both sides vanish. -/
example (phi : Fin 2 → ℝ → ℝ) (x : Fin 2 → ℝ) :
    (∫ a, (∑ i ∈ Finset.univ, x i * phi i a) ∂(0 : MeasureTheory.Measure ℝ)) =
      ∑ i ∈ Finset.univ, x i * (∫ a, phi i a ∂(0 : MeasureTheory.Measure ℝ)) :=
  ct_design_apply _ _ _ (fun i _ => MeasureTheory.integrable_zero_measure)

/-- Rays indexed separately from the two-dimensional domain. -/
example (mu : Fin 2 → MeasureTheory.Measure (Fin 2 → ℝ)) (phi : Fin 2 → (Fin 2 → ℝ) → ℝ)
    (x : Fin 2 → ℝ) (hint : ∀ i ∈ Finset.univ, MeasureTheory.Integrable (phi i) (mu 0)) :
    (∫ a, (∑ i ∈ Finset.univ, x i * phi i a) ∂(mu 0)) =
      ∑ i ∈ Finset.univ, x i * (∫ a, phi i a ∂(mu 0)) :=
  ct_design_apply (mu 0) phi x hint

/-- The design entry of a zero basis element vanishes at any ray. -/
example (xi : EuclideanSpace ℝ (Fin 2)) :
    ctDesignEntry (fun _ : Fin 2 => fun _ => (0:ℝ)) xi 3 0 = 0 := by
  unfold ctDesignEntry MetaMathlibExt.euclideanRadonTransform
  simp

/-- The Radon application law at a unit coordinate direction. -/
example : MetaMathlibExt.euclideanRadonTransform
      (fun a => ∑ i ∈ (Finset.univ : Finset (Fin 2)), (1:ℝ) * (fun _ => (0:ℝ)) a)
      (EuclideanSpace.single (0 : Fin 2) (1:ℝ)) 3 =
    ∑ i ∈ (Finset.univ : Finset (Fin 2)), (1:ℝ) * ctDesignEntry (fun _ : Fin 2 => fun _ => (0:ℝ))
      (EuclideanSpace.single (0 : Fin 2) (1:ℝ)) 3 i :=
  ct_design_radon_apply _ _ _ _
    (fun i _ => by simpa using MeasureTheory.integrableOn_zero)

end PhyslibExtTest.BiomedicalImaging.CTFiniteDesign
