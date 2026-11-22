/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.FiniteLinking

/-!
# Tests for finite-grid 2PL scale linking

On the two-point grid with abilities 0 and 1 and one item: the pushed
law at `A = 2`, `B = 1` is accepted with expected total score
`(σ 0 + σ 1) / 2`; reweighting without transport is rejected; and a
zero discrimination at `A = -1` gives expected score `1/2`.
-/

@[expose] public section

/-! ## Tests: nonvacuity obligations
Fixture: grid `Fin 2` with uniform weights, abilities `0, 1`; one item.
The tests are proved from the production theorems above. -/

open MathlibExt.Probability.Statistics.Measurement MathlibExt.Probability.FiniteProbability
  MeasureTheory

/-- Fixture: uniform weights on the two-point grid. -/
private noncomputable def testGrid : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => 2⁻¹) (by simp [ENNReal.mul_inv_cancel])

private theorem testGrid_expectation (g : Fin 2 → ℝ) :
    expectation (fun z => (testGrid z).toReal) g = (g 0 + g 1) / 2 := by
  simp [expectation, testGrid, Fin.sum_univ_two]
  ring

private theorem pure_expectation (g : Fin 2 → ℝ) :
    expectation (fun z => ((PMF.pure (0 : Fin 2)) z).toReal) g = g 0 := by
  simp [expectation, Fin.sum_univ_two, PMF.pure_apply]

/-- Positive rescale and shift with the matching pushed law, `A = 2`, `B = 1`
(not the identity): both production theorems apply, the pushed latent law
genuinely differs from the original one, and the common expected total score
is `(σ 0 + σ 1) / 2`. -/
private theorem test_pushed_law_accepted :
    (∀ i : Fin 1, 0 < (fun _ => (1 : ℝ)) i / 2)
    ∧ testGrid.map ![(0 : ℝ), 1] ≠ (testGrid.map ![(0 : ℝ), 1]).map (fun θ => 2 * θ + 1)
    ∧ (testGrid.map ![(0 : ℝ), 1]).bind
        (fun θ => twoPLPMF (ι := Fin 1) (fun _ => 1) (fun _ => 0) θ)
      = ((testGrid.map ![(0 : ℝ), 1]).map (fun θ => 2 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (1 : ℝ)) i / 2)
            (fun i => 2 * (fun _ => (0 : ℝ)) i + 1) θ)
    ∧ ∫ x, (totalScore x : ℝ)
        ∂(((testGrid.map ![(0 : ℝ), 1]).map (fun θ => 2 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (1 : ℝ)) i / 2)
            (fun i => 2 * (fun _ => (0 : ℝ)) i + 1) θ)).toMeasure
      = (Real.sigmoid 0 + Real.sigmoid 1) / 2 := by
  have hpos := finiteMixture_twoPL_affine_of_pos (ι := Fin 1) testGrid ![(0 : ℝ), 1]
    (fun _ => 1) (fun _ => 0) 2 1 two_pos (fun _ => one_pos)
  have hgen := finiteMixture_twoPL_affine (ι := Fin 1) testGrid ![(0 : ℝ), 1]
    (fun _ => 1) (fun _ => 0) 2 1 two_ne_zero
  refine ⟨hpos.1, ?_, hpos.2, ?_⟩
  · intro h
    have h0 := congrArg (fun p : PMF ℝ => p 0) h
    simp [PMF.map_comp, PMF.map_apply, tsum_fintype, Fin.sum_univ_two, testGrid] at h0
    norm_num at h0
  · rw [← hgen.2.1, hgen.2.2, testGrid_expectation]
    simp

/-- Changing the grid weights without the corresponding law transport is not
accepted: keeping the transformed abilities and item parameters but moving all
weight to grid point `0` gives expected total score `σ 0 = 1/2`, against
`(σ 0 + σ 1) / 2 ≈ 0.6155` for the transported law, so the observed laws
differ too. -/
private theorem test_reweighted_rejected :
    (testGrid.map ![(0 : ℝ), 1]).bind
        (fun θ => twoPLPMF (ι := Fin 1) (fun _ => 1) (fun _ => 0) θ)
      ≠ (((PMF.pure (0 : Fin 2)).map ![(0 : ℝ), 1]).map (fun θ => 2 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (1 : ℝ)) i / 2)
            (fun i => 2 * (fun _ => (0 : ℝ)) i + 1) θ)
    ∧ ∫ x, (totalScore x : ℝ)
        ∂((testGrid.map ![(0 : ℝ), 1]).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun _ => 1) (fun _ => 0) θ)).toMeasure
      ≠ ∫ x, (totalScore x : ℝ)
        ∂((((PMF.pure (0 : Fin 2)).map ![(0 : ℝ), 1]).map (fun θ => 2 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (1 : ℝ)) i / 2)
            (fun i => 2 * (fun _ => (0 : ℝ)) i + 1) θ)).toMeasure := by
  have horig := finiteMixture_twoPL_affine (ι := Fin 1) testGrid ![(0 : ℝ), 1]
    (fun _ => 1) (fun _ => 0) 2 1 two_ne_zero
  have hpure := finiteMixture_twoPL_affine (ι := Fin 1) (PMF.pure (0 : Fin 2))
    ![(0 : ℝ), 1] (fun _ => 1) (fun _ => 0) 2 1 two_ne_zero
  have hne : ∫ x, (totalScore x : ℝ)
        ∂((testGrid.map ![(0 : ℝ), 1]).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun _ => 1) (fun _ => 0) θ)).toMeasure
      ≠ ∫ x, (totalScore x : ℝ)
        ∂((((PMF.pure (0 : Fin 2)).map ![(0 : ℝ), 1]).map (fun θ => 2 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (1 : ℝ)) i / 2)
            (fun i => 2 * (fun _ => (0 : ℝ)) i + 1) θ)).toMeasure := by
    rw [← hpure.2.1, hpure.2.2, horig.2.2, testGrid_expectation, pure_expectation]
    have h01 : Real.sigmoid 0 < Real.sigmoid 1 := Real.sigmoid_strictMono one_pos
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, one_mul]
    intro h
    linarith
  exact ⟨fun h => hne (by rw [h]), hne⟩

/-- Boundary outside the positive model: a zero discrimination with a
negative scale `A = -1` is covered by the general theorem; the item curve is
flat at `σ 0 = 1/2`, so the expected total score is `1/2` on both scales. -/
private theorem test_zero_discrimination :
    (testGrid.map ![(0 : ℝ), 1]).bind
        (fun θ => twoPLPMF (ι := Fin 1) (fun _ => 0) (fun _ => 0) θ)
      = ((testGrid.map ![(0 : ℝ), 1]).map (fun θ => -1 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (0 : ℝ)) i / -1)
            (fun i => -1 * (fun _ => (0 : ℝ)) i + 1) θ)
    ∧ ∫ x, (totalScore x : ℝ)
        ∂(((testGrid.map ![(0 : ℝ), 1]).map (fun θ => -1 * θ + 1)).bind
          (fun θ => twoPLPMF (ι := Fin 1) (fun i => (fun _ => (0 : ℝ)) i / -1)
            (fun i => -1 * (fun _ => (0 : ℝ)) i + 1) θ)).toMeasure
      = 1 / 2 := by
  have hgen := finiteMixture_twoPL_affine (ι := Fin 1) testGrid ![(0 : ℝ), 1]
    (fun _ => 0) (fun _ => 0) (-1) 1 (by norm_num)
  refine ⟨hgen.1, ?_⟩
  rw [← hgen.2.1, hgen.2.2, testGrid_expectation]
  simp [Real.sigmoid_zero]
