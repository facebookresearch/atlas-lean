/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.LatentMoments

/-!
# Finite-grid 2PL scale linking

Changing the ability scale by `θ ↦ A * θ + B` with `A ≠ 0`, pushing the
finite-grid latent law forward along the same map, and transforming
discriminations and difficulties by `a ↦ a / A` and `b ↦ A * b + B`
leaves the observed response law of the latent mixture unchanged, and
the expected total score is the sum of the grid-averaged item curves.
Under a positive scale change, positive discriminations stay positive.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory

private theorem bind_sum_aux {Z Y : Type*} [Fintype Z] [Fintype Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (pi : PMF Z) (κ : Z → PMF Y) (f : Y → ℝ) :
    (∑ y, ((pi.bind κ) y).toReal * f y)
      = ∑ z, (pi z).toReal * (∑ y, (((κ z) y).toReal * f y)) := by
  have hbind : ∀ y, ((pi.bind κ) y).toReal
      = ∑ z, (pi z).toReal * (((κ z) y).toReal) := by
    intro y
    rw [PMF.bind_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top
      (pi.apply_ne_top z) ((κ z).apply_ne_top y))]
    apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul]
  simp_rw [hbind, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem totalScore_eq_sum_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) :
    (totalScore x : ℝ) = ∑ i, (if x i then (1 : ℝ) else 0) := by
  unfold totalScore
  rw [Finset.card_filter]
  simp [Finset.sum_boole]

/-- **Finite-grid 2PL linking.** Let `Z` be a finite grid with latent law
`pi : PMF Z` and ability map `zeta : Z → ℝ`, so that the latent ability law is
`pi.map zeta`. Change the ability scale by `θ ↦ A * θ + B` with `A ≠ 0`, push
the latent law forward to `(pi.map zeta).map (fun θ => A * θ + B)`, and
transform discriminations and difficulties by the 2PL rule `a ↦ a / A`,
`b ↦ A * b + B` (Weeks 2010, (7), (8a), (8b)); discriminations of any sign
are allowed. Then the observed response law of the latent mixture is
unchanged, so is the expected total score, and that score is the sum over
items of the grid averages of the item curves. -/
theorem finiteMixture_twoPL_affine {Z ι : Type*} [Fintype Z] [Fintype ι]
    [DecidableEq ι] (pi : PMF Z) (zeta : Z → ℝ) (a b : ι → ℝ) (A B : ℝ)
    (hA : A ≠ 0) :
    (pi.map zeta).bind (fun θ => twoPLPMF a b θ)
      = ((pi.map zeta).map (fun θ => A * θ + B)).bind
          (fun θ => twoPLPMF (fun i => a i / A) (fun i => A * b i + B) θ)
    ∧ ∫ x, (totalScore x : ℝ) ∂((pi.map zeta).bind (fun θ => twoPLPMF a b θ)).toMeasure
      = ∫ x, (totalScore x : ℝ)
          ∂(((pi.map zeta).map (fun θ => A * θ + B)).bind
            (fun θ => twoPLPMF (fun i => a i / A) (fun i => A * b i + B) θ)).toMeasure
    ∧ ∫ x, (totalScore x : ℝ) ∂((pi.map zeta).bind (fun θ => twoPLPMF a b θ)).toMeasure
      = ∑ i, MathlibExt.Probability.FiniteProbability.expectation
          (fun z => (pi z).toReal) (fun z => Real.sigmoid (a i * (zeta z - b i))) := by
  have hbind : (pi.map zeta).bind (fun θ => twoPLPMF a b θ)
      = ((pi.map zeta).map (fun θ => A * θ + B)).bind
          (fun θ => twoPLPMF (fun i => a i / A) (fun i => A * b i + B) θ) := by
    rw [PMF.bind_map (pi.map zeta)]
    congr 1
    funext θ
    simp only [Function.comp_apply]
    exact twoPLPMF_affine a b θ A B hA
  refine ⟨hbind, ?_, ?_⟩
  · rw [hbind]
  · have hLHS : (pi.map zeta).bind (fun θ => twoPLPMF a b θ)
        = pi.bind (fun z => twoPLPMF a b (zeta z)) := by
      rw [PMF.bind_map pi]
      rfl
    rw [hLHS, PMF.integral_eq_sum]
    simp_rw [smul_eq_mul, totalScore_eq_sum_aux, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [bind_sum_aux]
    have hinner : ∀ z, (∑ y, (((twoPLPMF a b (zeta z)) y).toReal
        * (if y i then (1 : ℝ) else 0)))
        = Real.sigmoid (a i * (zeta z - b i)) := by
      intro z
      have hq0 : ∀ k, 0 ≤ (fun k => Real.sigmoid (a k * (zeta z - b k))) k :=
        fun k => le_of_lt (Real.sigmoid_pos _)
      have hq1 : ∀ k, (fun k => Real.sigmoid (a k * (zeta z - b k))) k ≤ 1 :=
        fun k => le_of_lt (Real.sigmoid_lt_one _)
      have h := (localIndepPMF_coordinate_moments
        (fun k => Real.sigmoid (a k * (zeta z - b k))) hq0 hq1).1 i
      rw [PMF.integral_eq_sum] at h
      simp_rw [smul_eq_mul] at h
      have heq : twoPLPMF a b (zeta z)
          = localIndepPMF (fun k => Real.sigmoid (a k * (zeta z - b k))) hq0 hq1 := by
        unfold twoPLPMF
        rfl
      rw [heq]
      exact h
    simp_rw [hinner]
    rfl

/-- Under a positive change of ability scale `θ ↦ A * θ + B` with `0 < A`,
positive discriminations stay positive after the 2PL rule `a ↦ a / A`, and
the observed response law of the finite-grid latent mixture is unchanged
when the latent law is pushed forward along the same map. -/
theorem finiteMixture_twoPL_affine_of_pos {Z ι : Type*} [Fintype Z] [Fintype ι]
    [DecidableEq ι] (pi : PMF Z) (zeta : Z → ℝ) (a b : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (ha : ∀ i, 0 < a i) :
    (∀ i, 0 < a i / A)
    ∧ (pi.map zeta).bind (fun θ => twoPLPMF a b θ)
      = ((pi.map zeta).map (fun θ => A * θ + B)).bind
          (fun θ => twoPLPMF (fun i => a i / A) (fun i => A * b i + B) θ) := by
  have hgen := finiteMixture_twoPL_affine pi zeta a b A B (ne_of_gt hA)
  exact ⟨fun i => div_pos (ha i) hA, hgen.1⟩

end MathlibExt.Probability.Statistics.Measurement
