/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingInfraredReduction
import Code.Ising.GKS

open Finset
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

variable {Gamma Omega : Type*}
variable [Fintype Gamma] [AddCommGroup Gamma]




def HasFiniteStationaryGramRepresentation
    [Fintype Omega]
    (G : Gamma → ℝ) (weight : Omega → ℝ)
    (field : Omega → Gamma → ℝ) : Prop :=
  (∀ omega, 0 ≤ weight omega) ∧
    forall x z, G z =
      ∑ omega,
        weight omega * field omega x * field omega (x + z)

private theorem stationaryGram_reindex
    (field : Omega → Gamma → ℝ) (f : Gamma → ℂ)
    (omega : Omega) (x : Gamma) :
    (∑ z, field omega (x + z) * (f (x + z)).re) =
      ∑ y, field omega y * (f y).re := by
  simpa using
    (Equiv.sum_comp (Equiv.addLeft x)
      (fun y => field omega y * (f y).re))

private theorem stationaryGram_reindex_im
    (field : Omega → Gamma → ℝ) (f : Gamma → ℂ)
    (omega : Omega) (x : Gamma) :
    (∑ z, field omega (x + z) * (f (x + z)).im) =
      ∑ y, field omega y * (f y).im := by
  simpa using
    (Equiv.sum_comp (Equiv.addLeft x)
      (fun y => field omega y * (f y).im))

private theorem stationaryGram_real_square
    (field : Omega → Gamma → ℝ) (f : Gamma → ℂ)
    (omega : Omega) :
    (∑ x, ∑ z,
      field omega x * field omega (x + z) *
        ((f x).re * (f (x + z)).re)) =
      (∑ x, field omega x * (f x).re) ^ 2 := by
  simp_rw [mul_mul_mul_comm, ← Finset.mul_sum,
    stationaryGram_reindex field f omega]
  rw [← Finset.sum_mul]
  exact (pow_two (∑ x, field omega x * (f x).re)).symm

private theorem stationaryGram_im_square
    (field : Omega → Gamma → ℝ) (f : Gamma → ℂ)
    (omega : Omega) :
    (∑ x, ∑ z,
      field omega x * field omega (x + z) *
        ((f x).im * (f (x + z)).im)) =
      (∑ x, field omega x * (f x).im) ^ 2 := by
  simp_rw [mul_mul_mul_comm, ← Finset.mul_sum,
    stationaryGram_reindex_im field f omega]
  rw [← Finset.sum_mul]
  exact (pow_two (∑ x, field omega x * (f x).im)).symm

private theorem stationaryGram_term_re
    (a b : ℂ) (r : ℝ) :
    (conj a * (r : ℂ) * b).re =
      r * (a.re * b.re + a.im * b.im) := by
  simp [Complex.mul_re]
  ring

private theorem finite_sum_re {Alpha : Type*} [Fintype Alpha]
    (g : Alpha → ℂ) :
    (∑ a, g a).re = ∑ a, (g a).re := by
  exact map_sum RCLike.reCLM g Finset.univ



theorem finiteTorusQuadratic_re_eq_stationaryGram_squares
    [Fintype Omega]
    (G : Gamma → ℝ) (weight : Omega → ℝ)
    (field : Omega → Gamma → ℝ)
    (hrep : forall x z, G z =
      ∑ omega,
        weight omega * field omega x * field omega (x + z))
    (f : Gamma → ℂ) :
    (finiteTorusQuadratic G f).re =
      ∑ omega, weight omega *
        ((∑ x, field omega x * (f x).re) ^ 2 +
          (∑ x, field omega x * (f x).im) ^ 2) := by
  unfold finiteTorusQuadratic
  rw [finite_sum_re]
  simp_rw [finite_sum_re]
  simp_rw [stationaryGram_term_re]
  have hreplace (x z : Gamma) :
      G z * ((f x).re * (f (x + z)).re +
        (f x).im * (f (x + z)).im) =
        (∑ omega, weight omega * field omega x * field omega (x + z)) *
          ((f x).re * (f (x + z)).re +
            (f x).im * (f (x + z)).im) := by
    rw [hrep x z]
  simp_rw [hreplace]
  simp_rw [Finset.sum_mul]
  have hcomm :
      (∑ x, ∑ z, ∑ omega,
        weight omega * field omega x * field omega (x + z) *
          ((f x).re * (f (x + z)).re +
            (f x).im * (f (x + z)).im)) =
        ∑ omega, ∑ x, ∑ z,
          weight omega * field omega x * field omega (x + z) *
            ((f x).re * (f (x + z)).re +
              (f x).im * (f (x + z)).im) := by
    calc
      _ = ∑ x, ∑ omega, ∑ z,
          weight omega * field omega x * field omega (x + z) *
            ((f x).re * (f (x + z)).re +
              (f x).im * (f (x + z)).im) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro omega _
  have hfactor (x z : Gamma) :
      weight omega * field omega x * field omega (x + z) *
          ((f x).re * (f (x + z)).re +
            (f x).im * (f (x + z)).im) =
        weight omega *
          (field omega x * field omega (x + z) *
            ((f x).re * (f (x + z)).re +
              (f x).im * (f (x + z)).im)) := by ring
  simp_rw [hfactor, ← Finset.mul_sum]
  apply congrArg (fun t => weight omega * t)
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [stationaryGram_real_square field f omega,
    stationaryGram_im_square field f omega]




theorem isPositiveSemidefiniteTorusKernel_of_stationaryGram
    [Fintype Omega]
    (G : Gamma → ℝ) (weight : Omega → ℝ)
    (field : Omega → Gamma → ℝ)
    (hrep : HasFiniteStationaryGramRepresentation G weight field) :
    IsPositiveSemidefiniteTorusKernel G := by
  intro f
  rw [finiteTorusQuadratic_re_eq_stationaryGram_squares
    G weight field hrep.2 f]
  exact Finset.sum_nonneg fun omega _ =>
    mul_nonneg (hrep.1 omega) (add_nonneg (sq_nonneg _) (sq_nonneg _))




theorem finiteTorus_fourier_bound_of_stationaryGram_gaussianDomination
    [Fintype Omega]
    (G : Gamma → ℝ) (weight : Omega → ℝ)
    (field : Omega → Gamma → ℝ)
    (inverseEnergy : (Gamma → ℂ) → ℝ) (C delta : ℝ)
    (chi : AddChar Gamma ℂ) (hchi : chi ≠ 0)
    (hrep : HasFiniteStationaryGramRepresentation G weight field)
    (hgauss : HasFiniteTorusGaussianDomination G inverseEnergy C)
    (hmode : inverseEnergy chi = Fintype.card Gamma / delta) :
    0 ≤ (finiteTorusFourierCoeff G chi).re ∧
      (finiteTorusFourierCoeff G chi).re ≤ C / delta :=
  finiteTorus_fourier_bound_of_gaussianDomination G inverseEnergy C delta chi
    hchi (isPositiveSemidefiniteTorusKernel_of_stationaryGram
      G weight field hrep) hgauss hmode

section Ising

variable [DecidableEq Gamma]




theorem finiteIsing_hasFiniteStationaryGramRepresentation
    (H : SimpleGraph Gamma) [DecidableRel H.Adj]
    (beta h : ℝ) (G : Gamma → ℝ)
    (hstationary : ∀ x z, G z =
      ∑ sigma, Ising.isingProb H beta h sigma *
        (Ising.spin sigma x -
          Ising.isingExpectation H beta h (fun tau => Ising.spin tau x)) *
        (Ising.spin sigma (x + z) -
          Ising.isingExpectation H beta h
            (fun tau => Ising.spin tau (x + z)))) :
    HasFiniteStationaryGramRepresentation G (Ising.isingProb H beta h)
      (fun sigma x => Ising.spin sigma x -
        Ising.isingExpectation H beta h (fun tau => Ising.spin tau x)) := by
  exact ⟨Ising.isingProb_nonneg H beta h, hstationary⟩




theorem finiteIsingTorus_fourier_bound_of_gaussianDomination
    (H : SimpleGraph Gamma) [DecidableRel H.Adj]
    (beta h : ℝ) (G : Gamma → ℝ)
    (inverseEnergy : (Gamma → ℂ) → ℝ) (C delta : ℝ)
    (chi : AddChar Gamma ℂ) (hchi : chi ≠ 0)
    (hstationary : ∀ x z, G z =
      ∑ sigma, Ising.isingProb H beta h sigma *
        (Ising.spin sigma x -
          Ising.isingExpectation H beta h (fun tau => Ising.spin tau x)) *
        (Ising.spin sigma (x + z) -
          Ising.isingExpectation H beta h
            (fun tau => Ising.spin tau (x + z))))
    (hgauss : HasFiniteTorusGaussianDomination G inverseEnergy C)
    (hmode : inverseEnergy chi = Fintype.card Gamma / delta) :
    0 ≤ (finiteTorusFourierCoeff G chi).re ∧
      (finiteTorusFourierCoeff G chi).re ≤ C / delta :=
  finiteTorus_fourier_bound_of_stationaryGram_gaussianDomination G
    (Ising.isingProb H beta h)
    (fun sigma x => Ising.spin sigma x -
      Ising.isingExpectation H beta h (fun tau => Ising.spin tau x))
    inverseEnergy C delta chi hchi
    (finiteIsing_hasFiniteStationaryGramRepresentation H beta h G hstationary)
    hgauss hmode

end Ising

end StatMech.FrontierA
