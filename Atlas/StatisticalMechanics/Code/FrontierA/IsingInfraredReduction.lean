/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Finset Filter Set Topology
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

variable {Gamma : Type*} [Fintype Gamma] [AddCommGroup Gamma]



noncomputable def finiteTorusFourierCoeff
    (G : Gamma → ℝ) (chi : AddChar Gamma ℂ) : ℂ :=
  ∑ z : Gamma, (G z : ℂ) * chi z



noncomputable def finiteTorusQuadratic
    (G : Gamma → ℝ) (f : Gamma → ℂ) : ℂ :=
  ∑ x : Gamma, ∑ z : Gamma,
    conj (f x) * (G z : ℂ) * f (x + z)




def IsPositiveSemidefiniteTorusKernel (G : Gamma → ℝ) : Prop :=
  ∀ f : Gamma → ℂ, 0 ≤ (finiteTorusQuadratic G f).re




def HasFiniteTorusGaussianDomination
    (G : Gamma → ℝ) (inverseEnergy : (Gamma → ℂ) → ℝ) (C : ℝ) : Prop :=
  ∀ f : Gamma → ℂ, (∑ x : Gamma, f x) = 0 →
    (finiteTorusQuadratic G f).re ≤ C * inverseEnergy f




theorem finiteTorusQuadratic_addChar
    (G : Gamma → ℝ) (chi : AddChar Gamma ℂ) :
    finiteTorusQuadratic G chi =
      (Fintype.card Gamma : ℂ) * finiteTorusFourierCoeff G chi := by
  classical
  unfold finiteTorusQuadratic finiteTorusFourierCoeff
  calc
    (∑ x : Gamma, ∑ z : Gamma,
        conj (chi x) * (G z : ℂ) * chi (x + z)) =
        ∑ _x : Gamma, ∑ z : Gamma, (G z : ℂ) * chi z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      rw [AddChar.map_add_eq_mul, ← AddChar.inv_apply_eq_conj]
      have hne : chi x ≠ 0 := by
        intro hzero
        have hnorm := AddChar.norm_apply chi x
        simp [hzero] at hnorm
      field_simp
    _ = (Fintype.card Gamma : ℂ) *
        ∑ z : Gamma, (G z : ℂ) * chi z := by simp



theorem finiteTorus_addChar_sum_eq_zero
    (chi : AddChar Gamma ℂ) (hchi : chi ≠ 0) :
    (∑ x : Gamma, chi x) = 0 := by
  classical
  rw [AddChar.sum_eq_ite, if_neg hchi]



theorem finiteTorus_fourier_bound_of_gaussianDomination
    (G : Gamma → ℝ) (inverseEnergy : (Gamma → ℂ) → ℝ) (C delta : ℝ)
    (chi : AddChar Gamma ℂ) (hchi : chi ≠ 0)
    (hpsd : IsPositiveSemidefiniteTorusKernel G)
    (hgauss : HasFiniteTorusGaussianDomination G inverseEnergy C)
    (hmode : inverseEnergy chi = Fintype.card Gamma / delta) :
    0 ≤ (finiteTorusFourierCoeff G chi).re ∧
      (finiteTorusFourierCoeff G chi).re ≤ C / delta := by
  have hcardNat : 0 < Fintype.card Gamma := Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card Gamma := by exact_mod_cast hcardNat
  have hdiag := congrArg Complex.re (finiteTorusQuadratic_addChar G chi)
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hdiag
  have hnonnegQ := hpsd chi
  have hupperQ := hgauss chi (finiteTorus_addChar_sum_eq_zero chi hchi)
  rw [hmode] at hupperQ
  constructor
  · rw [hdiag] at hnonnegQ
    exact (mul_nonneg_iff_of_pos_left hcard).mp hnonnegQ
  · rw [hdiag] at hupperQ
    have hrhs : C * ((Fintype.card Gamma : ℝ) / delta) =
        (Fintype.card Gamma : ℝ) * (C / delta) := by ring
    rw [hrhs] at hupperQ
    nlinarith



theorem infrared_fourier_bound_of_tendsto
    (fourier dispersion : ℕ → ℝ) (C fourierLimit dispersionLimit : ℝ)
    (hfourier : Tendsto fourier atTop (nhds fourierLimit))
    (hdispersion : Tendsto dispersion atTop (nhds dispersionLimit))
    (hdispersionLimit : 0 < dispersionLimit)
    (hnonneg : ∀ n, 0 ≤ fourier n)
    (hbound : ∀ n, fourier n ≤ C / dispersion n) :
    0 ≤ fourierLimit ∧ fourierLimit ≤ C / dispersionLimit := by
  constructor
  · exact ge_of_tendsto hfourier (Eventually.of_forall hnonneg)
  · have hratio : Tendsto (fun n => C / dispersion n) atTop
        (nhds (C / dispersionLimit)) :=
      tendsto_const_nhds.div hdispersion hdispersionLimit.ne'
    exact le_of_tendsto_of_tendsto hfourier hratio
      (Eventually.of_forall hbound)




theorem infrared_average_tendsto_zero
    (averageFourier averageReciprocal : ℕ → ℝ) (C : ℝ)
    (hnonneg : ∀ n, 0 ≤ averageFourier n)
    (hbound : ∀ n, averageFourier n ≤ C * averageReciprocal n)
    (hreciprocal : Tendsto averageReciprocal atTop (nhds 0)) :
    Tendsto averageFourier atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall hnonneg) (Eventually.of_forall hbound)
  have hCr : Tendsto (fun n => C * averageReciprocal n) atTop (nhds (C * 0)) :=
    tendsto_const_nhds.mul hreciprocal
  simpa using hCr




theorem longRangeOrder_eq_zero_of_infrared_average
    (averageFourier averageReciprocal : ℕ → ℝ) (C m : ℝ)
    (hm : 0 ≤ m)
    (hmle : ∀ n, m ^ 2 ≤ averageFourier n)
    (hnonneg : ∀ n, 0 ≤ averageFourier n)
    (hbound : ∀ n, averageFourier n ≤ C * averageReciprocal n)
    (hreciprocal : Tendsto averageReciprocal atTop (nhds 0)) :
    m = 0 := by
  have havg := infrared_average_tendsto_zero averageFourier averageReciprocal
    C hnonneg hbound hreciprocal
  have hsq : m ^ 2 ≤ 0 := ge_of_tendsto havg
    (Eventually.of_forall hmle)
  nlinarith [sq_nonneg m]

end StatMech.FrontierA
