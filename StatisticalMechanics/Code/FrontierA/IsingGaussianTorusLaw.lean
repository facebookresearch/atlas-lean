/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusLaplacianNormalization
import Code.FK.HolleyCoupling










open Finset MeasureTheory
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising

noncomputable section

variable {d k : Nat}


def isingTorusZeroFieldMass (beta : Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) : Real :=
  Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma)) /
    isingTorusShiftedPartition (d := d) (k := k) beta 0

theorem isingTorusZeroFieldMass_nonneg (beta : Real) :
    0 <= isingTorusZeroFieldMass (d := d) (k := k) beta := by
  intro sigma
  exact div_nonneg (Real.exp_pos _).le
    (isingTorusShiftedPartition_zero_pos beta).le

theorem sum_isingTorusZeroFieldMass (beta : Real) :
    ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      isingTorusZeroFieldMass beta sigma = 1 := by
  have hZ := isingTorusShiftedPartition_zero_pos
    (d := d) (k := k) beta
  unfold isingTorusZeroFieldMass isingTorusShiftedPartition
  rw [← Finset.sum_div Finset.univ]
  simp only [add_zero]
  apply div_self
  simpa only [isingTorusShiftedPartition, Pi.zero_apply, add_zero] using hZ.ne'



def isingTorusZeroFieldLaw (beta : Real) :
    ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)) :=
  ⟨FK.measOfMass (isingTorusZeroFieldMass beta),
    FK.measOfMass_isProbabilityMeasure _
      (isingTorusZeroFieldMass_nonneg beta)
      (sum_isingTorusZeroFieldMass beta)⟩

theorem isingTorusZeroFieldLaw_real_singleton (beta : Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ((isingTorusZeroFieldLaw (d := d) (k := k) beta :
        ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k))) :
      Measure (ConfigSpace (IsingDyadicTorus d k))).real {sigma} =
      isingTorusZeroFieldMass beta sigma := by
  rw [isingTorusZeroFieldLaw, ProbabilityMeasure.coe_mk,
    FK.measOfMass_real _ (isingTorusZeroFieldMass_nonneg beta)]
  simp



theorem integral_isingTorusZeroFieldLaw (beta : Real)
    (g : ConfigSpace (IsingDyadicTorus d k) -> Real) :
    ∫ sigma, g sigma
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k))) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        isingTorusZeroFieldMass beta sigma * g sigma := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [isingTorusZeroFieldLaw_real_singleton beta, smul_eq_mul]


def isingTorusSmearedSpin (f : IsingDyadicTorus d k -> Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) : Real :=
  ∑ x, isingTorusSpinField sigma x * f x



theorem integral_exp_isingTorusSmearedSpin_le
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k -> Real)
    (hpotential : forall u : IsingDyadicTorus d k -> Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∫ sigma, Real.exp (s * isingTorusSmearedSpin f sigma)
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
      Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  rw [integral_isingTorusZeroFieldLaw]
  unfold isingTorusZeroFieldMass isingTorusSmearedSpin
  calc
    (∑ sigma,
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) /
          isingTorusShiftedPartition beta 0 *
            Real.exp (s * ∑ x, isingTorusSpinField sigma x * f x)) =
        (∑ sigma,
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
              Real.exp (s * ∑ x,
                isingTorusSpinField sigma x * f x)) /
          isingTorusShiftedPartition beta 0 := by
      rw [Finset.sum_div Finset.univ]
      apply Finset.sum_congr rfl
      intro sigma _
      ring
    _ <= _ := isingTorus_linear_expMoment_le_unconditional
      beta hbeta f h hpotential s


theorem integral_exp_abs_isingTorusSmearedSpin_le
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k -> Real)
    (hpotential : forall u : IsingDyadicTorus d k -> Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∫ sigma, Real.exp (s * |isingTorusSmearedSpin f sigma|)
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
      2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  rw [integral_isingTorusZeroFieldLaw]
  unfold isingTorusZeroFieldMass isingTorusSmearedSpin
  calc
    (∑ sigma,
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) /
          isingTorusShiftedPartition beta 0 *
            Real.exp (s * |∑ x,
              isingTorusSpinField sigma x * f x|)) =
        (∑ sigma,
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
              Real.exp (s * |∑ x,
                isingTorusSpinField sigma x * f x|)) /
          isingTorusShiftedPartition beta 0 := by
      rw [Finset.sum_div Finset.univ]
      apply Finset.sum_congr rfl
      intro sigma _
      ring
    _ <= _ := isingTorus_linear_expAbsMoment_le_unconditional
      beta hbeta f h hpotential s



theorem exists_isingTorusSmearedSpin_expMoment_bounds
    (beta : Real) (hbeta : 0 < beta)
    (f : IsingDyadicTorus d k -> Real) (hzero : ∑ x, f x = 0) :
    ∃ h : IsingDyadicTorus d k -> Real,
      (forall u : IsingDyadicTorus d k -> Real,
        isingTorusDirichletBilinear u h = ∑ x, u x * f x) ∧
      (forall s : Real,
        (∫ sigma, Real.exp (s * isingTorusSmearedSpin f sigma)
            ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
              ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
          Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) ∧
      (forall s : Real,
        (∫ sigma, Real.exp (s * |isingTorusSmearedSpin f sigma|)
            ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
              ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <=
          2 * Real.exp
            (s ^ 2 * isingTorusDirichlet h / (2 * beta))) := by
  obtain ⟨h, hpotential⟩ := exists_isingTorusDirichlet_potential f hzero
  exact ⟨h, hpotential,
    fun s => integral_exp_isingTorusSmearedSpin_le
      beta hbeta f h hpotential s,
    fun s => integral_exp_abs_isingTorusSmearedSpin_le
      beta hbeta f h hpotential s⟩

end

end StatMech.FrontierA
