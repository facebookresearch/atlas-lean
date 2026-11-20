/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianTorusCumulants
import Code.FrontierA.IsingGaussianSignedCumulants












open Filter MeasureTheory Topology
open scoped BigOperators

namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising

noncomputable section





theorem weakLimit_eq_of_positive_torusScaledSmeared_newmanFourth
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (c : Nat → Real)
    (a : (k : Nat) → IsingDyadicTorus d k → Real)
    (ha : ∀ k x, 0 < a k x)
    (potential : (k : Nat) → IsingDyadicTorus d k → Real)
    (hpotential : ∀ k (u : IsingDyadicTorus d k → Real),
      isingTorusDirichletBilinear u (potential k) = ∑ x, u x * a k x)
    (mu nu : ProbabilityMeasure Real)
    (hlim : Tendsto
      (fun k => isingTorusFieldLaw d k beta
        (isingTorusScaledSmearedField (c k) (a k))) atTop (nhds mu))
    (variance : Real → Real)
    (hvariance : ∀ t,
      Tendsto
        (fun k => isingTorusScaledSmearedCumulant
          beta (c k) t (a k) 2)
        atTop (nhds (variance t)))
    (hfourth : ∀ t,
      Tendsto
        (fun k => isingTorusScaledSmearedCumulant
          beta (c k) t (a k) 4)
        atTop (nhds 0))
    (energyBound : Real → Real)
    (henergy : ∀ k t,
      isingTorusDirichlet ((t * c k) • potential k) ≤ energyBound t)
    (hnuExp : ∀ t : Real, (0 : Real) ∈ interior
      (integrableExpSet id
        ((nu : Measure Real).map
          (InnerProductSpace.toDualMap Real Real t))))
    (hnuWick : ∀ t : Real, ScalarWickMoments (variance t)
      (fun order => ∫ x, x ^ order
        ∂((nu : Measure Real).map
          (InnerProductSpace.toDualMap Real Real t)))) :
    (mu : Measure Real) = (nu : Measure Real) := by
  refine weakLimit_eq_of_torus_projection_newmanFourth
    d beta hbeta
    (fun k => isingTorusScaledSmearedField (c k) (a k))
    mu nu hlim variance
    (fun k t order =>
      isingTorusScaledSmearedCumulant beta (c k) t (a k) order)
    ?_ ?_ hvariance hfourth
    (fun k t => (t * c k) • a k)
    (fun k t => (t * c k) • potential k)
    ?_ ?_ energyBound henergy hnuExp hnuWick
  · exact fun t =>
      isingTorusScaledSmeared_hasScalarMomentCumulantRecurrence
        d beta c a t
  · exact fun t =>
      isingTorusScaledSmeared_newmanFourthCumulantControl
        d beta hbeta.le c a ha t
  · intro k t sigma
    simp only [InnerProductSpace.toDualMap_apply_apply, RCLike.inner_apply,
      conj_trivial, isingTorusScaledSmearedField, isingTorusSmearedSpin,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · intro k t u
    rw [isingTorusDirichletBilinear_symm,
      isingTorusDirichletBilinear_smul_left,
      isingTorusDirichletBilinear_symm, hpotential]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring



theorem tendsto_cumulant_of_tendsto_sub_zero
    (torus box : Nat → Real) (limit : Real)
    (hbox : Tendsto box atTop (nhds limit))
    (happrox : Tendsto (fun n => torus n - box n) atTop (nhds 0)) :
    Tendsto torus atTop (nhds limit) := by
  have hsum := happrox.add hbox
  convert hsum using 1
  · funext n
    ring
  · simp







theorem weakLimit_eq_of_torus_freeBoxCumulantApproximation
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (X : (n : Nat) → ConfigSpace (IsingDyadicTorus d n) → E)
    (mu nu : ProbabilityMeasure E)
    (hlim : Tendsto (fun n => isingTorusFieldLaw d n beta (X n))
      atTop (nhds mu))
    (variance : E → Real)
    (torusCumulants boxCumulants : Nat → E → Nat → Real)
    (hrecurrence : ∀ t : E,
      HasScalarMomentCumulantRecurrence
        (fun scale order =>
          ∫ x, x ^ order
            ∂(((isingTorusFieldLaw d scale beta (X scale)).map
              (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable :
                ProbabilityMeasure Real) : Measure Real))
        (fun scale order => torusCumulants scale t order))
    (hboxVariance : ∀ t : E,
      Tendsto (fun n => boxCumulants n t 2) atTop (nhds (variance t)))
    (hboxNonGaussian : ∀ (t : E) (order : Nat), order ≠ 2 →
      Tendsto (fun n => boxCumulants n t order) atTop (nhds 0))
    (happrox : ∀ (t : E) (order : Nat),
      Tendsto
        (fun n => torusCumulants n t order - boxCumulants n t order)
        atTop (nhds 0))
    (f h : (n : Nat) → E → IsingDyadicTorus d n → Real)
    (hprojection : ∀ n t sigma,
      InnerProductSpace.toDualMap Real E t (X n sigma) =
        isingTorusSmearedSpin (f n t) sigma)
    (hpotential : ∀ n t u,
      isingTorusDirichletBilinear u (h n t) = ∑ x, u x * f n t x)
    (energyBound : E → Real)
    (henergy : ∀ n t, isingTorusDirichlet (h n t) ≤ energyBound t)
    (hnuExp : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id
        ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
    (hnuWick : ∀ t : E, ScalarWickMoments (variance t)
      (fun order => ∫ x, x ^ order
        ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
    (mu : Measure E) = (nu : Measure E) := by
  have hcumulants : ∀ (t : E) (order : Nat),
      Tendsto (fun n => torusCumulants n t order) atTop
        (nhds (scalarGaussianCumulant (variance t) order)) := by
    intro t order
    by_cases horder : order = 2
    · subst order
      simpa [scalarGaussianCumulant] using
        tendsto_cumulant_of_tendsto_sub_zero
          (fun n => torusCumulants n t 2)
          (fun n => boxCumulants n t 2) (variance t)
          (hboxVariance t) (happrox t 2)
    · simpa [scalarGaussianCumulant, horder] using
        tendsto_cumulant_of_tendsto_sub_zero
          (fun n => torusCumulants n t order)
          (fun n => boxCumulants n t order) 0
          (hboxNonGaussian t order horder) (happrox t order)
  apply weakLimit_eq_of_projection_cumulant_limits_uniform_exp
    (fun n => isingTorusFieldLaw d n beta (X n)) mu nu hlim
    variance torusCumulants hrecurrence hcumulants
    (fun _ => 1) (fun t => 2 * Real.exp (energyBound t / (2 * beta)))
  · intro t
    norm_num
  · intro t n
    exact integrable_exp_abs_projection_isingTorusFieldLaw
      d n beta 1 (X n) t
  · intro t n
    exact (integral_exp_abs_projection_isingTorusFieldLaw_le
      d n beta hbeta (X n) t (f n t) (h n t)
      (hprojection n t) (hpotential n t) 1).trans (by
        gcongr
        simpa only [one_pow, one_mul] using henergy n t)
  · exact hnuExp
  · exact hnuWick

end

end StatMech.FrontierA
