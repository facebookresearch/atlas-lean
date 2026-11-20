/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianTorusLaw
import Code.FrontierA.IsingGaussianNewmanBridge











open Filter MeasureTheory Topology

namespace StatMech.FrontierA

open ProbabilityTheory

noncomputable section



def isingTorusFieldLaw {E : Type*} [MeasurableSpace E]
  (d k : Nat) (beta : Real)
    (X : ConfigSpace (IsingDyadicTorus d k) -> E) : ProbabilityMeasure E :=
  (isingTorusZeroFieldLaw (d := d) (k := k) beta).map
    (Measurable.of_discrete : Measurable X).aemeasurable



theorem integral_exp_abs_projection_isingTorusFieldLaw_le
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E]
    (d k : Nat) (beta : Real) (hbeta : 0 < beta)
    (X : ConfigSpace (IsingDyadicTorus d k) -> E)
    (t : E) (f h : IsingDyadicTorus d k -> Real)
    (hprojection : forall sigma,
      InnerProductSpace.toDualMap Real E t (X sigma) =
        isingTorusSmearedSpin f sigma)
    (hpotential : forall u : IsingDyadicTorus d k -> Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∫ x, Real.exp (s * |x|)
        ∂(((isingTorusFieldLaw d k beta X).map
          (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable) :
            Measure Real)) <=
      2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  change (∫ x, Real.exp (s * |x|)
      ∂Measure.map (InnerProductSpace.toDualMap Real E t)
        (Measure.map X
          (isingTorusZeroFieldLaw (d := d) (k := k) beta : Measure _))) <= _
  rw [MeasureTheory.integral_map
    (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable
    (by fun_prop)]
  rw [MeasureTheory.integral_map
    (Measurable.of_discrete : Measurable X).aemeasurable (by fun_prop)]
  simp_rw [hprojection]
  exact integral_exp_abs_isingTorusSmearedSpin_le
    beta hbeta f h hpotential s



theorem integrable_exp_abs_projection_isingTorusFieldLaw
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E]
    (d k : Nat) (beta s : Real)
    (X : ConfigSpace (IsingDyadicTorus d k) -> E) (t : E) :
    Integrable (fun x : Real => Real.exp (s * |x|))
      (((isingTorusFieldLaw d k beta X).map
        (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable) :
          Measure Real) := by
  change Integrable (fun x : Real => Real.exp (s * |x|))
    (Measure.map (InnerProductSpace.toDualMap Real E t)
      (Measure.map X
        (isingTorusZeroFieldLaw (d := d) (k := k) beta : Measure _)))
  rw [MeasureTheory.integrable_map_measure (by fun_prop)
    (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable]
  rw [MeasureTheory.integrable_map_measure (by fun_prop)
    (Measurable.of_discrete : Measurable X).aemeasurable]
  exact Integrable.of_finite






theorem weakLimit_eq_of_torus_projection_newmanFourth
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (X : (n : Nat) -> ConfigSpace (IsingDyadicTorus d n) -> E)
    (mu nu : ProbabilityMeasure E)
    (hlim : Tendsto (fun n => isingTorusFieldLaw d n beta (X n))
      atTop (nhds mu))
    (variance : E -> Real) (cumulants : Nat -> E -> Nat -> Real)
    (hrecurrence : forall t : E,
      HasScalarMomentCumulantRecurrence
        (fun scale order =>
          ∫ x, x ^ order
            ∂(((isingTorusFieldLaw d scale beta (X scale)).map
              (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable :
                ProbabilityMeasure Real) : Measure Real))
        (fun scale order => cumulants scale t order))
    (hcontrol : forall t : E,
      NewmanFourthCumulantControl (fun scale order =>
        cumulants scale t order))
    (hvariance : forall t : E,
      Tendsto (fun scale => cumulants scale t 2) atTop
        (nhds (variance t)))
    (hfourth : forall t : E,
      Tendsto (fun scale => cumulants scale t 4) atTop (nhds 0))
    (f h : (n : Nat) -> E -> IsingDyadicTorus d n -> Real)
    (hprojection : forall n t sigma,
      InnerProductSpace.toDualMap Real E t (X n sigma) =
        isingTorusSmearedSpin (f n t) sigma)
    (hpotential : forall n t u,
      isingTorusDirichletBilinear u (h n t) =
        ∑ x, u x * f n t x)
    (energyBound : E -> Real)
    (henergy : forall n t, isingTorusDirichlet (h n t) <= energyBound t)
    (hnuExp : forall t : E, (0 : Real) ∈ interior
      (integrableExpSet id
        ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
    (hnuWick : forall t : E, ScalarWickMoments (variance t)
      (fun order => ∫ x, x ^ order
        ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
    (mu : Measure E) = (nu : Measure E) := by
  apply weakLimit_eq_of_projection_newmanFourth_uniform_exp
    (fun n => isingTorusFieldLaw d n beta (X n)) mu nu hlim
    variance cumulants hrecurrence hcontrol hvariance hfourth
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
