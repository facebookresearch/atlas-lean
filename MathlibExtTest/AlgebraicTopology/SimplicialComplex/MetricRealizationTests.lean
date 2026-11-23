/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricRealization

noncomputable section

open Topology

universe u z

#check PreAbstractSimplicialComplex.MetricRealization
#print axioms PreAbstractSimplicialComplex.MetricRealization
#check PreAbstractSimplicialComplex.instMetricSpaceMetricRealization
#print axioms PreAbstractSimplicialComplex.instMetricSpaceMetricRealization
#check PreAbstractSimplicialComplex.Realization.toMetric
#print axioms PreAbstractSimplicialComplex.Realization.toMetric
#check PreAbstractSimplicialComplex.Realization.toMetric_weights
#print axioms PreAbstractSimplicialComplex.Realization.toMetric_weights
#check PreAbstractSimplicialComplex.MetricRealization.toWeak
#print axioms PreAbstractSimplicialComplex.MetricRealization.toWeak
#check PreAbstractSimplicialComplex.MetricRealization.toWeak_support
#print axioms PreAbstractSimplicialComplex.MetricRealization.toWeak_support
#check PreAbstractSimplicialComplex.MetricRealization.toWeak_vertex
#print axioms PreAbstractSimplicialComplex.MetricRealization.toWeak_vertex
#check PreAbstractSimplicialComplex.weakMetricHomotopyEquiv
#print axioms PreAbstractSimplicialComplex.weakMetricHomotopyEquiv
#check PreAbstractSimplicialComplex.weakMetricHomotopyEquiv_toFun
#print axioms PreAbstractSimplicialComplex.weakMetricHomotopyEquiv_toFun
#check PreAbstractSimplicialComplex.weakMetricHomotopyEquiv_invFun
#print axioms PreAbstractSimplicialComplex.weakMetricHomotopyEquiv_invFun
#check PreAbstractSimplicialComplex.weakMetricLeftHomotopy
#print axioms PreAbstractSimplicialComplex.weakMetricLeftHomotopy
#check PreAbstractSimplicialComplex.weakMetricRightHomotopy
#print axioms PreAbstractSimplicialComplex.weakMetricRightHomotopy
#check PreAbstractSimplicialComplex.MetricRealization.continuous_iff_coordinates
#print axioms PreAbstractSimplicialComplex.MetricRealization.continuous_iff_coordinates

namespace PreAbstractSimplicialComplex

variable {V : Type u} (P : PreAbstractSimplicialComplex V)

-- No Fact, metric, finiteness or cardinality premise is supplied.
example : MetricSpace (MetricRealization P) := inferInstance

example (x : P.Realization) :
    ((weakMetricHomotopyEquiv P).toFun x).val.ofLp = x.point.weights := by
  rw [weakMetricHomotopyEquiv_toFun]
  exact Realization.toMetric_weights P x

example :
    (weakMetricHomotopyEquiv P).toFun = Realization.toMetric P ∧
      (weakMetricHomotopyEquiv P).invFun = MetricRealization.toWeak P :=
  ⟨weakMetricHomotopyEquiv_toFun P, weakMetricHomotopyEquiv_invFun P⟩

example (x : MetricRealization P) :
    (MetricRealization.toWeak P x).point.weights.support ⊆ x.val.ofLp.support :=
  MetricRealization.toWeak_support P x

example (v : V) (hv : {v} ∈ P) :
    MetricRealization.toWeak P (Realization.toMetric P (Realization.vertex P v hv)) =
      Realization.vertex P v hv :=
  MetricRealization.toWeak_vertex P v hv

example (v : V) (hv : {v} ∈ P) (t : unitInterval) :
    weakMetricLeftHomotopy P v hv (t, Realization.vertex P v hv) =
      Realization.vertex P v hv :=
  (weakMetricLeftHomotopy P v hv).eq_snd t (Set.mem_singleton_iff.mpr rfl)

example (v : V) (hv : {v} ∈ P) (t : unitInterval) :
    weakMetricRightHomotopy P v hv
        (t, Realization.toMetric P (Realization.vertex P v hv)) =
      Realization.toMetric P (Realization.vertex P v hv) :=
  (weakMetricRightHomotopy P v hv).eq_snd t (Set.mem_singleton_iff.mpr rfl)

example (v : V) (hv : {v} ∈ P) :
    (weakMetricLeftHomotopy P v hv).toHomotopy.curry 0 =
        (MetricRealization.toWeak P).comp (Realization.toMetric P) ∧
      (weakMetricLeftHomotopy P v hv).toHomotopy.curry 1 =
        ContinuousMap.id P.Realization :=
  ⟨(weakMetricLeftHomotopy P v hv).toHomotopy.curry_zero,
    (weakMetricLeftHomotopy P v hv).toHomotopy.curry_one⟩

example (v : V) (hv : {v} ∈ P) :
    (weakMetricRightHomotopy P v hv).toHomotopy.curry 0 =
        (Realization.toMetric P).comp (MetricRealization.toWeak P) ∧
      (weakMetricRightHomotopy P v hv).toHomotopy.curry 1 =
        ContinuousMap.id (MetricRealization P) :=
  ⟨(weakMetricRightHomotopy P v hv).toHomotopy.curry_zero,
    (weakMetricRightHomotopy P v hv).toHomotopy.curry_one⟩

-- This is the arbitrary-index criterion used to build later strong-model
-- interpolation families; normalized supported values are enforced by the type.
example {X : Type z} [TopologicalSpace X] (f : X → MetricRealization P)
    (hf : ∀ v, Continuous (fun x => (f x).val.ofLp v)) : Continuous f :=
  (MetricRealization.continuous_iff_coordinates P f).mpr hf

end PreAbstractSimplicialComplex

end
