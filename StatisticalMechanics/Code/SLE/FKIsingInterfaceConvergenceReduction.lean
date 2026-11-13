/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Code.SLE.ChainCapacity
import Code.SLE.CardyCLE
import Code.Universality.IsingSHolo

open Filter MeasureTheory Set Topology

namespace StatMech.SLE




def IsWeaklySequentiallyPrecompact
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (laws : Nat -> ProbabilityMeasure X) : Prop :=
  forall phi : Nat -> Nat, StrictMono phi ->
    exists psi : Nat -> Nat, StrictMono psi /\
      exists limit : ProbabilityMeasure X,
        Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit)



theorem weaklySequentiallyPrecompact_of_tight
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [PolishSpace X] [BorelSpace X]
    (laws : Nat -> ProbabilityMeasure X)
    (hTight : IsTightMeasureSet
      {mu : Measure X | exists n, mu = (laws n : Measure X)}) :
    IsWeaklySequentiallyPrecompact laws := by
  have hcompact : IsCompact (closure (Set.range laws)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert hTight using 1
    ext mu
    constructor
    · rintro ⟨nu, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨laws n, ⟨n, rfl⟩, rfl⟩
  intro phi _hphi
  have hmem : forall n, laws (phi n) ∈ closure (Set.range laws) := by
    intro n
    apply subset_closure
    exact Set.mem_range_self (phi n)
  obtain ⟨limit, _hlimit, psi, hpsi, htendsto⟩ :=
    hcompact.tendsto_subseq hmem
  exact ⟨psi, hpsi, limit, htendsto⟩




theorem tendsto_of_weaklySequentiallyPrecompact_of_subsequential_limits_eq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (laws : Nat -> ProbabilityMeasure X) (target : ProbabilityMeasure X)
    (hcompact : IsWeaklySequentiallyPrecompact laws)
    (hunique : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure X),
      StrictMono phi -> StrictMono psi ->
      Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) ->
      limit = target) :
    Tendsto laws atTop (nhds target) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨phi, hphi, hnsphi⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨psi, hpsi, limit, hlimit⟩ := hcompact (ns ∘ phi) hnsphi
  have heq := hunique (ns ∘ phi) psi limit hnsphi hpsi hlimit
  subst limit
  refine ⟨phi ∘ psi, ?_⟩
  simpa only [Function.comp_apply] using hlimit




theorem tendsto_of_tight_of_subsequential_limits_eq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [PolishSpace X] [BorelSpace X]
    (laws : Nat -> ProbabilityMeasure X) (target : ProbabilityMeasure X)
    (hTight : IsTightMeasureSet
      {mu : Measure X | exists n, mu = (laws n : Measure X)})
    (hunique : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure X),
      StrictMono phi -> StrictMono psi ->
      Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) ->
      limit = target) :
    Tendsto laws atTop (nhds target) :=
  tendsto_of_weaklySequentiallyPrecompact_of_subsequential_limits_eq
    laws target (weaklySequentiallyPrecompact_of_tight laws hTight) hunique




theorem tendsto_of_tight_of_unique_subsequential_criterion
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [PolishSpace X] [BorelSpace X]
    (laws : Nat -> ProbabilityMeasure X) (target : ProbabilityMeasure X)
    (criterion : ProbabilityMeasure X -> Prop)
    (hTight : IsTightMeasureSet
      {mu : Measure X | exists n, mu = (laws n : Measure X)})
    (hlimits : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure X),
      StrictMono phi -> StrictMono psi ->
      Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) ->
      criterion limit)
    (hunique : forall limit, criterion limit -> limit = target) :
    Tendsto laws atTop (nhds target) := by
  apply tendsto_of_tight_of_subsequential_limits_eq laws target hTight
  intro phi psi limit hphi hpsi hlimit
  exact hunique limit (hlimits phi psi limit hphi hpsi hlimit)

end StatMech.SLE
