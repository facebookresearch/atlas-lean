/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.UnitAddTorusVolume

@[expose] public section

open MeasureTheory UnitAddTorus

-- The volume on a unit torus is a probability measure; instance search also finds that it is
-- an additive Haar measure.
example (ι : Type*) [Fintype ι] : IsProbabilityMeasure (volume : Measure (UnitAddTorus ι)) :=
  inferInstance

example : (volume : Measure (UnitAddTorus (Fin 3))) Set.univ = 1 :=
  measure_univ

example (ι : Type*) [Fintype ι] : (volume : Measure (UnitAddTorus ι)).IsAddHaarMeasure :=
  inferInstance

example {ι : Type*} [Fintype ι] (P : Measure (UnitAddTorus ι))
    [IsProbabilityMeasure P] [P.IsAddLeftInvariant] : P = volume :=
  eq_volume_of_isAddLeftInvariant P

-- The pushforward characterization needs no topology on the source group.
example {A : Type*} [AddCommGroup A] [MeasurableSpace A]
    {ι : Type*} [Fintype ι] {Θ : A →+ UnitAddTorus ι} {P : Measure A}
    [IsProbabilityMeasure P] (hΘm : AEMeasurable Θ P)
    (hinv : (Measure.map Θ P).IsAddLeftInvariant) :
    Measure.map Θ P = volume :=
  map_eq_volume_of_isAddLeftInvariant hΘm hinv

-- Boundary example: factoring through a map to a unit torus is not automatic. For the zero map
-- from `ℝ` to the torus indexed by the empty type, every vector lies in the kernel, but the
-- identity function is not invariant under the shift by `1`, so it does not factor through the
-- map and does not descend to the torus.
example : ¬ Function.FactorsThrough (fun x : ℝ => (x : ℂ)) (0 : ℝ →+ UnitAddTorus (Fin 0)) := by
  intro h
  have h1 := @h 1 0 (by simp)
  norm_num at h1
