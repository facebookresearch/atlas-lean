/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.UnitAddTorusLift

@[expose] public section

open MeasureTheory Function UnitAddTorus

-- `exactSource` consumer with the original binders: a surjective additive
-- map to a unit torus and a complex-valued kernel-periodic function.
example {A : Type*} [AddCommGroup A] {ι : Type*} (Θ : A →+ UnitAddTorus ι)
    (hΘ : Surjective Θ) {H : A → ℂ} (hH : IsKerPeriodic Θ H) (x : A) :
    torusLift Θ hΘ H (Θ x) = H x :=
  torusLift_apply Θ hΘ hH x

example {A : Type*} [AddCommGroup A] {ι : Type*} (Θ : A →+ UnitAddTorus ι)
    (hΘ : Surjective Θ) {H : A → ℂ} (hH : IsKerPeriodic Θ H) :
    torusLift Θ hΘ H ∘ Θ = H :=
  torusLift_comp Θ hΘ hH

example {A : Type*} [AddCommGroup A] [TopologicalSpace A] {ι : Type*}
    (Θ : A →+ UnitAddTorus ι) (hΘ : IsOpenQuotientMap Θ) {H : A → ℂ}
    (hH : IsKerPeriodic Θ H) (hc : Continuous H) :
    Continuous (torusLift Θ hΘ.surjective H) :=
  continuous_torusLift Θ hΘ hH hc

-- Higher-universe consumer: the codomain may live in a higher universe.
example {A : Type*} [AddCommGroup A] {ι : Type*} (Θ : A →+ UnitAddTorus ι)
    (hΘ : Surjective Θ) {H : A → ULift ℂ} (hH : IsKerPeriodic Θ H) (x : A) :
    torusLift Θ hΘ H (Θ x) = H x :=
  torusLift_apply Θ hΘ hH x

-- The product Haar measure is a probability Haar measure.
example (ι : Type*) [Fintype ι] : IsProbabilityMeasure (torusMeasure ι) :=
  inferInstance

example (ι : Type*) [Fintype ι] : (torusMeasure ι).IsAddHaarMeasure :=
  inferInstance

example {ι : Type*} [Fintype ι] (P : Measure (UnitAddTorus ι))
    [IsProbabilityMeasure P] [P.IsAddLeftInvariant] : P = torusMeasure ι :=
  eq_torusMeasure P

example {A : Type*} [AddCommGroup A] [TopologicalSpace A] [MeasurableSpace A]
    {ι : Type*} [Fintype ι] {Θ : A →+ UnitAddTorus ι} {P : Measure A}
    [IsProbabilityMeasure P] (hΘm : AEMeasurable Θ P)
    (hinv : (Measure.map Θ P).IsAddLeftInvariant) :
    Measure.map Θ P = torusMeasure ι :=
  map_eq_torusMeasure hΘm hinv

-- Boundary example: kernel-periodicity is not automatic. For the zero map
-- from `ℝ` to the torus indexed by the empty type, every vector lies in
-- the kernel, but the identity function is not invariant under the shift
-- by `1`, so it does not descend to a function recovering its values.
example : ¬ IsKerPeriodic (0 : ℝ →+ UnitAddTorus (Fin 0)) (fun x : ℝ => (x : ℂ)) := by
  intro h
  have h1 := h 1 (by simp) 0
  simp only [zero_add] at h1
  norm_num at h1
