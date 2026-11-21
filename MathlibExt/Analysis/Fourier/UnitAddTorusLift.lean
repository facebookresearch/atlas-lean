/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean`
and
`P2M/Sol/S_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Maps.OpenQuotient

import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

noncomputable section

open MeasureTheory Function

namespace UnitAddTorus

/-- A function `H` on an additive group `A` is periodic along the kernel of
an additive map `Θ` to a unit torus when shifting by any element of the
kernel leaves every value unchanged. -/
def IsKerPeriodic {A : Type*} [AddCommGroup A] {ι : Type*}
    (Θ : A →+ UnitAddTorus ι) {E : Type*} (H : A → E) : Prop :=
  ∀ v : A, Θ v = 0 → ∀ x : A, H (x + v) = H x

/-- The descent of a kernel-periodic function along a surjective additive
map to a unit torus. The value at a point of the torus is the value of the
original function at any chosen preimage. -/
def torusLift {A : Type*} [AddCommGroup A] {ι : Type*} (Θ : A →+ UnitAddTorus ι)
    (hΘ : Surjective Θ) {E : Type*} (H : A → E) : UnitAddTorus ι → E :=
  fun θ => H (surjInv hΘ θ)

private theorem eq_iff_sub_mem_ker {A : Type*} [AddCommGroup A] {ι : Type*}
    {Θ : A →+ UnitAddTorus ι} (x y : A) : Θ x = Θ y ↔ Θ (x - y) = 0 := by
  rw [map_sub, sub_eq_zero]

/-- The descended function recovers the original function at every point
in the image of the defining map. -/
theorem torusLift_apply {A : Type*} [AddCommGroup A] {ι : Type*}
    (Θ : A →+ UnitAddTorus ι) (hΘ : Surjective Θ) {E : Type*} {H : A → E}
    (hH : IsKerPeriodic Θ H) (x : A) : torusLift Θ hΘ H (Θ x) = H x := by
  unfold torusLift
  have hy : Θ (surjInv hΘ (Θ x)) = Θ x := surjInv_eq _ _
  rw [eq_iff_sub_mem_ker] at hy
  have hper := hH _ hy x
  rwa [add_sub_cancel] at hper

/-- The descended function composed with the defining map is the original
function. -/
theorem torusLift_comp {A : Type*} [AddCommGroup A] {ι : Type*}
    (Θ : A →+ UnitAddTorus ι) (hΘ : Surjective Θ) {E : Type*} {H : A → E}
    (hH : IsKerPeriodic Θ H) : torusLift Θ hΘ H ∘ Θ = H :=
  funext (torusLift_apply Θ hΘ hH)

/-- Descent along an open quotient map preserves continuity: continuity of
the descended function can be checked after composing with the quotient
map, where the composition is the original continuous function. -/
theorem continuous_torusLift {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    {ι : Type*} (Θ : A →+ UnitAddTorus ι) (hΘ : IsOpenQuotientMap Θ)
    {E : Type*} [TopologicalSpace E] {H : A → E} (hH : IsKerPeriodic Θ H)
    (hc : Continuous H) : Continuous (torusLift Θ hΘ.surjective H) := by
  rw [← hΘ.continuous_comp_iff, torusLift_comp Θ hΘ.surjective hH]
  exact hc

/-- The descended function packaged as a continuous map. -/
def torusLiftCM {A : Type*} [AddCommGroup A] [TopologicalSpace A] {ι : Type*}
    (Θ : A →+ UnitAddTorus ι) (hΘ : IsOpenQuotientMap Θ) {E : Type*}
    [TopologicalSpace E] {H : A → E} (hH : IsKerPeriodic Θ H)
    (hc : Continuous H) : C(UnitAddTorus ι, E) :=
  ⟨torusLift Θ hΘ.surjective H, continuous_torusLift Θ hΘ hH hc⟩

/-- The underlying function of the packaged descended continuous map is
the descended function. -/
theorem torusLiftCM_apply {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    {ι : Type*} (Θ : A →+ UnitAddTorus ι) (hΘ : IsOpenQuotientMap Θ)
    {E : Type*} [TopologicalSpace E] {H : A → E} (hH : IsKerPeriodic Θ H)
    (hc : Continuous H) (θ : UnitAddTorus ι) :
    torusLiftCM Θ hΘ hH hc θ = torusLift Θ hΘ.surjective H θ :=
  rfl

/-- The product Haar measure on a unit torus: the product, over the index
type, of the normalized Haar measure on the unit additive circle. -/
def torusMeasure (ι : Type*) [Fintype ι] : Measure (UnitAddTorus ι) :=
  Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (torusMeasure ι) :=
  inferInstanceAs
    (IsProbabilityMeasure (Measure.pi fun _ : ι => AddCircle.haarAddCircle))

instance (ι : Type*) [Fintype ι] : (torusMeasure ι).IsAddHaarMeasure :=
  inferInstanceAs
    ((Measure.pi fun _ : ι => AddCircle.haarAddCircle).IsAddHaarMeasure)

/-- A probability measure on a unit torus that is invariant under left
addition is the product Haar measure. -/
theorem eq_torusMeasure {ι : Type*} [Fintype ι] (P : Measure (UnitAddTorus ι))
    [IsProbabilityMeasure P] [P.IsAddLeftInvariant] : P = torusMeasure ι := by
  haveI : P.IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_of_isCompact_nonempty_interior P Set.univ
      isCompact_univ (by rw [interior_univ]; exact Set.univ_nonempty)
      (by rw [measure_univ]; exact one_ne_zero)
      (by rw [measure_univ]; exact ENNReal.one_ne_top)
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure P (torusMeasure ι)

/-- The pushforward of a probability measure along a map to a unit torus
is the product Haar measure whenever the pushforward is invariant under
left addition. -/
theorem map_eq_torusMeasure {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [MeasurableSpace A] {ι : Type*} [Fintype ι] {Θ : A →+ UnitAddTorus ι}
    {P : Measure A} [IsProbabilityMeasure P] (hΘm : AEMeasurable Θ P)
    (hinv : (Measure.map Θ P).IsAddLeftInvariant) :
    Measure.map Θ P = torusMeasure ι := by
  haveI : IsProbabilityMeasure (Measure.map Θ P) :=
    (Measure.isProbabilityMeasure_map_iff hΘm).mpr inferInstance
  haveI : (Measure.map Θ P).IsAddLeftInvariant := hinv
  exact eq_torusMeasure _

end UnitAddTorus

end
