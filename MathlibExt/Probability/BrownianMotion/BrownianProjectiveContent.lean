/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.BrownianMotion.BrownianFiniteDimensional
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# The additive content of the Brownian finite-dimensional laws

The projective family `brownianFiniteDimensionalPiLaw` defines an additive content on the
measurable cylinders of `ℝ → ℝ` (Mathlib's `projectiveFamilyContent`). This file records its
basic properties; σ-subadditivity, and hence the extension to a measure, is proved in
`BrownianProjectiveExtension`.

## Main definitions

* `StatMech.SLE.brownianProjectiveContent`: the content of a cylinder `{ω | ω|_I ∈ S}` is
  `brownianFiniteDimensionalPiLaw I S`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace StatMech.SLE

/-- The additive content on measurable cylinders of `ℝ → ℝ` defined by the Brownian
finite-dimensional laws. -/
noncomputable def brownianProjectiveContent :
    AddContent ENNReal (measurableCylinders fun _ : Real => Real) :=
  projectiveFamilyContent brownianFiniteDimensionalPiLaw_isProjective

/-- The content of the cylinder over `S ⊆ I → ℝ` is the finite-dimensional law of `S`. -/
theorem brownianProjectiveContent_cylinder
    (I : Finset Real) (S : Set (I → Real)) (hS : MeasurableSet S) :
    brownianProjectiveContent (cylinder I S) =
      brownianFiniteDimensionalPiLaw I S := by
  exact projectiveFamilyContent_cylinder
    brownianFiniteDimensionalPiLaw_isProjective hS

@[simp]
theorem brownianProjectiveContent_empty :
    brownianProjectiveContent (∅ : Set (Real → Real)) = 0 := by
  exact addContent_empty (m := brownianProjectiveContent)

@[simp]
theorem brownianProjectiveContent_univ :
    brownianProjectiveContent (univ : Set (Real → Real)) = 1 := by
  calc
    brownianProjectiveContent (univ : Set (Real → Real)) =
        brownianProjectiveContent
          (cylinder (∅ : Finset Real) (univ : Set ((∅ : Finset Real) → Real))) := by
      rw [cylinder_univ]
    _ = brownianFiniteDimensionalPiLaw (∅ : Finset Real) univ :=
      brownianProjectiveContent_cylinder _ _ MeasurableSet.univ
    _ = 1 := measure_univ

theorem brownianProjectiveContent_ne_top
    (A : Set (Real → Real)) :
    brownianProjectiveContent A ≠ ∞ := by
  exact projectiveFamilyContent_ne_top
    brownianFiniteDimensionalPiLaw_isProjective

theorem brownianProjectiveContent_mono
    {A B : Set (Real → Real)}
    (hA : A ∈ measurableCylinders fun _ : Real => Real)
    (hB : B ∈ measurableCylinders fun _ : Real => Real)
    (hAB : A ≤ B) :
    brownianProjectiveContent A ≤ brownianProjectiveContent B := by
  exact projectiveFamilyContent_mono
    brownianFiniteDimensionalPiLaw_isProjective hA hB hAB

/-- Countable subadditivity for cylinders over a common finite index set. -/
theorem brownianProjectiveContent_iUnion_cylinder_le
    (I : Finset Real) (S : Nat → Set (I → Real))
    (hS : ∀ n, MeasurableSet (S n)) :
    brownianProjectiveContent (cylinder I (iUnion S)) ≤
      tsum (fun n => brownianProjectiveContent (cylinder I (S n))) := by
  rw [brownianProjectiveContent_cylinder I (iUnion S)
      (MeasurableSet.iUnion hS)]
  simp_rw [brownianProjectiveContent_cylinder I _ (hS _)]
  exact measure_iUnion_le _

/-- Continuity at `∅` for decreasing cylinders over a common finite index set. -/
theorem brownianProjectiveContent_cylinder_tendsto_zero
    (I : Finset Real) (S : Nat → Set (I → Real))
    (hS : ∀ n, MeasurableSet (S n))
    (hanti : Antitone S)
    (hinter : iInter S = (∅ : Set (I → Real))) :
    Tendsto (fun n => brownianProjectiveContent (cylinder I (S n)))
      atTop (nhds 0) := by
  simp_rw [brownianProjectiveContent_cylinder I _ (hS _)]
  have hlimit := tendsto_measure_iInter_atTop
    (μ := brownianFiniteDimensionalPiLaw I)
    (fun n => (hS n).nullMeasurableSet) hanti
    (Exists.intro 0 (measure_ne_top _ _))
  rw [hinter, measure_empty] at hlimit
  exact hlimit

/-- Continuity at `∅` for decreasing cylinders whose index sets are contained in a common finite
set. -/
theorem brownianProjectiveContent_cylinder_tendsto_zero_of_bounded_coordinates
    (I : Nat → Finset Real) (S : ∀ n, Set (I n → Real))
    (hS : ∀ n, MeasurableSet (S n))
    (J : Finset Real) (hIJ : ∀ n, I n ≤ J)
    (hanti : Antitone
      (fun n => Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n))
    (hinter : iInter (fun n =>
      Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n) =
      (∅ : Set (J → Real))) :
    Tendsto (fun n => brownianProjectiveContent (cylinder (I n) (S n)))
      atTop (nhds 0) := by
  have hcylinder (n : Nat) :
      cylinder (I n) (S n) =
        (cylinder J
          (Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n) :
            Set (Real → Real)) := by
    ext x
    simp only [mem_cylinder, Set.mem_preimage]
    rfl
  have hmeasurable (n : Nat) :
      MeasurableSet
        (Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n) :=
    (Finset.measurable_restrict₂ (X := fun _ : Real => Real) (hIJ n)) (hS n)
  simpa only [hcylinder] using
    brownianProjectiveContent_cylinder_tendsto_zero
      J (fun n =>
        Finset.restrict₂ (π := fun _ : Real => Real) (hIJ n) ⁻¹' S n)
      hmeasurable hanti hinter

end StatMech.SLE
