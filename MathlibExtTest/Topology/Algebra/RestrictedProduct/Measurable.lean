/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Algebra.RestrictedProduct.Measurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

open scoped RestrictedProduct

/-- The Borel σ-algebra on the concrete restricted product used below. -/
instance : MeasurableSpace (Πʳ _ : ℕ, [ℝ, Set.Icc 0 1]) := borel _

/-- The Borel σ-algebra on the concrete restricted product used below. -/
instance : BorelSpace (Πʳ _ : ℕ, [ℝ, Set.Icc 0 1]) := ⟨rfl⟩

/-- `exactSource` consumer with the original binders. -/
private theorem exactSource {ι : Type*} [Countable ι] {R : ι → Type*}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    {A : (i : ι) → Set (R i)} (hA : ∀ i, MeasurableSet (A i))
    [MeasurableSpace (Πʳ i, [R i, A i])] [BorelSpace (Πʳ i, [R i, A i])]
    {X : Type*} [MeasurableSpace X] (f : X → Πʳ i, [R i, A i]) :
    Measurable f ↔ ∀ i, Measurable fun x => f x i :=
  RestrictedProduct.measurable_iff_forall_measurable_apply hA f

/-- Nontrivial instance: the identity on a restricted product of copies of
`ℝ` restricted to the unit interval is measurable, checked coordinatewise.
The Borel σ-algebra on the restricted product is supplied explicitly. -/
example : Measurable (id : (Πʳ _ : ℕ, [ℝ, Set.Icc 0 1]) →
    Πʳ _ : ℕ, [ℝ, Set.Icc 0 1]) := by
  rw [RestrictedProduct.measurable_iff_forall_measurable_apply
    (fun _ => measurableSet_Icc)]
  intro i
  exact (RestrictedProduct.continuous_eval i).measurable

/-- Coordinatewise characterization for the same concrete product: a map
from `ℝ` is measurable exactly when all its coordinates are. -/
example (f : ℝ → Πʳ _ : ℕ, [ℝ, Set.Icc 0 1]) :
    Measurable f ↔ ∀ i, Measurable fun x => f x i :=
  RestrictedProduct.measurable_iff_forall_measurable_apply
    (fun _ => measurableSet_Icc) f
