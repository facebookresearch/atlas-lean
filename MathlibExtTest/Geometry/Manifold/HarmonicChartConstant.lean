/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.HarmonicChartConstant
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

open InnerProductSpace

/-! Instances of the constancy of harmonic functions on a compact connected charted space. -/

#check @ChartedSpace.exists_eq_const_of_harmonicAt

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X] [ConnectedSpace X]

/-- A constant function is harmonic in every chart, and the theorem returns its value. -/
example (c : ℝ) : ∃ d, ∀ x : X, (fun _ : X => c) x = d :=
  ChartedSpace.exists_eq_const_of_harmonicAt fun _ => harmonicAt_const c

/-- A function harmonic in the charts takes the same value at any two points. -/
example {f : X → ℝ} (hf : ∀ x, HarmonicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x))
    (x y : X) : f x = f y := by
  obtain ⟨c, hc⟩ := ChartedSpace.exists_eq_const_of_harmonicAt hf
  rw [hc x, hc y]

/-- A non-constant function is not harmonic in all charts. -/
example {f : X → ℝ} {x y : X} (hxy : f x ≠ f y) :
    ¬ ∀ z, HarmonicAt (f ∘ (chartAt ℂ z).symm) (chartAt ℂ z z) := fun hf => by
  obtain ⟨c, hc⟩ := ChartedSpace.exists_eq_const_of_harmonicAt hf
  exact hxy (by rw [hc x, hc y])
