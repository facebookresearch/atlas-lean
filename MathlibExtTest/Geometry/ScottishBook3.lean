/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.ScottishBook3
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Isometry

open MathlibExt.Geometry.ScottishBook3Wanted Set

universe u

-- An isometric self-map of a compact metric space is surjective in every universe.
example {X : Type u} [MetricSpace X] [CompactSpace X] {f : X → X} (hf : Isometry f) :
    Function.Surjective f := by
  simpa only [image_univ, range_eq_univ] using
    image_eq_of_isometry_mapsTo isCompact_univ hf (mapsTo_univ f univ)

-- A closed interval may sit in a noncompact ambient space, and its endpoints can be unordered.
example (a b : ℝ) (f : ℝ → ℝ) (hf : Isometry f) (hmaps : MapsTo f (Icc a b) (Icc a b)) :
    f '' Icc a b = Icc a b := by
  by_contra hne
  exact noCompactSetCongruentToProperSubset ℝ isCompact_Icc ⟨f, hf.dist_eq, hmaps.image_subset, hne⟩

-- Translation by one takes the closed ray into itself and misses zero.
example : ¬ IsCompact (Ici (0 : ℝ)) := by
  intro hK
  apply noCompactSetCongruentToProperSubset ℝ hK
  refine ⟨(· + 1), fun x y => by simp [Real.dist_eq], ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact add_nonneg hx zero_le_one
  · intro heq
    have hzero : 0 ∈ (· + 1) '' Ici (0 : ℝ) := by
      rw [heq]
      exact self_mem_Ici
    obtain ⟨x, hx, hx0⟩ := hzero
    exact (add_pos_of_nonneg_of_pos hx zero_lt_one).ne' hx0
