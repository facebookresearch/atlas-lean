/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ThreeChain

open Set

namespace MetaMathlibExt.ThreeChainTest

-- Two chains can attain all fourteen regions, including those created by self-crossings.
example : ∃ (p q u v : Fin 2 → ℝ × ℝ), (∀ i, u i ≠ 0 ∧ v i ≠ 0) ∧
    14 = planeRegionCount (⋃ i, ((fun s : ℝ => p i + s • u i) '' Ici 0 ∪
      segment ℝ (p i) (q i) ∪ (fun s : ℝ => q i + s • v i) '' Ici 0)) :=
  (isGreatest_planeRegionCount_threeChain 2).1

-- The upper bound also applies when the endpoints coincide and the middle segment collapses.
example (p u v : ℝ × ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    planeRegionCount ((fun s : ℝ => p + s • u) '' Ici 0 ∪
      (fun s : ℝ => p + s • v) '' Ici 0) ≤ 3 := by
  apply (isGreatest_planeRegionCount_threeChain 1).2
  refine ⟨fun _ => p, fun _ => p, fun _ => u, fun _ => v, fun _ => ⟨hu, hv⟩, ?_⟩
  have hp : p ∈ (fun s : ℝ => p + s • u) '' Ici 0 := ⟨0, le_rfl, by simp⟩
  congr 1
  ext z
  constructor
  · intro hz
    exact mem_iUnion_of_mem (0 : Fin 1) (by
      simpa [union_eq_left.2 (singleton_subset_iff.2 hp)] using hz)
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    simpa [union_eq_left.2 (singleton_subset_iff.2 hp)] using hi

end MetaMathlibExt.ThreeChainTest
