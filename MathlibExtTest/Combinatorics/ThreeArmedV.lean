/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ThreeArmedV

open Set

namespace MetaMathlibExt.ThreeArmedVTest

example : planeRegionCount ∅ = 1 := planeRegionCount_empty

example : planeRegionCount univ = 0 := by simp [planeRegionCount]

-- Three coincident arms make a single ray. Its complement is connected around the tip.
example :
    planeRegionCount (⋃ _ : Fin 3, (fun s : ℝ => s • ((1, 0) : ℝ × ℝ)) '' Ici 0) = 1 := by
  let K : Set (ℝ × ℝ) := ⋃ _ : Fin 3, (fun s : ℝ => s • ((1, 0) : ℝ × ℝ)) '' Ici 0
  let L : Set (ℝ × ℝ) := Iio 0 ×ˢ univ
  let D : Set (ℝ × ℝ) := univ ×ˢ Iio 0
  let U : Set (ℝ × ℝ) := univ ×ˢ Ioi 0
  have hK (p : ℝ × ℝ) : p ∈ K ↔ 0 ≤ p.1 ∧ p.2 = 0 := by
    rcases p with ⟨x, y⟩
    simp [K, Prod.smul_mk, smul_eq_mul, eq_comm]
  have hcomp : Kᶜ = L ∪ (D ∪ U) := by
    ext p
    rw [mem_compl_iff, hK]
    simp only [L, D, U, mem_union, mem_prod, mem_Iio, mem_Ioi, mem_univ, and_true, true_and]
    rw [not_and_or, not_le]
    exact or_congr Iff.rfl ne_iff_lt_or_gt
  have hL : IsPreconnected L := isPreconnected_Iio.prod isPreconnected_univ
  have hD : IsPreconnected D := isPreconnected_univ.prod isPreconnected_Iio
  have hU : IsPreconnected U := isPreconnected_univ.prod isPreconnected_Ioi
  have hLD : (L ∩ D).Nonempty := ⟨(-1, -1), ⟨by norm_num, trivial⟩, ⟨trivial, by norm_num⟩⟩
  have hUL : (U ∩ (L ∪ D)).Nonempty :=
    ⟨(-1, 1), ⟨trivial, by norm_num⟩, Or.inl ⟨by norm_num, trivial⟩⟩
  have hc : IsPreconnected Kᶜ := by
    rw [hcomp, ← union_assoc, union_comm]
    exact hU.union' hUL (hL.union' hLD hD)
  have h₀ : (-1, (0 : ℝ)) ∈ Kᶜ := by norm_num [hK]
  have h : {C : Set (ℝ × ℝ) | ∃ x ∈ Kᶜ, C = connectedComponentIn Kᶜ x} = {Kᶜ} := by
    ext C
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_singleton_iff.2 (hc.connectedComponentIn hx)
    · intro hC
      exact ⟨(-1, 0), h₀, (mem_singleton_iff.1 hC).trans (hc.connectedComponentIn h₀).symm⟩
  change planeRegionCount K = 1
  rw [planeRegionCount, h, ncard_singleton]

example : ∃ (c : Fin 2 → ℝ × ℝ) (u : Fin 2 → Fin 3 → ℝ × ℝ),
    (∀ i j, u i j ≠ 0) ∧
      14 = planeRegionCount (⋃ i, ⋃ j, (fun s : ℝ => c i + s • u i j) '' Ici 0) := by
  exact (isGreatest_planeRegionCount_threeArmedV 2).1

end MetaMathlibExt.ThreeArmedVTest
