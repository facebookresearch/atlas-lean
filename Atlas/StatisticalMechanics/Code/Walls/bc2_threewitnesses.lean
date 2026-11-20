/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Mathlib
import Code.Percolation.TrifurcationConstruction

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}










def bc2_ThreeWitnesses (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃









theorem bc2_threeWitnesses (n : ℕ) : bc2_ThreeWitnesses d n := by
  intro ω hω
  obtain ⟨_, x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  exact ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩












theorem bc2_disjoint_of_ne {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : cluster d ω x ≠ cluster d ω y) : Disjoint (cluster d ω x) (cluster d ω y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  apply h
  
  have hxz : Connected d ω x z := mem_cluster.mp hzx
  have hyz : Connected d ω y z := mem_cluster.mp hzy
  have hxy : Connected d ω x y := hxz.trans hyz.symm
  exact cluster_eq_of_connected hxy





theorem bc2_threeWitnesses_pairwise_disjoint (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      Disjoint (cluster d ω x₁) (cluster d ω x₂) ∧
      Disjoint (cluster d ω x₁) (cluster d ω x₃) ∧
      Disjoint (cluster d ω x₂) (cluster d ω x₃) := by
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ :=
    bc2_threeWitnesses n ω hω
  exact ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3,
    bc2_disjoint_of_ne hd12, bc2_disjoint_of_ne hd13, bc2_disjoint_of_ne hd23⟩









theorem bc2_distinct_sites (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ :=
    bc2_threeWitnesses n ω hω
  refine ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, ?_, ?_, ?_⟩
  · intro h; exact hd12 (by rw [h])
  · intro h; exact hd13 (by rw [h])
  · intro h; exact hd23 (by rw [h])









theorem bc2_threeMeetBox_numInfinite (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) : numInfiniteClusters d ω = ⊤ :=
  hω.1


















theorem bc2_three_witnesses_node (n : ℕ) :
    bc2_ThreeWitnesses d n ∧
      (∀ ω ∈ threeMeetBox d n,
        ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
          (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
          Disjoint (cluster d ω x₁) (cluster d ω x₂) ∧
          Disjoint (cluster d ω x₁) (cluster d ω x₃) ∧
          Disjoint (cluster d ω x₂) (cluster d ω x₃)) :=
  ⟨bc2_threeWitnesses n, fun ω hω => bc2_threeWitnesses_pairwise_disjoint n ω hω⟩

end Walls

end StatMech
