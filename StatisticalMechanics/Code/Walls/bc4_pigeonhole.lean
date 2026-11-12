/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib

open Set

namespace StatMech

namespace Walls








theorem bc4_finite_biUnion_infinite {α ι : Type*} {S : Set ι} (hS : S.Finite)
    {f : ι → Set α} (hinf : (⋃ i ∈ S, f i).Infinite) :
    ∃ i ∈ S, (f i).Infinite := by
  by_contra hcon
  
  simp only [not_exists, not_and, Set.not_infinite] at hcon
  exact hinf (Set.Finite.biUnion hS (fun i hi => hcon i hi))



theorem bc4_finite_iUnion_infinite {α ι : Type*} [Finite ι] {f : ι → Set α}
    (hinf : (⋃ i, f i).Infinite) : ∃ i, (f i).Infinite := by
  by_contra hcon
  simp only [not_exists, Set.not_infinite] at hcon
  exact hinf (Set.finite_iUnion hcon)







theorem bc4_finset_biUnion_infinite {α ι : Type*} (s : Finset ι) {f : ι → Set α}
    (hinf : (⋃ i ∈ s, f i).Infinite) : ∃ i ∈ s, (f i).Infinite := by
  
  have hset : (⋃ i ∈ (s : Set ι), f i) = (⋃ i ∈ s, f i) := by
    ext x; simp
  rw [← hset] at hinf
  obtain ⟨i, hi, hfi⟩ := bc4_finite_biUnion_infinite s.finite_toSet hinf
  exact ⟨i, hi, hfi⟩



theorem bc4_finite_sUnion_infinite {α : Type*} {C : Set (Set α)} (hC : C.Finite)
    (hinf : (⋃₀ C).Infinite) : ∃ t ∈ C, Set.Infinite t := by
  by_contra hcon
  simp only [not_exists, not_and, Set.not_infinite] at hcon
  exact hinf (Set.Finite.sUnion hC (fun t ht => hcon t ht))

end Walls

end StatMech
