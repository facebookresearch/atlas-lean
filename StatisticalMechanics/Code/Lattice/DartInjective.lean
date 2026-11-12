/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext

open SimpleGraph

namespace StatMech

namespace Lattice




theorem rot90Fun_injective : Function.Injective (rot90Fun : Site 2 → Site 2) := by
  have := rot90Equiv.injective; simpa using this


theorem rot90Fun_rot90Fun' (a : Site 2) : rot90Fun (rot90Fun a) = -a :=
  rot90Fun_rot90Fun a


theorem rot90Fun_neg (a : Site 2) : rot90Fun (-a) = -rot90Fun a := by
  funext i; fin_cases i <;> simp [rot90Fun]








theorem dartNext_right_tail (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).tail = e.head + (-rot90Fun e.dir) := by
  rw [dartNext_of_front_mem K e h, mkDart_tail]


theorem dartNext_straight_tail (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).tail = e.tail + (-rot90Fun e.dir) := by
  rw [dartNext_of_side_mem K e h1 h2, mkDart_tail]


theorem dartNext_straight_head (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).head = e.head + (-rot90Fun e.dir) := by
  rw [dartNext_of_side_mem K e h1 h2, mkDart_head, Dart.dir_def]; abel


theorem dartNext_straight_dir (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).dir = e.dir := by
  rw [dartNext_of_side_mem K e h1 h2, mkDart_dir]


theorem dartNext_left_tail (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    (dartNext K e).tail = e.tail := by
  rw [dartNext_of_corner K e h1 h2, mkDart_tail]


theorem dartNext_left_head (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    (dartNext K e).head = e.tail + (-rot90Fun e.dir) := by
  rw [dartNext_of_corner K e h1 h2, mkDart_head]


theorem dartNext_left_dir (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    (dartNext K e).dir = -rot90Fun e.dir := by
  rw [dartNext_of_corner K e h1 h2, mkDart_dir]





theorem dart_eq_of_head_dir {e₁ e₂ : Dart} (hH : e₁.head = e₂.head)
    (hd : e₁.dir = e₂.dir) : e₁ = e₂ := by
  have hT : e₁.tail = e₂.tail := by
    have h : e₁.head - e₁.tail = e₂.head - e₂.tail := hd
    have hrw : e₁.tail = e₁.head - (e₁.head - e₁.tail) := by abel
    rw [hrw, h, ← hH]; abel
  exact Dart.ext hT hH



theorem dart_eq_of_tail_dir {e₁ e₂ : Dart} (hT : e₁.tail = e₂.tail)
    (hd : e₁.dir = e₂.dir) : e₁ = e₂ := by
  have hH : e₁.head = e₂.head := by
    have h : e₁.head - e₁.tail = e₂.head - e₂.tail := hd
    have hrw : e₁.head = (e₁.head - e₁.tail) + e₁.tail := by abel
    rw [hrw, h, hT]; abel
  exact Dart.ext hT hH





theorem eq_of_dartNext_eq_right (K : Set (Site 2)) (e₁ e₂ : Dart)
    (a : e₁.head + (-rot90Fun e₁.dir) ∈ K) (b : e₂.head + (-rot90Fun e₂.dir) ∈ K)
    (heq : dartNext K e₁ = dartNext K e₂) : e₁ = e₂ := by
  have hH : e₁.head = e₂.head := by
    have := congrArg Dart.head heq
    rwa [(dartNext_front_head K e₁ a).1, (dartNext_front_head K e₂ b).1] at this
  have hd : e₁.dir = e₂.dir := by
    apply rot90Fun_injective
    have := congrArg Dart.dir heq
    rwa [(dartNext_front_head K e₁ a).2, (dartNext_front_head K e₂ b).2] at this
  exact dart_eq_of_head_dir hH hd



theorem eq_of_dartNext_eq_straight (K : Set (Site 2)) (e₁ e₂ : Dart)
    (a1 : e₁.head + (-rot90Fun e₁.dir) ∉ K) (a2 : e₁.tail + (-rot90Fun e₁.dir) ∈ K)
    (b1 : e₂.head + (-rot90Fun e₂.dir) ∉ K) (b2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K)
    (heq : dartNext K e₁ = dartNext K e₂) : e₁ = e₂ := by
  have hd : e₁.dir = e₂.dir := by
    have := congrArg Dart.dir heq
    rwa [dartNext_straight_dir K e₁ a1 a2, dartNext_straight_dir K e₂ b1 b2] at this
  have ht : e₁.tail = e₂.tail := by
    have := congrArg Dart.tail heq
    rw [dartNext_straight_tail K e₁ a1 a2, dartNext_straight_tail K e₂ b1 b2, hd] at this
    have hrw : e₁.tail = (e₁.tail + (-rot90Fun e₂.dir)) - (-rot90Fun e₂.dir) := by abel
    rw [hrw, this]; abel
  exact dart_eq_of_tail_dir ht hd



theorem eq_of_dartNext_eq_left (K : Set (Site 2)) (e₁ e₂ : Dart)
    (a1 : e₁.head + (-rot90Fun e₁.dir) ∉ K) (a2 : e₁.tail + (-rot90Fun e₁.dir) ∉ K)
    (b1 : e₂.head + (-rot90Fun e₂.dir) ∉ K) (b2 : e₂.tail + (-rot90Fun e₂.dir) ∉ K)
    (heq : dartNext K e₁ = dartNext K e₂) : e₁ = e₂ := by
  have hd : e₁.dir = e₂.dir := by
    have := congrArg Dart.dir heq
    rw [dartNext_left_dir K e₁ a1 a2, dartNext_left_dir K e₂ b1 b2] at this
    exact rot90Fun_injective (neg_injective this)
  have ht : e₁.tail = e₂.tail := by
    have := congrArg Dart.tail heq
    rwa [dartNext_left_tail K e₁ a1 a2, dartNext_left_tail K e₂ b1 b2] at this
  exact dart_eq_of_tail_dir ht hd











theorem not_dartNext_eq_right_straight (K : Set (Site 2)) (e₁ e₂ : Dart)
    (b1t : e₁.tail ∈ K) (b2h : e₂.head ∉ K)
    (hR : e₁.head + (-rot90Fun e₁.dir) ∈ K)
    (hS1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
    (hS2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K)
    (heq : dartNext K e₁ = dartNext K e₂) : False := by
  have hdir : rot90Fun e₁.dir = e₂.dir := by
    have := congrArg Dart.dir heq
    rwa [(dartNext_front_head K e₁ hR).2, dartNext_straight_dir K e₂ hS1 hS2] at this
  have hhead : e₁.head = e₂.head + (-rot90Fun e₂.dir) := by
    have := congrArg Dart.head heq
    rwa [(dartNext_front_head K e₁ hR).1, dartNext_straight_head K e₂ hS1 hS2] at this
  have key : e₂.head = e₁.tail := by
    have e1t : e₁.tail = e₁.head - e₁.dir := by rw [Dart.dir_def]; abel
    have hsq : rot90Fun (rot90Fun e₁.dir) = -e₁.dir := rot90Fun_rot90Fun' e₁.dir
    rw [hdir] at hsq
    rw [e1t]
    have hh : e₁.head = e₂.head + (-rot90Fun e₂.dir) := hhead
    rw [hsq] at hh
    rw [hh]; abel
  rw [key] at b2h; exact b2h b1t




theorem not_dartNext_eq_right_left (K : Set (Site 2)) (e₁ e₂ : Dart)
    (b1t : e₁.tail ∈ K)
    (hR : e₁.head + (-rot90Fun e₁.dir) ∈ K)
    (hL1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
    (hL2 : e₂.tail + (-rot90Fun e₂.dir) ∉ K)
    (heq : dartNext K e₁ = dartNext K e₂) : False := by
  have hdir : rot90Fun e₁.dir = -rot90Fun e₂.dir := by
    have := congrArg Dart.dir heq
    rwa [(dartNext_front_head K e₁ hR).2, dartNext_left_dir K e₂ hL1 hL2] at this
  have hhead : e₁.head = e₂.tail + (-rot90Fun e₂.dir) := by
    have := congrArg Dart.head heq
    rwa [(dartNext_front_head K e₁ hR).1, dartNext_left_head K e₂ hL1 hL2] at this
  have hd : e₁.dir = -e₂.dir := by
    apply rot90Fun_injective
    rw [hdir, rot90Fun_neg]
  have key : e₁.tail = e₂.head + (-rot90Fun e₂.dir) := by
    have e1t : e₁.tail = e₁.head - e₁.dir := by rw [Dart.dir_def]; abel
    have e2h : e₂.head = e₂.tail + e₂.dir := by rw [Dart.dir_def]; abel
    rw [e1t, hhead, hd, e2h]; abel
  rw [key] at b1t; exact hL1 b1t




theorem not_dartNext_eq_straight_left (K : Set (Site 2)) (e₁ e₂ : Dart)
    (b1t : e₁.tail ∈ K) (b2h : e₂.head ∉ K)
    (hS1 : e₁.head + (-rot90Fun e₁.dir) ∉ K)
    (hS2 : e₁.tail + (-rot90Fun e₁.dir) ∈ K)
    (hL1 : e₂.head + (-rot90Fun e₂.dir) ∉ K)
    (hL2 : e₂.tail + (-rot90Fun e₂.dir) ∉ K)
    (heq : dartNext K e₁ = dartNext K e₂) : False := by
  have hdir : e₁.dir = -rot90Fun e₂.dir := by
    have := congrArg Dart.dir heq
    rwa [dartNext_straight_dir K e₁ hS1 hS2, dartNext_left_dir K e₂ hL1 hL2] at this
  have htail : e₁.tail + (-rot90Fun e₁.dir) = e₂.tail := by
    have := congrArg Dart.tail heq
    rwa [dartNext_straight_tail K e₁ hS1 hS2, dartNext_left_tail K e₂ hL1 hL2] at this
  have hr : rot90Fun e₁.dir = e₂.dir := by
    rw [hdir, rot90Fun_neg, rot90Fun_rot90Fun', neg_neg]
  have key : e₁.tail = e₂.head := by
    have e2h : e₂.head = e₂.tail + e₂.dir := by rw [Dart.dir_def]; abel
    rw [e2h, ← htail, hr]; abel
  rw [key] at b1t; exact b2h b1t










theorem dartNext_injOn (K : Set (Site 2)) :
    Set.InjOn (dartNext K) {e | IsBoundaryDart K e} := by
  rintro e₁ ⟨h1t, h1h⟩ e₂ ⟨h2t, h2h⟩ heq
  
  by_cases hA1 : e₁.head + (-rot90Fun e₁.dir) ∈ K
  · 
    by_cases hB1 : e₂.head + (-rot90Fun e₂.dir) ∈ K
    · exact eq_of_dartNext_eq_right K e₁ e₂ hA1 hB1 heq
    · by_cases hB2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K
      · 
        exact absurd heq (fun h => not_dartNext_eq_right_straight K e₁ e₂ h1t h2h hA1 hB1 hB2 h)
      · 
        exact absurd heq (fun h => not_dartNext_eq_right_left K e₁ e₂ h1t hA1 hB1 hB2 h)
  · by_cases hA2 : e₁.tail + (-rot90Fun e₁.dir) ∈ K
    · 
      by_cases hB1 : e₂.head + (-rot90Fun e₂.dir) ∈ K
      · 
        exact absurd heq
          (fun h => not_dartNext_eq_right_straight K e₂ e₁ h2t h1h hB1 hA1 hA2 h.symm)
      · by_cases hB2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K
        · 
          exact eq_of_dartNext_eq_straight K e₁ e₂ hA1 hA2 hB1 hB2 heq
        · 
          exact absurd heq
            (fun h => not_dartNext_eq_straight_left K e₁ e₂ h1t h2h hA1 hA2 hB1 hB2 h)
    · 
      by_cases hB1 : e₂.head + (-rot90Fun e₂.dir) ∈ K
      · 
        exact absurd heq
          (fun h => not_dartNext_eq_right_left K e₂ e₁ h2t hB1 hA1 hA2 h.symm)
      · by_cases hB2 : e₂.tail + (-rot90Fun e₂.dir) ∈ K
        · 
          exact absurd heq
            (fun h => not_dartNext_eq_straight_left K e₂ e₁ h2t h1h hB1 hB2 hA1 hA2 h.symm)
        · 
          exact eq_of_dartNext_eq_left K e₁ e₂ hA1 hA2 hB1 hB2 heq





theorem unitVectors_finite : {z : Site 2 | unitWt z = 1}.Finite := by
  apply (box_finite 2 1).subset
  intro z hz
  rw [Set.mem_setOf_eq, unitWt] at hz
  rw [mem_box]
  intro i
  by_contra h
  rw [not_le] at h
  have hle : (z i).natAbs ≤ ∑ j, (z j).natAbs :=
    Finset.single_le_sum (f := fun j => (z j).natAbs) (by intros; positivity)
      (Finset.mem_univ i)
  omega




theorem boundaryDarts_finite (K : Set (Site 2)) (hK : K.Finite) :
    {e : Dart | IsBoundaryDart K e}.Finite := by
  apply Set.Finite.of_finite_image (f := fun e : Dart => (e.tail, e.dir))
  · apply Set.Finite.subset (hK.prod unitVectors_finite)
    rintro _ ⟨e, he, rfl⟩
    exact ⟨he.1, unitWt_dir e⟩
  · rintro e₁ _ e₂ _ h
    simp only [Prod.mk.injEq] at h
    exact dart_eq_of_tail_dir h.1 h.2







theorem dartNext_bijOn_of_finite (K : Set (Site 2)) (hK : K.Finite) :
    Set.BijOn (dartNext K) {e | IsBoundaryDart K e} {e | IsBoundaryDart K e} := by
  have hmaps : Set.MapsTo (dartNext K) {e | IsBoundaryDart K e}
      {e | IsBoundaryDart K e} := fun e he => dartNext_isBoundaryDart K e he
  exact (Set.Finite.injOn_iff_bijOn_of_mapsTo (boundaryDarts_finite K hK) hmaps).mp
    (dartNext_injOn K)

end Lattice

end StatMech
