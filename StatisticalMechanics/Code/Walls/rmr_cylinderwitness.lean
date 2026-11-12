/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Code.Inequalities.PerOrbitCardClose

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}






def cylinder (K : Finset E) (ω : ConfigSpace E) : Set (ConfigSpace E) :=
  {ω' | agreeOn (↑K) ω ω'}

@[simp] theorem mem_cylinder {K : Finset E} {ω ω' : ConfigSpace E} :
    ω' ∈ cylinder K ω ↔ ∀ e ∈ K, ω' e = ω e := by
  simp only [cylinder, Set.mem_setOf_eq, agreeOn, Finset.mem_coe]


theorem self_mem_cylinder (K : Finset E) (ω : ConfigSpace E) : ω ∈ cylinder K ω :=
  agreeOn_refl _ ω




theorem cylinder_subset_iff_occursOn {A : Set (ConfigSpace E)} {K : Finset E}
    {ω : ConfigSpace E} : cylinder K ω ⊆ A ↔ OccursOn A (↑K) ω := Iff.rfl



theorem cylinder_subset_of_subset {K K' : Finset E} (h : K ⊆ K') (ω : ConfigSpace E) :
    cylinder K' ω ⊆ cylinder K ω := by
  intro ω' hω'
  simp only [mem_cylinder] at hω' ⊢
  exact fun e he => hω' e (h he)



theorem cylinder_subset_A_mono {A : Set (ConfigSpace E)} {K K' : Finset E}
    (h : K ⊆ K') (ω : ConfigSpace E) (hA : cylinder K ω ⊆ A) : cylinder K' ω ⊆ A :=
  (cylinder_subset_of_subset h ω).trans hA










theorem exists_minimal_cylinder_witness {A : Set (ConfigSpace E)} {ω : ConfigSpace E}
    {K : Finset E} (hK : cylinder K ω ⊆ A) :
    ∃ K₀ ⊆ K, Minimal (fun S => cylinder S ω ⊆ A) K₀ := by
  classical
  have hne : (K.powerset.filter (fun S => cylinder S ω ⊆ A)).Nonempty :=
    ⟨K, by simp [Finset.mem_powerset, hK]⟩
  obtain ⟨K₀, hmin⟩ :=
    (K.powerset.filter (fun S => cylinder S ω ⊆ A)).exists_minimal hne
  rw [minimal_iff] at hmin
  obtain ⟨hmem0, hmin0⟩ := hmin
  rw [Finset.mem_filter, Finset.mem_powerset] at hmem0
  obtain ⟨hsub0, hwit0⟩ := hmem0
  refine ⟨K₀, hsub0, ?_⟩
  rw [minimal_iff]
  refine ⟨hwit0, fun S hwitS hSle => ?_⟩
  have hSmem : S ∈ K.powerset.filter (fun S => cylinder S ω ⊆ A) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSle.trans hsub0, hwitS⟩
  exact hmin0 hSmem hSle

section Finite

variable [Finite E]





theorem mem_disjointOccurrence_iff_cylinder {A B : Set (ConfigSpace E)} {ω : ConfigSpace E} :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Finset E, Disjoint K L ∧ cylinder K ω ⊆ A ∧ cylinder L ω ⊆ B := by
  classical
  rw [mem_disjointOccurrence]
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨K.toFinite.toFinset, L.toFinite.toFinset,
      by rw [Set.Finite.disjoint_toFinset]; exact hKL,
      by rw [cylinder_subset_iff_occursOn, Set.Finite.coe_toFinset]; exact hA,
      by rw [cylinder_subset_iff_occursOn, Set.Finite.coe_toFinset]; exact hB⟩
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨↑K, ↑L, by rwa [Finset.disjoint_coe],
      by rwa [cylinder_subset_iff_occursOn] at hA,
      by rwa [cylinder_subset_iff_occursOn] at hB⟩





theorem mem_disjointOccurrence_iff_minimal_cylinder {A B : Set (ConfigSpace E)}
    {ω : ConfigSpace E} :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Finset E, Disjoint K L ∧
        Minimal (fun S => cylinder S ω ⊆ A) K ∧
        Minimal (fun S => cylinder S ω ⊆ B) L := by
  constructor
  · intro hω
    obtain ⟨K, L, hKL, hA, hB⟩ := mem_disjointOccurrence_iff_cylinder.mp hω
    obtain ⟨K₀, hK0sub, hK0min⟩ := exists_minimal_cylinder_witness hA
    obtain ⟨L₀, hL0sub, hL0min⟩ := exists_minimal_cylinder_witness hB
    exact ⟨K₀, L₀,
      Finset.disjoint_of_subset_left hK0sub (Finset.disjoint_of_subset_right hL0sub hKL),
      hK0min, hL0min⟩
  · rintro ⟨K, L, hKL, hKmin, hLmin⟩
    exact mem_disjointOccurrence_iff_cylinder.mpr ⟨K, L, hKL, hKmin.1, hLmin.1⟩

end Finite



section Fintype

variable [Fintype E] [DecidableEq E]

omit [DecidableEq E] in



theorem cylinder_filter_subset_iff_occursOn {A : Set (ConfigSpace E)} {ω : ConfigSpace E}
    (wK : E → Bool) :
    cylinder (Finset.univ.filter (fun a => wK a = true)) ω ⊆ A ↔
      OccursOn A {a | wK a = true} ω := by
  rw [cylinder_subset_iff_occursOn]
  have hcoe : (↑(Finset.univ.filter (fun a => wK a = true)) : Set E) = {a | wK a = true} := by
    ext a; simp
  rw [hcoe]

open Classical in





theorem slabBox_top_eq_cylinderWitness (A B : Set (ConfigSpace E)) :
    (StatMech.poc_slabBox A B StatMech.poc_topKey : Finset (ConfigSpace E)) =
      Finset.univ.filter (fun ω =>
        ∃ K L : Finset E, Disjoint K L ∧ cylinder K ω ⊆ A ∧ cylinder L ω ⊆ B) := by
  rw [StatMech.poc_slabBox_top]
  apply Finset.filter_congr
  intro ω _
  exact mem_disjointOccurrence_iff_cylinder

end Fintype

end StatMech.Walls
