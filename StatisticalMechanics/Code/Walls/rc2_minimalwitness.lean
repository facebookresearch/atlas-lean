/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Code.Walls.rmr_cylinderwitness

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}








variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}






theorem exists_minimal_witness_of_wellFounded {A : Set (ConfigSpace E)} {ω : ConfigSpace E}
    {K : Finset E} (hK : cylinder K ω ⊆ A) :
    ∃ K₀ ⊆ K, Minimal (fun S => cylinder S ω ⊆ A) K₀ := by
  classical
  exact exists_minimal_le_of_wellFoundedLT (fun S => cylinder S ω ⊆ A) K hK




theorem not_witness_of_lt_minimal {K S : Finset E}
    (hmin : Minimal (fun S => cylinder S ω ⊆ A) K) (hlt : S ⊂ K) :
    ¬ cylinder S ω ⊆ A := by
  intro hS
  exact absurd (hmin.eq_of_le hS (le_of_lt hlt)) (ne_of_lt hlt)




theorem minimal_witness_eq_of_subset {K S : Finset E}
    (hmin : Minimal (fun S => cylinder S ω ⊆ A) K) (hS : cylinder S ω ⊆ A) (hSK : S ⊆ K) :
    S = K :=
  hmin.eq_of_le hS hSK




theorem minimal_witness_card_le {K S : Finset E}
    (hmin : Minimal (fun S => cylinder S ω ⊆ A) K) (hS : cylinder S ω ⊆ A) (hSK : S ⊆ K) :
    K.card ≤ S.card :=
  le_of_eq (congrArg Finset.card (minimal_witness_eq_of_subset hmin hS hSK)).symm

section Finite

variable [Finite E]














theorem exists_minimal_disjoint_witness :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Finset E, Disjoint K L ∧
        Minimal (fun S => cylinder S ω ⊆ A) K ∧
        Minimal (fun S => cylinder S ω ⊆ B) L :=
  mem_disjointOccurrence_iff_minimal_cylinder



theorem minimal_disjoint_witness_of_mem (hω : ω ∈ disjointOccurrence A B) :
    ∃ K L : Finset E, Disjoint K L ∧
      Minimal (fun S => cylinder S ω ⊆ A) K ∧
      Minimal (fun S => cylinder S ω ⊆ B) L :=
  exists_minimal_disjoint_witness.mp hω



theorem mem_of_disjoint_witness {K L : Finset E} (hKL : Disjoint K L)
    (hA : cylinder K ω ⊆ A) (hB : cylinder L ω ⊆ B) :
    ω ∈ disjointOccurrence A B :=
  mem_disjointOccurrence_iff_cylinder.mpr ⟨K, L, hKL, hA, hB⟩

end Finite










section Fintype

variable [Fintype E] [DecidableEq E]





theorem cylinder_eq_supportSlice (K : Finset E) (ω ω' : ConfigSpace E) :
    ω' ∈ cylinder K ω ↔ cfgSupport ω' ∩ K = cfgSupport ω ∩ K := by
  rw [mem_cylinder]
  constructor
  · intro h
    ext i
    simp only [Finset.mem_inter, mem_cfgSupport]
    constructor
    · rintro ⟨hi, hiK⟩; exact ⟨by rw [← h i hiK]; exact hi, hiK⟩
    · rintro ⟨hi, hiK⟩; exact ⟨by rw [h i hiK]; exact hi, hiK⟩
  · intro h i hiK
    have hiff := congrArg (fun s => i ∈ s) h
    simp only [Finset.mem_inter, mem_cfgSupport] at hiff
    rw [eq_iff_iff] at hiff
    
    cases hb' : ω' i with
    | true =>
      exact (hiff.mp ⟨hb', hiK⟩).1.symm
    | false =>
      cases hb : ω i with
      | false => rfl
      | true => exact absurd (hiff.mpr ⟨hb, hiK⟩).1 (by rw [hb']; exact Bool.false_ne_true)






theorem exists_support_encoded_minimal_witness (hω : ω ∈ disjointOccurrence A B) :
    ∃ (s K L : Finset E), s = cfgSupport ω ∧ Disjoint K L ∧
      Minimal (fun S => cylinder S ω ⊆ A) K ∧
      Minimal (fun S => cylinder S ω ⊆ B) L := by
  obtain ⟨K, L, hKL, hKmin, hLmin⟩ := minimal_disjoint_witness_of_mem hω
  exact ⟨cfgSupport ω, K, L, rfl, hKL, hKmin, hLmin⟩




theorem mem_of_support_encoding {s K L : Finset E} (hs : s = cfgSupport ω)
    (hKL : Disjoint K L) (hA : cylinder K (supportCfg s) ⊆ A) (hB : cylinder L (supportCfg s) ⊆ B) :
    ω ∈ disjointOccurrence A B := by
  subst hs
  rw [supportCfg_cfgSupport] at hA hB
  exact mem_of_disjoint_witness hKL hA hB

end Fintype

end StatMech.Walls
