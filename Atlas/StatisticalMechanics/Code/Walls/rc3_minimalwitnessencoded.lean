/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Code.Walls.rc2_minimalwitness

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}

section Fintype

variable [Fintype E] [DecidableEq E]
variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}














structure SupportEncodedMinimalWitness (A B : Set (ConfigSpace E)) (ω : ConfigSpace E)
    (s K L : Finset E) : Prop where
  
  support : s = cfgSupport ω
  
  disjoint : Disjoint K L
  
  minimalA : Minimal (fun S => cylinder S ω ⊆ A) K
  
  minimalB : Minimal (fun S => cylinder S ω ⊆ B) L








theorem cylinder_supportCfg_of_support {s : Finset E} (hs : s = cfgSupport ω) (K : Finset E) :
    cylinder K (supportCfg s) = cylinder K ω := by
  subst hs
  rw [supportCfg_cfgSupport]






theorem mem_cylinder_supportCfg_iff {s : Finset E} (hs : s = cfgSupport ω) (K : Finset E)
    (ω' : ConfigSpace E) :
    ω' ∈ cylinder K (supportCfg s) ↔ cfgSupport ω' ∩ K = s ∩ K := by
  rw [cylinder_supportCfg_of_support hs, cylinder_eq_supportSlice]
  subst hs
  rfl





theorem mem_of_supportEncoding_decode {s K L : Finset E}
    (h : SupportEncodedMinimalWitness A B ω s K L) :
    cylinder K (supportCfg s) ⊆ A ∧ cylinder L (supportCfg s) ⊆ B := by
  rw [cylinder_supportCfg_of_support h.support, cylinder_supportCfg_of_support h.support]
  exact ⟨h.minimalA.1, h.minimalB.1⟩









theorem exists_supportEncodedMinimalWitness (hω : ω ∈ disjointOccurrence A B) :
    ∃ s K L : Finset E, SupportEncodedMinimalWitness A B ω s K L := by
  obtain ⟨s, K, L, hs, hKL, hKmin, hLmin⟩ := exists_support_encoded_minimal_witness hω
  exact ⟨s, K, L, ⟨hs, hKL, hKmin, hLmin⟩⟩






theorem mem_of_supportEncodedMinimalWitness {s K L : Finset E}
    (h : SupportEncodedMinimalWitness A B ω s K L) :
    ω ∈ disjointOccurrence A B := by
  obtain ⟨hA, hB⟩ := mem_of_supportEncoding_decode h
  exact mem_of_support_encoding h.support h.disjoint hA hB







theorem mem_disjointOccurrence_iff_supportEncodedMinimalWitness :
    ω ∈ disjointOccurrence A B ↔
      ∃ s K L : Finset E, SupportEncodedMinimalWitness A B ω s K L :=
  ⟨exists_supportEncodedMinimalWitness,
    fun ⟨_, _, _, h⟩ => mem_of_supportEncodedMinimalWitness h⟩










theorem supportCfg_of_supportEncodedMinimalWitness {s K L : Finset E}
    (h : SupportEncodedMinimalWitness A B ω s K L) :
    supportCfg s = ω := by
  rw [h.support, supportCfg_cfgSupport]




theorem support_eq_cfgEquivFinset {s K L : Finset E}
    (h : SupportEncodedMinimalWitness A B ω s K L) :
    s = cfgEquivFinset ω := by
  rw [h.support, cfgEquivFinset_apply]

end Fintype








section Nonvacuity

variable [Fintype E] [DecidableEq E]
variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}





theorem exists_supportEncodedMinimalWitness_of_disjoint_witness {K L : Finset E}
    (hKL : Disjoint K L) (hA : cylinder K ω ⊆ A) (hB : cylinder L ω ⊆ B) :
    ∃ s K' L' : Finset E, SupportEncodedMinimalWitness A B ω s K' L' :=
  exists_supportEncodedMinimalWitness (mem_of_disjoint_witness hKL hA hB)

end Nonvacuity

end StatMech.Walls
