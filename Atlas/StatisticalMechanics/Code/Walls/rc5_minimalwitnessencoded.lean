/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Code.Walls.rc3_minimalwitnessencoded

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}

section Fintype

variable [Fintype E] [DecidableEq E]
variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}

















structure OccursMinimalWitness (A B : Set (ConfigSpace E)) (ω : ConfigSpace E)
    (s K L : Finset E) : Prop where
  
  support : s = cfgSupport ω
  
  disjoint : Disjoint K L
  
  minimalA : Minimal (fun S : Finset E => OccursOn A (↑S) ω) K
  
  minimalB : Minimal (fun S : Finset E => OccursOn B (↑S) ω) L











theorem occursMinimalWitness_iff_supportEncoded {s K L : Finset E} :
    OccursMinimalWitness A B ω s K L ↔ SupportEncodedMinimalWitness A B ω s K L :=
  ⟨fun h => ⟨h.support, h.disjoint, h.minimalA, h.minimalB⟩,
    fun h => ⟨h.support, h.disjoint, h.minimalA, h.minimalB⟩⟩








theorem occursOn_supportCfg_of_support {s : Finset E} (hs : s = cfgSupport ω) (K : Finset E) :
    OccursOn A (↑K) (supportCfg s) ↔ OccursOn A (↑K) ω := by
  subst hs
  rw [supportCfg_cfgSupport]






theorem occursOn_iff_supportSlice {s : Finset E} (hs : s = cfgSupport ω) (K : Finset E)
    (ω' : ConfigSpace E) :
    ω' ∈ cylinder K (supportCfg s) ↔ cfgSupport ω' ∩ K = s ∩ K :=
  mem_cylinder_supportCfg_iff hs K ω'






theorem occursOn_of_occursEncoding_decode {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    OccursOn A (↑K) (supportCfg s) ∧ OccursOn B (↑L) (supportCfg s) := by
  obtain ⟨hA, hB⟩ :=
    mem_of_supportEncoding_decode (occursMinimalWitness_iff_supportEncoded.mp h)
  exact ⟨hA, hB⟩








theorem exists_occursMinimalWitness (hω : ω ∈ disjointOccurrence A B) :
    ∃ s K L : Finset E, OccursMinimalWitness A B ω s K L := by
  obtain ⟨s, K, L, h⟩ := exists_supportEncodedMinimalWitness hω
  exact ⟨s, K, L, occursMinimalWitness_iff_supportEncoded.mpr h⟩






theorem mem_of_occursMinimalWitness {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    ω ∈ disjointOccurrence A B :=
  mem_of_supportEncodedMinimalWitness (occursMinimalWitness_iff_supportEncoded.mp h)







theorem mem_disjointOccurrence_iff_occursMinimalWitness :
    ω ∈ disjointOccurrence A B ↔
      ∃ s K L : Finset E, OccursMinimalWitness A B ω s K L :=
  ⟨exists_occursMinimalWitness,
    fun ⟨_, _, _, h⟩ => mem_of_occursMinimalWitness h⟩









theorem occursOn_of_occursMinimalWitness {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    OccursOn A (↑K) ω ∧ OccursOn B (↑L) ω ∧ Disjoint K L :=
  ⟨h.minimalA.1, h.minimalB.1, h.disjoint⟩





theorem not_occursOn_of_lt_minimalA {s K L S : Finset E}
    (h : OccursMinimalWitness A B ω s K L) (hlt : S ⊂ K) :
    ¬ OccursOn A (↑S) ω := by
  intro hS
  exact absurd (h.minimalA.eq_of_le hS (le_of_lt hlt)) (ne_of_lt hlt)



theorem not_occursOn_of_lt_minimalB {s K L S : Finset E}
    (h : OccursMinimalWitness A B ω s K L) (hlt : S ⊂ L) :
    ¬ OccursOn B (↑S) ω := by
  intro hS
  exact absurd (h.minimalB.eq_of_le hS (le_of_lt hlt)) (ne_of_lt hlt)










theorem supportCfg_of_occursMinimalWitness {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    supportCfg s = ω :=
  supportCfg_of_supportEncodedMinimalWitness (occursMinimalWitness_iff_supportEncoded.mp h)




theorem support_eq_cfgEquivFinset_of_occursMinimalWitness {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    s = cfgEquivFinset ω :=
  support_eq_cfgEquivFinset (occursMinimalWitness_iff_supportEncoded.mp h)

end Fintype








section Nonvacuity

variable [Fintype E] [DecidableEq E]
variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}





theorem exists_occursMinimalWitness_of_disjoint_witness {K L : Set E}
    (hKL : Disjoint K L) (hA : OccursOn A K ω) (hB : OccursOn B L ω) :
    ∃ s K' L' : Finset E, OccursMinimalWitness A B ω s K' L' :=
  exists_occursMinimalWitness (mem_disjointOccurrence.mpr ⟨K, L, hKL, hA, hB⟩)

end Nonvacuity

end StatMech.Walls
