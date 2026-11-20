/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Walls.rc5_minimalwitnessencoded

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}

section Fintype

variable [Fintype E] [DecidableEq E]
variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}












theorem occursMinimalWitness_support_unique {s s' K K' L L' : Finset E}
    (h : OccursMinimalWitness A B ω s K L) (h' : OccursMinimalWitness A B ω s' K' L') :
    s = s' := by
  rw [h.support, h'.support]





theorem occursMinimalWitness_decode {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    supportCfg s = ω :=
  supportCfg_of_occursMinimalWitness h








open Classical in





noncomputable def canonicalWitness (A B : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    Finset E × Finset E × Finset E :=
  if hω : ω ∈ disjointOccurrence A B then
    let p := exists_occursMinimalWitness hω
    (p.choose, p.choose_spec.choose, p.choose_spec.choose_spec.choose)
  else (∅, ∅, ∅)

open Classical in





theorem canonicalWitness_spec (hω : ω ∈ disjointOccurrence A B) :
    OccursMinimalWitness A B ω (canonicalWitness A B ω).1
      (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 := by
  unfold canonicalWitness
  rw [dif_pos hω]
  exact (exists_occursMinimalWitness hω).choose_spec.choose_spec.choose_spec






theorem canonicalWitness_support (hω : ω ∈ disjointOccurrence A B) :
    (canonicalWitness A B ω).1 = cfgSupport ω :=
  (canonicalWitness_spec hω).support


theorem canonicalWitness_disjoint (hω : ω ∈ disjointOccurrence A B) :
    Disjoint (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 :=
  (canonicalWitness_spec hω).disjoint



theorem canonicalWitness_minimalA (hω : ω ∈ disjointOccurrence A B) :
    Minimal (fun S : Finset E => OccursOn A (↑S) ω) (canonicalWitness A B ω).2.1 :=
  (canonicalWitness_spec hω).minimalA



theorem canonicalWitness_minimalB (hω : ω ∈ disjointOccurrence A B) :
    Minimal (fun S : Finset E => OccursOn B (↑S) ω) (canonicalWitness A B ω).2.2 :=
  (canonicalWitness_spec hω).minimalB



theorem canonicalWitness_occursOn (hω : ω ∈ disjointOccurrence A B) :
    OccursOn A (↑(canonicalWitness A B ω).2.1) ω ∧
      OccursOn B (↑(canonicalWitness A B ω).2.2) ω ∧
      Disjoint (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 :=
  occursOn_of_occursMinimalWitness (canonicalWitness_spec hω)



theorem canonicalWitness_not_occursOn_ssubsetA (hω : ω ∈ disjointOccurrence A B)
    {S : Finset E} (hlt : S ⊂ (canonicalWitness A B ω).2.1) :
    ¬ OccursOn A (↑S) ω :=
  not_occursOn_of_lt_minimalA (canonicalWitness_spec hω) hlt


theorem canonicalWitness_not_occursOn_ssubsetB (hω : ω ∈ disjointOccurrence A B)
    {S : Finset E} (hlt : S ⊂ (canonicalWitness A B ω).2.2) :
    ¬ OccursOn B (↑S) ω :=
  not_occursOn_of_lt_minimalB (canonicalWitness_spec hω) hlt






theorem canonicalWitness_decode (hω : ω ∈ disjointOccurrence A B) :
    supportCfg (canonicalWitness A B ω).1 = ω :=
  supportCfg_of_occursMinimalWitness (canonicalWitness_spec hω)






theorem canonicalWitness_mem {s K L : Finset E}
    (h : OccursMinimalWitness A B ω s K L) :
    ω ∈ disjointOccurrence A B :=
  mem_of_occursMinimalWitness h





theorem canonicalWitness_decode_occursOn (hω : ω ∈ disjointOccurrence A B) :
    OccursOn A (↑(canonicalWitness A B ω).2.1) (supportCfg (canonicalWitness A B ω).1) ∧
      OccursOn B (↑(canonicalWitness A B ω).2.2) (supportCfg (canonicalWitness A B ω).1) :=
  occursOn_of_occursEncoding_decode (canonicalWitness_spec hω)










theorem mem_disjointOccurrence_iff_canonicalWitness :
    ω ∈ disjointOccurrence A B ↔
      OccursMinimalWitness A B ω (canonicalWitness A B ω).1
        (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 :=
  ⟨canonicalWitness_spec, canonicalWitness_mem⟩





theorem mem_disjointOccurrence_iff_exists_via_canonical :
    ω ∈ disjointOccurrence A B ↔
      ∃ s K L : Finset E, OccursMinimalWitness A B ω s K L :=
  mem_disjointOccurrence_iff_occursMinimalWitness

end Fintype







section Nonvacuity

variable [Fintype E] [DecidableEq E]
variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}





theorem canonicalWitness_spec_of_disjoint_witness {K L : Set E}
    (hKL : Disjoint K L) (hA : OccursOn A K ω) (hB : OccursOn B L ω) :
    OccursMinimalWitness A B ω (canonicalWitness A B ω).1
      (canonicalWitness A B ω).2.1 (canonicalWitness A B ω).2.2 :=
  canonicalWitness_spec (mem_disjointOccurrence.mpr ⟨K, L, hKL, hA, hB⟩)

end Nonvacuity

end StatMech.Walls
