/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitWindingWitness

open Set SimpleGraph Function
open StatMech.Lattice

namespace StatMech.Walls













theorem kc3_eor_farLeft_rayCount_zero {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (t : Site 2) (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
    jec_rayCount t Vc = 0 :=
  jec_rayCount_eq_zero_of_right t Vc ht



theorem kc3_eor_farLeft_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (t : Site 2) (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
    Even (jec_rayCount t Vc) := by
  rw [kc3_eor_farLeft_rayCount_zero Vc t ht]; exact ⟨0, rfl⟩




theorem kc3_eor_farLeft_notMem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (t : Site 2) (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0) :
    t ∉ jec_leftRegion Vc :=
  pww_farLeft_notMem_leftRegion Vc ht



















theorem kc3_evenOddRule {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z t : Site 2} (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z t) :
    (¬ Even (jec_rayCount z Vc)) ↔
      (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
  
  have htout : ¬ ¬ Even (jec_rayCount t Vc) :=
    not_not.mpr (kc3_eor_farLeft_even Vc t ht)
  
  have hpar := crossCount_parity (jec_leftRegion Vc) γ
  simp only [jec_mem_leftRegion] at hpar
  
  constructor
  · intro hodd heven
    have hside := hpar.mp heven
    
    exact htout (hside.mp hodd)
  · intro hcrossOdd hray
    apply hcrossOdd
    rw [hpar]
    
    constructor
    · intro h; exact absurd h (not_not.mpr hray)
    · intro h; exact absurd h htout





theorem kc3_evenOddRule_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z t : Site 2} (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z t) :
    Even (jec_rayCount z Vc) ↔ Even (crossCount (jec_leftRegion Vc) γ) := by
  have h := kc3_evenOddRule Vc ht γ
  rw [not_iff_not] at h
  exact h





theorem kc3_evenOddRule_mod {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z t : Site 2} (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z t) :
    jec_rayCount z Vc % 2 = crossCount (jec_leftRegion Vc) γ % 2 := by
  have h := kc3_evenOddRule_even Vc ht γ
  rw [Nat.even_iff, Nat.even_iff] at h
  rcases Nat.mod_two_eq_zero_or_one (jec_rayCount z Vc) with hr | hr
  · rw [hr, (h.mp hr).symm]
  · rcases Nat.mod_two_eq_zero_or_one (crossCount (jec_leftRegion Vc) γ) with hc | hc
    · exact absurd (h.mpr hc) (by rw [hr]; decide)
    · rw [hr, hc]





theorem kc3_memLeftRegion_iff_oddCross {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z t : Site 2} (ht : ∀ p ∈ Vc.support, t 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z t) :
    z ∈ jec_leftRegion Vc ↔ ¬ Even (crossCount (jec_leftRegion Vc) γ) := by
  rw [jec_mem_leftRegion]
  exact kc3_evenOddRule Vc ht γ














theorem kc3_crossCount_indep_of_escape {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z t₁ t₂ : Site 2} (ht₁ : ∀ p ∈ Vc.support, t₁ 0 ≤ p 0)
    (ht₂ : ∀ p ∈ Vc.support, t₂ 0 ≤ p 0)
    (γ₁ : (hypercubicLattice 2).Walk z t₁) (γ₂ : (hypercubicLattice 2).Walk z t₂) :
    crossCount (jec_leftRegion Vc) γ₁ % 2 = crossCount (jec_leftRegion Vc) γ₂ % 2 := by
  rw [← kc3_evenOddRule_mod Vc ht₁ γ₁, ← kc3_evenOddRule_mod Vc ht₂ γ₂]













theorem kc3_evenOddRule_node :
    (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z t : Site 2),
        (∀ p ∈ Vc.support, t 0 ≤ p 0) →
        ∀ γ : (hypercubicLattice 2).Walk z t,
          (¬ Even (jec_rayCount z Vc)) ↔
            (¬ Even (crossCount (jec_leftRegion Vc) γ)))
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (t : Site 2),
        (∀ p ∈ Vc.support, t 0 ≤ p 0) → t ∉ jec_leftRegion Vc) :=
  ⟨fun _ Vc _ _ ht γ => kc3_evenOddRule Vc ht γ,
   fun _ Vc t ht => kc3_eor_farLeft_notMem_leftRegion Vc t ht⟩

end StatMech.Walls
