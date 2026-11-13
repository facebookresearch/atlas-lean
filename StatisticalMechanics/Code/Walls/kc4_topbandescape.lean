/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.FloodFillConnected
import Code.Lattice.StraightWalk

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}









def kc4_supportSet (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {z | z ∈ Vc.support}

@[simp] theorem kc4_mem_supportSet (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    z ∈ kc4_supportSet Vc ↔ z ∈ Vc.support := Iff.rfl



theorem kc4_mem_exterior_of_row_high (R : ℕ) {z : Site 2} (hz : (R : ℤ) + 1 ≤ z 1) :
    z ∈ exterior 2 R := by
  refine ⟨1, ?_⟩
  have h2 : (R : ℤ) < |z 1| := by
    have : (R : ℤ) < z 1 := by omega
    exact lt_of_lt_of_le this (le_abs_self _)
  rw [Int.abs_eq_natAbs] at h2
  exact_mod_cast h2









theorem kc4_vertUp_support_col {z : Site 2} {R : ℕ} {w : Site 2}
    (hw : w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support) :
    ∃ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) ∧ w = ![z 0, t] :=
  (sw_vertSeg_mem_support (z 0) (z 1) ((R : ℤ) + 1) w).mp hw




theorem kc4_vertUp_clear_of_colClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support := by
  intro w hw
  obtain ⟨t, ht, rfl⟩ := kc4_vertUp_support_col hw
  exact hcol t ht










theorem kc4_reachesExterior_of_offSupport_walk (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z e : Site 2} (heExt : e ∈ exterior 2 R)
    (p : (hypercubicLattice 2).Walk z e) (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    ∃ e' : Site 2, e' ∈ exterior 2 R ∧
      (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e' := by
  have hzoff : z ∉ kc4_supportSet Vc := hp z p.start_mem_support
  refine ⟨e, heExt, ?_⟩
  rw [ffc_reachable_iff_offSupportWalk hzoff]
  exact ⟨p, fun w hw => hp w hw⟩










theorem kc4_reachesExterior_of_colClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e := by
  
  set e : Site 2 := ![z 0, (R : ℤ) + 1] with he
  have heExt : e ∈ exterior 2 R := kc4_mem_exterior_of_row_high R (by rw [he]; simp)
  
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine kc4_reachesExterior_of_offSupport_walk Vc R heExt p ?_
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact kc4_vertUp_clear_of_colClear Vc R hcol w hw






















theorem kc4_TopBandEscape (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : kc4_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e := by
  rcases lt_or_ge (R : ℤ) (z 1) with hlt | hge
  · 
    exact ⟨z, kc4_mem_exterior_of_row_high R (by omega), SimpleGraph.Reachable.refl _⟩
  · 
    
    have hzR : z 1 = R := le_antisymm hge hzrow
    refine kc4_reachesExterior_of_colClear Vc R ?_
    intro t ht hmem
    rw [Set.mem_uIcc] at ht
    
    have htbox : (![z 0, t] : Site 2) ∈ box 2 R := hsupp hmem
    have htabs : (t).natAbs ≤ R := by have := htbox 1; simpa using this
    have htle : t ≤ (R : ℤ) := by
      have : |t| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast htabs
      exact (abs_le.mp this).2
    
    have htR : t = (R : ℤ) := by omega
    subst htR
    
    have hzeq : (![z 0, (R : ℤ)] : Site 2) = z := by
      ext i; fin_cases i
      · simp
      · change (R : ℤ) = z 1; rw [hzR]
    rw [hzeq] at hmem
    exact hzoff hmem













theorem kc4_topBand_self (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hzrow : (R : ℤ) + 1 ≤ z 1) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (kc4_supportSet Vc)).Reachable z e :=
  ⟨z, kc4_mem_exterior_of_row_high R hzrow, SimpleGraph.Reachable.refl _⟩

end Walls

end StatMech
