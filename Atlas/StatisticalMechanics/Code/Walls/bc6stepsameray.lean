/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Percolation.HrouteHighDim
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeaneUniqueness

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}










def bc6_clusterNbhd (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) : Set (Site d) :=
  ⋃ (t : ℕ) (_ : 1 ≤ t ∧ t ≤ L), cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ))



lemma bc6_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L : ℕ} {x : Site d} :
    x ∈ bc6_clusterNbhd ω j L ↔
      ∃ t : ℕ, (1 ≤ t ∧ t ≤ L) ∧ x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ)) := by
  simp only [bc6_clusterNbhd, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hx⟩; exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩; exact ⟨t, ht, hx⟩


lemma bc6_rayPt_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L t : ℕ}
    (h1 : 1 ≤ t) (h2 : t ≤ L) : hrHD_rayPt j (t : ℤ) ∈ bc6_clusterNbhd ω j L := by
  rw [bc6_mem_clusterNbhd]
  exact ⟨t, ⟨h1, h2⟩, self_mem_cluster _ _⟩









lemma bc6_corridorEdge_structure {j : Fin d} {L : ℕ} {u v : Site d}
    (h : s(u, v) ∈ hrHD_corridorEdges j L) :
    ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) := by
  rw [hrHD_corridorEdges, Finset.mem_image] at h
  obtain ⟨p, hp, hpe⟩ := h
  rw [Finset.mem_range] at hp
  exact ⟨p, hp, hpe.symm⟩










lemma bc6_sameAxis_step_mem (ω : ConfigSpace (Sym2 (Site d))) (a : Fin d) (La : ℕ)
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hmem : s(u, v) ∈ hrHD_corridorEdges a (La + 1)) :
    v ∈ bc6_clusterNbhd ω a (La + 1) := by
  obtain ⟨p, hp, hpe⟩ := bc6_corridorEdge_structure hmem
  
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  
  have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
    rw [← hpe]; exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hvmem
  rcases hvmem with rfl | rfl
  · 
    exact bc6_rayPt_mem_clusterNbhd hp1 (by omega)
  · 
    have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; exact bc6_rayPt_mem_clusterNbhd (by omega) (by omega)

end Walls

end StatMech
