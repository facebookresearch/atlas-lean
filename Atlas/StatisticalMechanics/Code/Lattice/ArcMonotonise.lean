/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Lattice.CrossingParity
import Code.Lattice.PathVisitsRow
import Code.RSW.Defs
import Code.Universality.HVIntersection
import Code.Lattice.JordanStripInduction

open Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.RSW.Box
open StatMech.Universality







def amo_proj (ω : ConfigSpace (Sym2 (Site 2))) (S : Set (Site 2)) :
    (openSubgraphInduce 2 ω S) →g (hypercubicLattice 2) where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    rw [openSubgraphInduce_adj] at huv
    exact (openSubgraph_le ω) huv




theorem amo_connectedWithin_of_mem_support (ω : ConfigSpace (Sym2 (Site 2))) (S : Set (Site 2))
    {a b : (S : Set (Site 2))} (W : (openSubgraphInduce 2 ω S).Walk a b)
    {z : (S : Set (Site 2))} (hz : z ∈ W.support) :
    ConnectedWithin 2 ω S a z :=
  ⟨W.takeUntil z hz⟩













theorem amo_overlapComp_visits_row (ω : ConfigSpace (Sym2 (Site 2))) {m m' c d : ℤ}
    {xB yT : Site 2} (hxB : xB ∈ rect m m' c d) (hyT : yT ∈ rect m m' c d)
    (hxBc : xB 1 = c) (hyTd : yT 1 = d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
    (r : ℤ) (hcr : c ≤ r) (hrd : r ≤ d) :
    ∃ z : Site 2, z ∈ overlapComp ω m m' c d xB hxB ∧ z 1 = r ∧ m ≤ z 0 ∧ z 0 ≤ m' := by
  classical
  
  have hcd : c ≤ d := by have := mem_rect.mp hxB; omega
  
  obtain ⟨W⟩ := hcV
  
  have hac : (W.map (amo_proj ω (rect m m' c d))).getVert 0 1 = c := by
    rw [SimpleGraph.Walk.getVert_zero]; exact hxBc
  
  obtain ⟨z, hzs, hzr⟩ :=
    pvr_visits_every_row (W.map (amo_proj ω (rect m m' c d)))
      (c := c) (d := d) (by show (xB : Site 2) 1 = c; exact hxBc)
      (by show (yT : Site 2) 1 = d; exact hyTd) hcd r hcr hrd
  
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzs
  obtain ⟨zz, hzzs, hzze⟩ := hzs
  
  have hzzconn : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ zz :=
    amo_connectedWithin_of_mem_support ω (rect m m' c d) W hzzs
  have hzcomp : (zz : Site 2) ∈ overlapComp ω m m' c d xB hxB := ⟨zz.2, hzzconn⟩
  
  have hzzrect := mem_rect.mp zz.2
  refine ⟨(zz : Site 2), hzcomp, ?_, hzzrect.1, hzzrect.2.1⟩
  
  have hval : (zz : Site 2) = z := hzze
  rw [hval, hzr]














theorem amo_rowCell_of_vCrossing (ω : ConfigSpace (Sym2 (Site 2))) {m m' c d : ℤ}
    {xB yT : Site 2} (hxB : xB ∈ rect m m' c d) (hyT : yT ∈ rect m m' c d)
    (hxBc : xB 1 = c) (hyTd : yT 1 = d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩) :
    ∃ col : ℤ → ℤ,
      (∀ r, c ≤ r → r ≤ d → m ≤ col r) ∧
      (∀ r, c ≤ r → r ≤ d → col r ≤ m') ∧
      (∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ overlapComp ω m m' c d xB hxB) := by
  classical
  
  choose! f hf using fun r (hr : c ≤ r ∧ r ≤ d) =>
    amo_overlapComp_visits_row ω hxB hyT hxBc hyTd hcV r hr.1 hr.2
  
  refine ⟨fun r => (f r) 0, ?_, ?_, ?_⟩
  · intro r hcr hrd; exact (hf r ⟨hcr, hrd⟩).2.2.1
  · intro r hcr hrd; exact (hf r ⟨hcr, hrd⟩).2.2.2
  · intro r hcr hrd
    
    have hrow : (f r) 1 = r := (hf r ⟨hcr, hrd⟩).2.1
    have hcomp : (f r) ∈ overlapComp ω m m' c d xB hxB := (hf r ⟨hcr, hrd⟩).1
    have hcell : jsi_cell ((f r) 0) r = f r := by
      funext i; fin_cases i
      · show ((f r) 0 : ℤ) = (f r) 0; rfl
      · show (r : ℤ) = (f r) 1; rw [hrow]
    rw [hcell]; exact hcomp














theorem amo_overlapComp_allClosed (m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d) :
    overlapComp (fun _ => false) m m' c d xB hxB = {xB} := by
  ext z
  simp only [overlapComp, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_hz, hconn⟩
    obtain ⟨w⟩ := hconn
    have hno : ∀ (u v : (rect m m' c d : Set (Site 2))),
        ¬ (openSubgraphInduce 2 (fun _ => false) (rect m m' c d)).Adj u v := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact absurd huv.2 (by simp)
    cases w with
    | nil => rfl
    | cons h _ => exact absurd h (hno _ _)
  · rintro rfl
    exact ⟨hxB, connectedWithin_refl _ _ _⟩





theorem amo_singleton_no_monotoneArc {m m' c d : ℤ} (pt : Site 2) (hcd : c < d)
    (A : JsiMonotoneArc ({pt} : Set (Site 2)) m m' c d) : False := by
  have hc : jsi_cell (A.col c) c ∈ ({pt} : Set (Site 2)) :=
    A.on_arc (jsi_cell (A.col c) c) (by simp) (by simp only [jsi_cell_1]; omega) (by simp)
      (A.band_lo c (le_refl c) (by omega)) (A.band_hi c (le_refl c) (by omega))
  have hd : jsi_cell (A.col d) d ∈ ({pt} : Set (Site 2)) :=
    A.on_arc (jsi_cell (A.col d) d) (by simp only [jsi_cell_1]; omega) (by simp) (by simp)
      (A.band_lo d (by omega) (le_refl d)) (A.band_hi d (by omega) (le_refl d))
  rw [Set.mem_singleton_iff] at hc hd
  have heq : jsi_cell (A.col c) c = jsi_cell (A.col d) d := by rw [hc, hd]
  rw [jsi_cell_eq] at heq
  omega











theorem amo_hasMonotoneArc_false {m m' c d : ℤ} (hmm' : m ≤ m') (hcd : c < d) :
    ¬ JsiHasMonotoneArc (fun _ => false) m m' c d := by
  intro h
  have hxB : (jsi_cell m c) ∈ rect m m' c d := by
    rw [jsi_cell_mem_rect]; exact ⟨le_refl m, hmm', le_refl c, le_of_lt hcd⟩
  obtain ⟨A⟩ := h (jsi_cell m c) hxB
  rw [amo_overlapComp_allClosed] at A
  exact amo_singleton_no_monotoneArc (jsi_cell m c) hcd A

end Lattice

end StatMech
