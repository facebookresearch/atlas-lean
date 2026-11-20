/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.RSW.Defs
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}









@[simp] theorem des_rot90Inv_zero (x : Site 2) : (rot90Inv x) 0 = x 1 := by
  simp [rot90Inv]
@[simp] theorem des_rot90Inv_one (x : Site 2) : (rot90Inv x) 1 = - x 0 := by
  simp [rot90Inv]



theorem des_rot90Inv_rect (n : ℤ) (x : Site 2) :
    x ∈ rect 0 n 0 n ↔ rot90Inv x ∈ rect 0 n (-n) 0 := by
  simp only [mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩



theorem des_rot90Inv_bottomSide (n : ℤ) (x : Site 2) :
    x ∈ bottomSide 0 n 0 n ↔ rot90Inv x ∈ leftSide 0 n (-n) 0 := by
  simp only [mem_bottomSide, mem_leftSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩



theorem des_rot90Inv_topSide (n : ℤ) (x : Site 2) :
    x ∈ topSide 0 n 0 n ↔ rot90Inv x ∈ rightSide 0 n (-n) 0 := by
  simp only [mem_topSide, mem_rightSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩















def des_negConfig (ω : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => !(ω e)

@[simp] theorem des_negConfig_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    des_negConfig ω e = !(ω e) := rfl


theorem des_negConfig_open_iff_closed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    des_negConfig ω e = true ↔ ω e = false := by
  rw [des_negConfig_apply]; cases ω e <;> simp





theorem des_isOpenEdge_dual_iff (ω : ConfigSpace (Sym2 (Site 2))) (p q : Site 2) :
    IsOpenEdge 2 (dualConfig ω) p q ↔
      IsOpenEdge 2 (des_negConfig ω) (rot90Inv p) (rot90Inv q) := by
  unfold IsOpenEdge
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨?_, ?_⟩
    · 
      have := (rot90_adj (rot90Inv p) (rot90Inv q))
      rw [show rot90Fun (rot90Inv p) = p from rot90Equiv.right_inv p,
          show rot90Fun (rot90Inv q) = q from rot90Equiv.right_inv q] at this
      exact this.mp hadj
    · rw [des_negConfig_open_iff_closed]
      rw [dual_isOpen_iff_isClosed] at hopen
      rwa [show (crossEdge.symm s(p, q)) = s(rot90Inv p, rot90Inv q) by
        simp [crossEdge, sym2Congr, Sym2.map_mk]] at hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨?_, ?_⟩
    · have := (rot90_adj (rot90Inv p) (rot90Inv q))
      rw [show rot90Fun (rot90Inv p) = p from rot90Equiv.right_inv p,
          show rot90Fun (rot90Inv q) = q from rot90Equiv.right_inv q] at this
      exact this.mpr hadj
    · rw [des_negConfig_open_iff_closed] at hopen
      rw [dual_isOpen_iff_isClosed]
      rwa [show (crossEdge.symm s(p, q)) = s(rot90Inv p, rot90Inv q) by
        simp [crossEdge, sym2Congr, Sym2.map_mk]]




noncomputable def des_inducedHom (n : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)) →g
      (openSubgraphInduce 2 (des_negConfig ω) (rect 0 n (-n) 0)) where
  toFun := fun x => ⟨rot90Inv (x : Site 2), (des_rot90Inv_rect n x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    show IsOpenEdge 2 (des_negConfig ω) (rot90Inv (x : Site 2)) (rot90Inv (y : Site 2))
    exact (des_isOpenEdge_dual_iff ω (x : Site 2) (y : Site 2)).1 hxy




noncomputable def des_inducedHomInv (n : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (des_negConfig ω) (rect 0 n (-n) 0)) →g
      (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)) where
  toFun := fun x => ⟨rot90Fun (x : Site 2),
    (des_rot90Inv_rect n (rot90Fun (x : Site 2))).2 (by
      rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2)⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    show IsOpenEdge 2 (dualConfig ω) (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))
    rw [des_isOpenEdge_dual_iff ω (rot90Fun (x : Site 2)) (rot90Fun (y : Site 2))]
    rw [show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2),
       show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from
        rot90Equiv.left_inv (y : Site 2)]
    exact hxy






theorem des_dualV_iff_negH (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    DualVerticalCrossing ω 0 n 0 n ↔ HorizontalCrossing (des_negConfig ω) 0 n (-n) 0 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Inv (x : Site 2), (des_rot90Inv_bottomSide n x).1 x.2⟩,
            ⟨rot90Inv (y : Site 2), (des_rot90Inv_topSide n y).1 y.2⟩, ?_⟩
    exact (hxy : (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)).Reachable _ _).map
      (des_inducedHom n ω)
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Fun (x : Site 2), ?_⟩, ⟨rot90Fun (y : Site 2), ?_⟩, ?_⟩
    · rw [des_rot90Inv_bottomSide n, show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2
    · rw [des_rot90Inv_topSide n, show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from
        rot90Equiv.left_inv (y : Site 2)]; exact y.2
    · exact (hxy : (openSubgraphInduce 2 (des_negConfig ω) (rect 0 n (-n) 0)).Reachable _ _).map
        (des_inducedHomInv n ω)





theorem des_dualVerticalCrossingEvent_eq (n : ℤ) :
    dualVerticalCrossingEvent 0 n 0 n
      = {ω | HorizontalCrossing (des_negConfig ω) 0 n (-n) 0} := by
  ext ω
  rw [mem_dualVerticalCrossingEvent, Set.mem_setOf_eq, dualVerticalCrossing_iff]
  exact des_dualV_iff_negH ω n
















theorem des_hsepSquare_iff_closedH_rotbox (n : ℤ) :
    ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) ↔
      (∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 n 0 n →
        HorizontalCrossing (des_negConfig ω) 0 n (-n) 0) := by
  constructor
  · intro h ω hno
    have : ω ∈ dualVerticalCrossingEvent 0 n 0 n := h (by
      simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact hno)
    rw [mem_dualVerticalCrossingEvent, dualVerticalCrossing_iff] at this
    exact (des_dualV_iff_negH ω n).1 this
  · intro h ω hω
    simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
    rw [mem_dualVerticalCrossingEvent, dualVerticalCrossing_iff]
    exact (des_dualV_iff_negH ω n).2 (h ω hω)





















noncomputable def des_cutConfig : ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e => decide (¬ ∃ b : ℤ, e = s(![0, b], ![1, b]))


theorem des_cutConfig_cut_closed (b : ℤ) : des_cutConfig s(![0, b], ![1, b]) = false := by
  classical
  simp only [des_cutConfig, decide_eq_false_iff_not, not_not]
  exact ⟨b, rfl⟩


theorem des_cutConfig_open_of_not_cut {e : Sym2 (Site 2)}
    (h : ¬ ∃ b : ℤ, e = s(![0, b], ![1, b])) : des_cutConfig e = true := by
  classical
  simp only [des_cutConfig, decide_eq_true_eq]
  exact h




theorem des_cross_edge_is_cut {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u 0 = 0) (hv : v 0 = 1) : s(u, v) = s(![0, u 1], ![1, u 1]) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two, hu, hv] at hadj
  set b := u 1 with hb
  have h1 : b = v 1 := by
    have : (b - v 1).natAbs = 0 := by omega
    omega
  have hue : u = ![0, b] := by
    funext i; fin_cases i
    · simpa using hu
    · simp [← hb]
  have hve : v = ![1, b] := by
    funext i; fin_cases i
    · simpa using hv
    · simp [h1]
  rw [hue, hve]



theorem des_cutConfig_no_cross {u v : Site 2}
    (h : IsOpenEdge 2 des_cutConfig u v) (hu : u 0 = 0) (hv : v 0 = 1) : False := by
  obtain ⟨hadj, hopen⟩ := h
  rw [des_cross_edge_is_cut hadj hu hv, des_cutConfig_cut_closed] at hopen
  exact absurd hopen (by simp)




theorem des_cutConfig_open_sameSide0 {u v : Site 2}
    (h : IsOpenEdge 2 des_cutConfig u v) : (u 0 ≤ 0 ↔ v 0 ≤ 0) := by
  have hadj' := h.1
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  have hbound : (u 0 - v 0).natAbs ≤ 1 := by omega
  constructor
  · intro hu
    by_contra hv
    
    have hu0 : u 0 = 0 := by omega
    have hv1 : v 0 = 1 := by omega
    exact des_cutConfig_no_cross h hu0 hv1
  · intro hv
    by_contra hu
    have hv0 : v 0 = 0 := by omega
    have hu1 : u 0 = 1 := by omega
    exact des_cutConfig_no_cross (isOpenEdge_symm h) hv0 hu1




theorem des_cutConfig_connectedWithin_sameSide0 {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 des_cutConfig S x y) : ((x : Site 2) 0 ≤ 0 ↔ (y : Site 2) 0 ≤ 0) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact (des_cutConfig_open_sameSide0 hab).trans ih





theorem des_cutConfig_no_H (n : ℤ) (hn : 1 ≤ n) :
    ¬ HorizontalCrossing des_cutConfig 0 n 0 n := by
  rintro ⟨x, y, hxy⟩
  have hside := des_cutConfig_connectedWithin_sameSide0 hxy
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = n := y.2.2
  rw [hx0, hy0] at hside
  have : (0 : ℤ) ≤ 0 := le_refl 0
  have : (n : ℤ) ≤ 0 := hside.mp this
  omega




theorem des_negCut_open_le_one {u v : Site 2}
    (h : IsOpenEdge 2 (des_negConfig des_cutConfig) u v) : u 0 ≤ 1 ∧ v 0 ≤ 1 := by
  obtain ⟨hadj, hopen⟩ := h
  
  rw [des_negConfig_open_iff_closed] at hopen
  
  by_contra hcon
  apply absurd hopen
  rw [des_cutConfig_open_of_not_cut]
  · simp
  · rintro ⟨c, hc⟩
    
    rw [Sym2.eq_iff] at hc
    push Not at hcon
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · subst hu; subst hv; simp at hcon
    · subst hu; subst hv; simp at hcon



theorem des_negCut_connectedWithin_le_one {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (des_negConfig des_cutConfig) S x y)
    (hx : (x : Site 2) 0 ≤ 1) : (y : Site 2) 0 ≤ 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (des_negCut_open_le_one hab).2





theorem des_cutConfig_no_negH (n : ℤ) (hn : 2 ≤ n) :
    ¬ HorizontalCrossing (des_negConfig des_cutConfig) 0 n (-n) 0 := by
  rintro ⟨x, y, hxy⟩
  have hx1 : ((⟨(x : Site 2), leftSide_subset x.2⟩ : rect 0 n (-n) 0) : Site 2) 0 ≤ 1 := by
    show (x : Site 2) 0 ≤ 1; rw [x.2.2]; norm_num
  have hy1 := des_negCut_connectedWithin_le_one hxy hx1
  have : (y : Site 2) 0 ≤ 1 := hy1
  rw [y.2.2] at this
  omega












theorem des_hsepSquare_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) := by
  rw [des_hsepSquare_iff_closedH_rotbox]
  intro h
  exact des_cutConfig_no_negH n hn (h des_cutConfig (des_cutConfig_no_H n (by omega)))

end Universality

end StatMech
