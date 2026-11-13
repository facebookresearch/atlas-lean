/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality









def bcar_cfg : ConfigSpace (Sym2 (Site 2)) := fun e =>
  e = s(![1,0],![2,0]) || e = s(![1,1],![2,1])


theorem bcar_site_eq_x0 {a : Site 2} (ha0 : a 0 = 0) : a = ![0, a 1] := by
  funext i; fin_cases i
  · simpa using ha0
  · simp










theorem bcar_open_no_x0 {a b : Site 2} (hopen : bcar_cfg s(a, b) = true) :
    a 0 ≠ 0 ∧ b 0 ≠ 0 := by
  unfold bcar_cfg at hopen
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, Sym2.eq_iff, Sym2.eq_iff] at hopen
  rcases hopen with (⟨e1, e2⟩ | ⟨e1, e2⟩) | (⟨e1, e2⟩ | ⟨e1, e2⟩) <;>
    subst e1 <;> subst e2 <;> exact ⟨by decide, by decide⟩



theorem bcar_open_keeps_x0 {a b : Site 2} (hopen : bcar_cfg s(a, b) = true) :
    (a 0 = 0 ↔ b 0 = 0) := by
  obtain ⟨ha, hb⟩ := bcar_open_no_x0 hopen
  constructor
  · intro h; exact absurd h ha
  · intro h; exact absurd h hb


theorem bcar_walk_keeps_x0 {x y : (rect 0 2 0 1 : Set (Site 2))}
    (w : (openSubgraphInduce 2 bcar_cfg (rect 0 2 0 1)).Walk x y) :
    ((x : Site 2) 0 = 0 ↔ (y : Site 2) 0 = 0) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact (bcar_open_keeps_x0 hab.2).trans ih




theorem bcar_noH : ¬ HorizontalCrossing bcar_cfg 0 2 0 1 := by
  rintro ⟨x, y, hxy⟩
  have hinv := bcar_walk_keeps_x0 (x := ⟨(x:Site 2), leftSide_subset x.2⟩)
    (y := ⟨(y:Site 2), rightSide_subset y.2⟩) hxy.some
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = 2 := y.2.2
  rw [hy0] at hinv
  have : (2:ℤ) = 0 := hinv.mp hx0
  norm_num at this











theorem bcar_crossEdge_symm_mk (x y : Site 2) :
    crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
  simp [crossEdge, sym2Congr]




theorem bcar_topRung_dualClosed {p q : Site 2} (hp1 : p 1 = 1) (hq1 : q 1 = 2)
    (hpq0 : p 0 = q 0) (hx : p 0 = -1 ∨ p 0 = 0) :
    dualConfig bcar_cfg s(p, q) = false := by
  
  have hpe : p = ![p 0, 1] := by funext i; fin_cases i <;> simp [hp1]
  have hqe : q = ![p 0, 2] := by funext i; fin_cases i <;> simp [hpq0.symm, hq1]
  rw [show dualConfig bcar_cfg s(p, q) = !(bcar_cfg (crossEdge.symm s(p, q))) from rfl,
    bcar_crossEdge_symm_mk, hpe, hqe, rot90Inv_apply, rot90Inv_apply, Bool.not_eq_false']
  
  
  rcases hx with hx | hx <;> rw [hx]
  · show bcar_cfg s(![1, -(-1)], ![2, -(-1)]) = true
    norm_num [bcar_cfg]
  · show bcar_cfg s(![1, -(0:ℤ)], ![2, -(0:ℤ)]) = true
    norm_num [bcar_cfg]





theorem bcar_dualOpen_keeps_snd_le {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q)
    (hp : p ∈ rect (-1) 0 0 2) (hq : q ∈ rect (-1) 0 0 2)
    (hopen : dualConfig bcar_cfg s(p, q) = true) (hple : p 1 ≤ 1) : q 1 ≤ 1 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [mem_rect] at hp hq
  by_contra hqgt
  push Not at hqgt
  
  have hq2 : q 1 = 2 := by omega
  have hp1 : p 1 = 1 := by omega
  have hpq0 : p 0 = q 0 := by omega
  have hx : p 0 = -1 ∨ p 0 = 0 := by omega
  rw [bcar_topRung_dualClosed hp1 hq2 hpq0 hx] at hopen
  exact absurd hopen (by decide)



theorem bcar_dualVwalk_keeps_snd {x y : (rect (-1) 0 0 2 : Set (Site 2))}
    (w : (openSubgraphInduce 2 (dualConfig bcar_cfg) (rect (-1) 0 0 2)).Walk x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  induction w with
  | nil => exact hx
  | @cons a b c hab p ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (bcar_dualOpen_keeps_snd_le hab.1 a.2 b.2 hab.2 hx)




theorem bcar_noV : ¬ DualVerticalCrossing bcar_cfg (-1) 0 0 2 := by
  rintro ⟨x, y, hxy⟩
  have hx1 : (x : Site 2) 1 = 0 := x.2.2
  have hy1 : (y : Site 2) 1 = 2 := y.2.2
  have hinv := bcar_dualVwalk_keeps_snd (x := ⟨(x:Site 2), bottomSide_subset x.2⟩)
    (y := ⟨(y:Site 2), topSide_subset y.2⟩) hxy.some (by rw [hx1]; norm_num)
  rw [hy1] at hinv
  norm_num at hinv






theorem bcar_noH_noV :
    ¬ HorizontalCrossing bcar_cfg 0 2 0 1 ∧ ¬ DualVerticalCrossing bcar_cfg (-1) 0 0 2 :=
  ⟨bcar_noH, bcar_noV⟩















theorem bcar_asymm_dichotomy_false :
    ¬ ((horizontalCrossingEvent 0 2 0 1)ᶜ ⊆ dualVerticalCrossingEvent (-1) 0 0 2) := by
  intro hsub
  have hmem : bcar_cfg ∈ (horizontalCrossingEvent 0 2 0 1)ᶜ := by
    rw [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact bcar_noH
  have hdv : bcar_cfg ∈ dualVerticalCrossingEvent (-1) 0 0 2 := hsub hmem
  rw [mem_dualVerticalCrossingEvent] at hdv
  exact bcar_noV hdv

end Universality

end StatMech
