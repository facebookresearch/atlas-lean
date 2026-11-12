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
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.SegmentConn
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.BoxCrossingDichotomyClose

open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality













theorem jex_leftSide_subset_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ leftSide 0 n 0 n) : x ∈ bcd_leftReach ω n :=
  ⟨leftSide_subset hx, x, hx, leftSide_subset hx,
    connectedWithin_refl ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩⟩




theorem jex_rightSide_notin_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {y : Site 2} (hy : y ∈ rightSide 0 n 0 n) :
    y ∉ bcd_leftReach ω n :=
  (bcd_no_horizontal_iff_right_unreachable ω n).mp hnoH y hy









theorem jex_leftReach_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (bcd_leftReach ω n)
    (jex_leftSide_subset_leftReach ω n hx) (jex_rightSide_notin_leftReach ω n hnoH hy)






theorem jex_escape_crossCount_odd (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n)
    (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount (bcd_leftReach ω n) w) :=
  crossCount_odd_of_separated (bcd_leftReach ω n)
    (jex_leftSide_subset_leftReach ω n hx) (jex_rightSide_notin_leftReach ω n hnoH hy) w





theorem jex_barrier_edge_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q) (hbd : bdEdge (bcd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    ω s(p, q) = false := by
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈ bcd_leftReach ω n
  · exact bcd_leftReach_boundary_closed ω n hp hqbox hadj (hbd.mp hp)
  · have hq : q ∈ bcd_leftReach ω n := by
      by_contra hqn; exact hp (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    exact bcd_leftReach_boundary_closed ω n hq hpbox hadj.symm hp





theorem jex_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q) (hbd : bdEdge (bcd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact jex_barrier_edge_closed ω n hadj hbd hpbox hqbox












theorem jex_leftReach_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (bcd_leftReach ω n).Finite :=
  bcd_leftReach_finite ω n




theorem jex_lattice_walk_row (c : ℤ) (m : ℕ) :
    (hypercubicLattice 2).Reachable (![0, c]) (![(m : ℤ), c]) := by
  have h := segment_connectedWithin (d := 2) (Set.univ) (0 : Fin 2) (![0, c]) m
    (fun t _ => Set.mem_univ _)
  have h2 : (hypercubicLattice 2).Reachable
      (Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (0 : ℤ)))
      (Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (m : ℤ))) := by
    obtain ⟨w⟩ := h
    exact ⟨w.map (Embedding.induce Set.univ).toHom⟩
  have e0 : Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (0 : ℤ)) = ![0, c] := by
    funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (m : ℤ))
      = ![(m : ℤ), c] := by
    funext i; fin_cases i <;> simp [Function.update]
  rw [e0, em] at h2; exact h2





theorem jex_edgeBoundary_nonempty (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {c : ℤ} (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    (edgeBoundary 2 (bcd_leftReach ω n)).Nonempty := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hxL : (![0, c] : Site 2) ∈ leftSide 0 (m : ℤ) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    refine ⟨by simp, ?_, by simpa using hc0, by simpa using hcn⟩
    simp only [Matrix.cons_val_zero]; exact hn
  have hyR : (![(m : ℤ), c] : Site 2) ∈ rightSide 0 (m : ℤ) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    refine ⟨?_, by simp, by simpa using hc0, by simpa using hcn⟩
    simp only [Matrix.cons_val_zero]; exact hn
  obtain ⟨w⟩ := jex_lattice_walk_row c m
  exact edgeBoundary_nonempty_of_walk (bcd_leftReach ω (m : ℤ)) w
    (jex_leftSide_subset_leftReach ω (m : ℤ) hxL)
    (jex_rightSide_notin_leftReach ω (m : ℤ) hnoH hyR)












theorem jex_exists_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {c : ℤ} (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle := by
  obtain ⟨⟨a, b⟩, hab⟩ := jex_edgeBoundary_nonempty ω hn hnoH hc0 hcn
  exact exists_dualCircuit_of_finite_of_edgeBoundary (bcd_leftReach ω n)
    (jex_leftReach_finite ω n) hab







theorem jex_dualCircuit_edge_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f g : Site 2} (hadj : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    {p q : Site 2} (hpq : sharedPrimalEdge f g = s(p, q))
    (hpadj : (hypercubicLattice 2).Adj p q)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true := by
  have hbd : bdEdge (bcd_leftReach ω n) (sharedPrimalEdge f g) :=
    faceBoundaryGraph_sharedPrimalEdge_bdEdge _ hadj
  rw [hpq] at hbd
  exact jex_barrier_dual_open ω n hpadj hbd hpbox hqbox




















def jex_DualBarrierVCrossing (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  DualVerticalCrossing ω 0 n 0 n








theorem jex_native_dualVerticalCrossing_of_barrier (ω : ConfigSpace (Sym2 (Site 2)))
    (n : ℤ) (h : jex_DualBarrierVCrossing ω n) :
    DualVerticalCrossing ω 0 n 0 n :=
  h







theorem jex_exhaustivity_of_barrier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : jex_DualBarrierVCrossing ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n :=
  Or.inr (jex_native_dualVerticalCrossing_of_barrier ω n h)













theorem jex_barrier_vcrossing_nonvacuous :
    jex_DualBarrierVCrossing bcc_botCfg 2 :=
  bcc_dualVert_botCfg







theorem jex_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall




theorem jex_wall_separates {x y : Site 2}
    (hx : x ∈ leftSide 0 2 0 2) (hy : y ∈ rightSide 0 2 0 2) :
    ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y :=
  jex_leftReach_separates bcc_wallCfg 2 bcc_noH_wall hx hy





theorem jex_wall_dualCircuit :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2)).Walk u u),
      cyc.IsCycle :=
  jex_exists_dualCircuit bcc_wallCfg (by norm_num) bcc_noH_wall (c := 0) (by norm_num)
    (by norm_num)

end Universality

end StatMech
