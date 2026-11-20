/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.CrossingParity
import Code.RSW.Defs
import Code.Universality.HVIntersection
import Code.Universality.VSeparatesFixed
import Code.Lattice.ArcSides

open Set SimpleGraph MeasureTheory

namespace StatMech

namespace Lattice

open StatMech.RSW.Box
open StatMech.Universality






theorem tpc_overlapComp_singleton_of_closed (m m' c d : ℤ) (xB : Site 2)
    (hxB : xB ∈ rect m m' c d) (z : Site 2)
    (hz : z ∈ overlapComp (fun _ => false) m m' c d xB hxB) : z = xB := by
  obtain ⟨_hzmem, hreach⟩ := hz
  obtain ⟨w⟩ := hreach
  cases w with
  | nil => rfl
  | cons hadj _p =>
    exfalso
    simp only [openSubgraphInduce_adj, openSubgraph_adj] at hadj
    exact absurd hadj.2 (by simp)









theorem tpc_arcS_twoPathsCross_false :
    ¬ ArcS_TwoPathsCross (fun _ => false) 0 1 0 0 0 1 ![0, 1]
        (by simp [rect]) := by
  intro hcross
  have hxB : (![0, 1] : Site 2) ∈ rect 0 0 0 1 := by simp [rect]
  have hadj : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  let γ : (hypercubicLattice 2).Walk ![0, 0] ![1, 0] :=
    SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
  have hx : (![0, 0] : Site 2) ∈ rect 0 1 0 1 := by simp [rect]
  have hy : (![1, 0] : Site 2) ∈ rect 0 1 0 1 := by simp [rect]
  have hsuppeq : γ.support = [![0, 0], ![1, 0]] := by
    simp [γ, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
  have hsupp : ∀ z ∈ γ.support, z ∈ rect 0 1 0 1 := by
    intro z hz
    rw [hsuppeq] at hz
    rcases List.mem_cons.mp hz with h | h
    · subst h; simp [rect]
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp [rect]
      · exact absurd h List.not_mem_nil
  obtain ⟨z, hzs, hzP⟩ := hcross (le_refl 0) (le_refl 0) (by norm_num)
    ![0, 0] ![1, 0] hx hy (by simp) (by simp) γ hsupp
  have hzxB : z = ![0, 1] :=
    tpc_overlapComp_singleton_of_closed 0 0 0 1 ![0, 1] hxB z hzP
  subst hzxB
  rw [hsuppeq] at hzs
  rcases List.mem_cons.mp hzs with h | h
  · exact absurd (congrFun h 1) (by norm_num)
  · rcases List.mem_cons.mp h with h | h
    · exact absurd (congrFun h 1) (by norm_num)
    · exact absurd h List.not_mem_nil









theorem tpc_arcWalk_support {ω : ConfigSpace (Sym2 (Site 2))} {m m' c d : ℤ} {xB : Site 2}
    (hxB : xB ∈ rect m m' c d) {yT : Site 2} (hyT : yT ∈ rect m m' c d)
    (h : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩) :
    ∃ (V : (hypercubicLattice 2).Walk xB yT),
      ∀ z ∈ V.support, z ∈ overlapComp ω m m' c d xB hxB := by
  classical
  obtain ⟨w⟩ := h
  refine ⟨liftWalk ω (rect m m' c d) w, ?_⟩
  intro z hz
  obtain ⟨z', hz'mem, hz'eq⟩ := liftWalk_support_mem ω (rect m m' c d) w hz
  subst hz'eq
  exact ⟨z'.2, ⟨w.takeUntil z' hz'mem⟩⟩












theorem tpc_meets_of_separating_set {P S : Set (Site 2)} {x y : Site 2}
    (γ : (hypercubicLattice 2).Walk x y) (hxS : x ∈ S) (hyS : y ∉ S)
    (hbd : ∀ u v : Site 2, (hypercubicLattice 2).Adj u v → s(u, v) ∈ γ.edges →
       bdEdge S s(u, v) → u ∈ P ∨ v ∈ P) :
    ∃ z ∈ γ.support, z ∈ P := by
  classical
  
  have hodd : ¬ Even (crossCount S γ) := by
    rw [crossCount_parity]; intro h; exact hyS (h.mp hxS)
  
  have hbdedge : ∃ e ∈ γ.edges, bdEdge S e := by
    by_contra hcon
    apply hodd
    have hz : crossCount S γ = 0 := by
      rw [crossCount, List.countP_eq_zero]
      intro e he; simp only [decide_eq_true_eq]
      exact fun hb => hcon ⟨e, he, hb⟩
    rw [hz]; exact ⟨0, rfl⟩
  obtain ⟨e, hemem, hebd⟩ := hbdedge
  induction e with
  | h u v =>
    have hadj : (hypercubicLattice 2).Adj u v := γ.adj_of_mem_edges hemem
    have hu : u ∈ γ.support := γ.fst_mem_support_of_mem_edges hemem
    have hv : v ∈ γ.support := γ.snd_mem_support_of_mem_edges hemem
    rcases hbd u v hadj hemem hebd with h | h
    · exact ⟨u, hu, h⟩
    · exact ⟨v, hv, h⟩










def ArcSeparatingSet (P : Set (Site 2)) (α β c d : ℤ) : Prop :=
  ∃ S : Set (Site 2),
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = α → z ∈ S) ∧
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = β → z ∉ S) ∧
    (∀ u v : Site 2, u ∈ rect α β c d → v ∈ rect α β c d →
        (hypercubicLattice 2).Adj u v → bdEdge S s(u, v) → u ∈ P ∨ v ∈ P)








theorem tpc_two_paths_cross_of_sep {P : Set (Site 2)} {α β c d : ℤ}
    (hsep : ArcSeparatingSet P α β c d)
    {x y : Site 2} (hx : x ∈ rect α β c d) (hy : y ∈ rect α β c d)
    (hx0 : x 0 = α) (hy0 : y 0 = β)
    (γ : (hypercubicLattice 2).Walk x y)
    (hsupp : ∀ z ∈ γ.support, z ∈ rect α β c d) :
    ∃ z ∈ γ.support, z ∈ P := by
  obtain ⟨S, hSleft, hSright, hSedge⟩ := hsep
  refine tpc_meets_of_separating_set γ (hSleft x hx hx0) (hSright y hy hy0) ?_
  intro u v hadj hemem hbd
  have hu : u ∈ rect α β c d := hsupp u (γ.fst_mem_support_of_mem_edges hemem)
  have hv : v ∈ rect α β c d := hsupp v (γ.snd_mem_support_of_mem_edges hemem)
  exact hSedge u v hu hv hadj hbd









theorem tpc_arc_sides_of_sep (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hsep : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcSeparatingSet (overlapComp ω m m' c d xB hxB) α β c d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro _hαm _hmm' _hm'β xB hxB _hxBbot _yT _hyT _hcV
  obtain ⟨S, hSleft, hSright, hSedge⟩ := hsep xB hxB
  exact ⟨S, hSleft, hSright, hSedge⟩







theorem tpc_rsw_strip_glue_of_sep
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcSeparatingSet (overlapComp ω m m' c d xB hxB) a m' c d)
    (hsepR : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcSeparatingSet (overlapComp ω m m' c d xB hxB) m b c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  vsFix_rsw_strip_glue_of_arc_sides μ hpa ham hmm' hm'b
    (fun ω => tpc_arc_sides_of_sep ω (hsepL ω))
    (fun ω => tpc_arc_sides_of_sep ω (hsepR ω))

end Lattice

end StatMech
