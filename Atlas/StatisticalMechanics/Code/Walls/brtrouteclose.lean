/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Walls.bararmray
import Code.Walls.bc60upperlines

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}










theorem brt_reachable_of_avoidWalk (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (z : Site d) {u v : Site d}
    (p : (openSubgraph d ω).Walk u v)
    (hp : ∀ w ∈ p.support, w ∉ bc61_boxAround d L z) :
    (bc67_contractedLattice ω L z).Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj q ih =>
    have ha : a ∉ bc61_boxAround d L z := hp a (by simp [SimpleGraph.Walk.support_cons])
    have hb : b ∉ bc61_boxAround d L z := hp b (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
    have hstep : (bc67_contractedLattice ω L z).Adj a b :=
      bgc_adj_of_openAdj_avoiding ω L z a b hadj ha hb
    have hrest : (bc67_contractedLattice ω L z).Reachable b c :=
      ih (fun w hw => hp w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw))
    exact hstep.reachable.trans hrest




theorem brt_adj_transfer (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x z a b : Site d)
    (h : (bc67_contractedLattice ω L x).Adj a b)
    (ha : a ∉ bc61_boxAround d L z) (hb : b ∉ bc61_boxAround d L z) :
    (bc67_contractedLattice ω L z).Adj a b :=
  bgc_adj_of_openAdj_avoiding ω L z a b (bc67_contractedLattice_le ω L x h) ha hb



theorem brt_ray_reach (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x z : Site d) (r : ℕ → Site d)
    (hadj : ∀ k, (bc67_contractedLattice ω L x).Adj (r k) (r (k + 1)))
    (havoid : ∀ k, r k ∉ bc61_boxAround d L z) :
    ∀ k, (bc67_contractedLattice ω L z).Reachable (r 0) (r k) := by
  intro k
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    exact ih.trans
      (brt_adj_transfer ω L x z (r n) (r (n + 1)) (hadj n) (havoid n) (havoid (n + 1))).reachable







theorem brt_boxAvoiding_reach (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x z arm : Site d)
    (hinf : (cluster d (removeSites (bc61_boxAround d L x) ω) arm).Infinite) :
    ∃ b : Site d, (bc67_contractedLattice ω L x).Reachable arm b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, r k ∉ bc61_boxAround d L z) ∧
        (∀ k, (bc67_contractedLattice ω L z).Reachable b (r k)) := by
  obtain ⟨b, hreach, r, hr0, hinj, hadj, havoid⟩ :=
    bar_boxAvoiding_armRay ω L x arm hinf (bc61_boxAround d L z)
  refine ⟨b, hreach, r, hr0, hinj, havoid, ?_⟩
  intro k
  have := brt_ray_reach ω L x z r hadj havoid k
  rwa [hr0] at this






theorem brt_hroute_step (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (aj x b ai : Site d)
    (hxb : (bc67_contractedLattice ω L aj).Reachable x b)
    (hbai : (bc67_contractedLattice ω L aj).Reachable b ai) :
    (bc67_contractedLattice ω L aj).Reachable x ai :=
  hxb.trans hbai










theorem brt_origin_no_openEdge (v : Site 2) : bc60_upperLines s((0 : Site 2), v) ≠ true := by
  intro h
  have h1 : (1 : ℤ) ≤ (0 : Site 2) 1 := (bc60_open_edge_heights h).1
  simp only [Pi.zero_apply] at h1
  exact absurd h1 (by decide)




theorem brt_contractedLattice_no_adj_origin (L : ℕ) (z v : Site 2) :
    ¬ (bc67_contractedLattice bc60_upperLines L z).Adj 0 v := by
  intro h
  have h2 := bc67_contractedLattice_le bc60_upperLines L z h
  rw [openSubgraph_adj] at h2
  exact brt_origin_no_openEdge v h2.2


theorem brt_origin_reach_eq (L : ℕ) (z w : Site 2)
    (h : (bc67_contractedLattice bc60_upperLines L z).Reachable 0 w) : w = 0 := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj q => exact absurd hadj (brt_contractedLattice_no_adj_origin L z _)






theorem brt_hroute_false_on_witness (L : ℕ) (a : Fin 3 → Site 2) (hane : ∀ i, a i ≠ 0) :
    ¬ (∀ i j, i ≠ j →
        (bc67_contractedLattice bc60_upperLines L (a j)).Reachable (0 : Site 2) (a i)) := by
  intro hroute
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  exact hane 0 (brt_origin_reach_eq L (a 1) (a 0) (hroute 0 1 h01))




theorem brt_witness_trif_but_no_route {L : ℕ} (hL : 3 ≤ L)
    (a : Fin 3 → Site 2) (hane : ∀ i, a i ≠ 0) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    ¬ (∀ i j, i ≠ j →
        (bc67_contractedLattice bc60_upperLines L (a j)).Reachable (0 : Site 2) (a i)) :=
  ⟨bc67_upperLines_is_G_n_trifurcation hL, brt_hroute_false_on_witness L a hane⟩







theorem brt_witness_tail_fires {L : ℕ} (hL : 3 ≤ L) (z : Site 2) :
    ∃ arm b : Site 2, (bc67_contractedLattice bc60_upperLines L 0).Reachable arm b ∧
      ∃ r : ℕ → Site 2, r 0 = b ∧ Function.Injective r ∧
        (∀ k, r k ∉ bc61_boxAround 2 L z) ∧
        (∀ k, (bc67_contractedLattice bc60_upperLines L z).Reachable b (r k)) := by
  obtain ⟨a1, a2, a3, _, ⟨hinf1, _, _⟩, _⟩ := bc67_upperLines_is_G_n_trifurcation hL
  obtain ⟨b, hb, hrest⟩ := brt_boxAvoiding_reach bc60_upperLines L 0 z a1 hinf1
  exact ⟨a1, b, hb, hrest⟩



























theorem brt_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x z arm : Site d),
      (cluster d (removeSites (bc61_boxAround d L x) ω) arm).Infinite →
      ∃ b : Site d, (bc67_contractedLattice ω L x).Reachable arm b ∧
        ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, r k ∉ bc61_boxAround d L z) ∧
          (∀ k, (bc67_contractedLattice ω L z).Reachable b (r k))) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (aj x b ai : Site d),
      (bc67_contractedLattice ω L aj).Reachable x b →
      (bc67_contractedLattice ω L aj).Reachable b ai →
      (bc67_contractedLattice ω L aj).Reachable x ai) ∧
    
    
    (∀ (L : ℕ), 3 ≤ L → ∀ (a : Fin 3 → Site 2), (∀ i, a i ≠ 0) →
      bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
      ¬ (∀ i j, i ≠ j →
          (bc67_contractedLattice bc60_upperLines L (a j)).Reachable (0 : Site 2) (a i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L x z arm hinf; exact brt_boxAvoiding_reach ω L x z arm hinf
  · intro ω L aj x b ai hxb hbai; exact brt_hroute_step ω L aj x b ai hxb hbai
  · intro L hL a hane; exact brt_witness_trif_but_no_route hL a hane

end StatMech.Walls
