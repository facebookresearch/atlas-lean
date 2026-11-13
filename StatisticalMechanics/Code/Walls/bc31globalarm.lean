/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.RootedForestPeelClose
import Code.Walls.bc26forest
import Code.Walls.bc29armdiv
import Code.Walls.bc30armforest

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}










theorem bc31_removeSites_isolated {T : Finset (Site d)} {t : Site d} (htT : t ∈ T)
    (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSites T ω)).Adj t y := by
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  rw [removeSites] at hopen
  rw [if_pos ⟨t, htT, by simp⟩] at hopen
  exact Bool.false_ne_true hopen





theorem bc31_walk_avoids_removeSites {T : Finset (Site d)} {a b : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} (haT : a ∉ T)
    (w : (openSubgraph d (removeSites T ω)).Walk a b) :
    ∀ z ∈ w.support, z ∉ T := by
  induction w with
  | nil =>
    intro z hz
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz; exact haT
  | @cons u v c huv w' ih =>
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact haT
    · 
      have hvT : v ∉ T := fun hv => bc31_removeSites_isolated hv ω u huv.symm
      exact ih hvT z hz














theorem bc31_edge_transfer {T : Finset (Site d)} {x : Site d}
    (ω : ConfigSpace (Sym2 (Site d))) {u v : Site d} (huT : u ∉ T) (hvT : v ∉ T)
    (h : (openSubgraph d (removeSite x ω)).Adj u v) :
    (openSubgraph d (removeSites T ω)).Adj u v := by
  rw [openSubgraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨hadj, hopen⟩ := h
  rw [removeSite] at hopen
  by_cases hx : x ∈ (s(u,v) : Sym2 (Site d))
  · rw [if_pos hx] at hopen; exact absurd hopen (by simp)
  · rw [if_neg hx] at hopen
    rw [removeSites]
    have hnoT : ¬ ∃ t ∈ T, t ∈ (s(u,v) : Sym2 (Site d)) := by
      rintro ⟨t, htT, htmem⟩
      rw [Sym2.mem_iff] at htmem
      rcases htmem with rfl | rfl
      · exact huT htT
      · exact hvT htT
    rw [if_neg hnoT]; exact hopen






theorem bc31_walk_transfer {T : Finset (Site d)} {x a b : Site d}
    (ω : ConfigSpace (Sym2 (Site d)))
    (w : (openSubgraph d (removeSite x ω)).Walk a b)
    (havoid : ∀ z ∈ w.support, z ∉ T) :
    Connected d (removeSites T ω) a b := by
  refine ⟨w.transfer (openSubgraph d (removeSites T ω)) ?_⟩
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    have hu : u ∈ w.support := w.fst_mem_support_of_mem_edges he
    have hv : v ∈ w.support := w.snd_mem_support_of_mem_edges he
    have hadj : (openSubgraph d (removeSite x ω)).Adj u v := w.adj_of_mem_edges he
    exact bc31_edge_transfer ω (havoid u hu) (havoid v hv) hadj










theorem bc31_infinite_globalCut_reaches_boundary (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) {a : Site d}
    (haT : a ∉ T) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSites T ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSites T ω)).Walk a z, ∀ v ∈ w.support, v ∉ T := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSites T ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, hr⟩ :=
    tfc_walk_crossing (openSubgraph d (removeSites T ω)) (fun v => v ∈ box d n) w habox hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSites T ω)) hbc
  refine ⟨b, tfc_boundary_cross_vertex n hn b c hb hc hblat, ?_⟩
  obtain ⟨wab⟩ := hr
  exact ⟨wab, bc31_walk_avoids_removeSites haT wab⟩



























theorem bc31_globalCut_infinite_of_escaping {T : Finset (Site d)} {x a : Site d}
    (ω : ConfigSpace (Sym2 (Site d)))
    (hesc : ∀ m : ℕ, ∃ y, y ∉ box d m ∧
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a y, ∀ z ∈ w.support, z ∉ T) :
    (cluster d (removeSites T ω) a).Infinite := by
  rw [cluster_infinite_iff]
  intro m
  obtain ⟨y, hy, w, havoid⟩ := hesc m
  exact ⟨y, hy, bc31_walk_transfer ω w havoid⟩



theorem bc31_support_connected {x a b z : Site d} (ω : ConfigSpace (Sym2 (Site d)))
    (w : (openSubgraph d (removeSite x ω)).Walk a b) (hz : z ∈ w.support) :
    Connected d (removeSite x ω) a z := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_append] at hz
  obtain ⟨q, r, rfl⟩ := hz
  exact ⟨q⟩










theorem bc31_globalCut_infinite_of_singleCut_Tfree {T : Finset (Site d)} {x a : Site d}
    (ω : ConfigSpace (Sym2 (Site d)))
    (hinf : (cluster d (removeSite x ω) a).Infinite)
    (hTfree : ∀ z, Connected d (removeSite x ω) a z → z ∉ T) :
    (cluster d (removeSites T ω) a).Infinite := by
  refine bc31_globalCut_infinite_of_escaping (x := x) ω (fun m => ?_)
  obtain ⟨y, hy, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf m
  obtain ⟨w⟩ := hyconn
  exact ⟨y, hy, w, fun z hz => hTfree z (bc31_support_connected ω w hz)⟩

























def bc31_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSite x ω) (b x)).Infinite ∧
      (∀ z, Connected d (removeSite x ω) (b x) z → z ∉ tfc_trifFinset ω n)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x))





theorem bc31_globalCutDownArmData_of_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc31_TfreeDownArmData ω n rank) :
    bc30_GlobalCutDownArmData ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  rw [bc30_globalCutDownArmData_iff_rootedDownArmForest]
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf, hbTfree⟩ := hbdata x hxbox htri
  exact ⟨hbbox, hbconn, bc31_globalCut_infinite_of_singleCut_Tfree ω hbinf hbTfree⟩




theorem bc31_bundledRootedDownArmForest_of_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc31_TfreeDownArmData ω n rank) :
    bc29_BundledRootedDownArmForest ω n :=
  bc30_bundledRootedDownArmForest_of_data ω n rank hinj
    (bc31_globalCutDownArmData_of_TfreeDownArmData ω n rank h)


theorem bc31_Tcount_le_boundary_of_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc31_TfreeDownArmData ω n rank) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc30_Tcount_le_boundary_of_data ω n hn rank hinj
    (bc31_globalCutDownArmData_of_TfreeDownArmData ω n rank h)














theorem bc31_removeSite_notConnected_self {x a : Site d} (ω : ConfigSpace (Sym2 (Site d)))
    (hax : a ≠ x) : ¬ Connected d (removeSite x ω) a x := by
  intro h
  obtain ⟨w⟩ := h
  exact arc_walk_avoids_x hax w (by simp)











theorem bc31_globalCutDownArmData_of_uniqueTrif_singleCut
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a) (hax0 : a ≠ x₀)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bc30_GlobalCutDownArmData ω n rank := by
  apply bc31_globalCutDownArmData_of_TfreeDownArmData
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    obtain rfl := huniq x hxbox htri
    refine ⟨habox, haconn, hainf, ?_⟩
    intro z hz hzT
    rw [tfc_mem_trifFinset] at hzT
    have hzx0 : z = x := huniq z hzT.1 hzT.2
    rw [hzx0] at hz
    exact bc31_removeSite_notConnected_self ω hax0 hz
  · intro x hxbox htri y hybox htriy hxy _ _
    have h1 := huniq x hxbox htri
    have h2 := huniq y hybox htriy
    exact absurd (h1.trans h2.symm) hxy





















theorem bc31_TfreeDownArmData_clauses_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx by' : Site 1),
      (∀ z, Connected 1 (removeSite y ω) by' z → z ≠ y ∧ z ≠ bx) ∧
      ¬ Connected 1 (removeSite y ω) by' bx := by
  refine ⟨rfp_ωpath, rfp_p1, rfp_p0, rfp_p2, ?_, ?_⟩
  · intro z hz
    have heq := rfp_path_conn_eq_after_p1 hz
    subst heq
    refine ⟨?_, ?_⟩
    · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p2, rfp_p1] at this
    · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p2, rfp_p0] at this
  · intro h
    have heq := rfp_path_conn_eq_after_p1 h
    have := congrFun heq ⟨0, by norm_num⟩; simp [rfp_p2, rfp_p0] at this













theorem bc31_TfreeDownArmData_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSite x₀ ω) (b x₀)).Infinite ∧
      (∀ z, Connected d (removeSite x₀ ω) (b x₀) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSite m ω) (b m)).Infinite ∧
      (∀ z, Connected d (removeSite m ω) (b m) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSite g ω) (b g)).Infinite ∧
      (∀ z, Connected d (removeSite g ω) (b g) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc31_TfreeDownArmData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  have hrankeq : (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) := by
    funext z; simp only [hdep]; split_ifs <;> rfl
  rw [show (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) from hrankeq]
  refine ⟨b, ?_, ?_⟩
  · 
    have hTfree : ∀ {a : Site d},
        (∀ z, Connected d (removeSite a ω) (b a) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g) →
        (∀ z, Connected d (removeSite a ω) (b a) z → z ∉ tfc_trifFinset ω n) := by
      intro a hne z hz hzT
      rw [tfc_mem_trifFinset] at hzT
      rcases hthree z hzT.1 hzT.2 with rfl | rfl | rfl
      · exact (hne z hz).1 rfl
      · exact (hne z hz).2.1 rfl
      · exact (hne z hz).2.2 rfl
    intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact ⟨hbx0.1, hbx0.2.1, hbx0.2.2.1, hTfree hbx0.2.2.2⟩
    · exact ⟨hbm.1, hbm.2.1, hbm.2.2.1, hTfree hbm.2.2.2⟩
    · exact ⟨hbg.1, hbg.2.1, hbg.2.2.1, hTfree hbg.2.2.2⟩
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hsxm
    · exact hsxg
    · simp only [] at hlt; rw [hdepm, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy
    · exact hsmg
    · simp only [] at hlt; rw [hdepg, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only [] at hlt; rw [hdepg, hdepm] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy



















theorem bc31_TfreeDownArmData_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSite x₀ ω) (b x₀)).Infinite ∧
      (∀ z, Connected d (removeSite x₀ ω) (b x₀) z → z ≠ x₀ ∧ ∀ i, z ≠ y i))
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (cluster d (removeSite (y i) ω) (b (y i))).Infinite ∧
      (∀ z, Connected d (removeSite (y i) ω) (b (y i)) z → z ≠ x₀ ∧ ∀ j, z ≠ y j))
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hssib : ∀ i j : Fin 3, (j : ℕ) < i →
      ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
    bc31_TfreeDownArmData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, if_pos rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, if_neg hne, dif_pos hex, hchoose]
  
  have hTfree : ∀ {a : Site d},
      (∀ z, Connected d (removeSite a ω) (b a) z → z ≠ x₀ ∧ ∀ i, z ≠ y i) →
      (∀ z, Connected d (removeSite a ω) (b a) z → z ∉ tfc_trifFinset ω n) := by
    intro a hne z hz hzT
    rw [tfc_mem_trifFinset] at hzT
    have hnez := hne z hz
    rcases hsingle z hzT.1 hzT.2 with rfl | ⟨i, rfl⟩
    · exact hnez.1 rfl
    · exact hnez.2 i rfl
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact ⟨hbx0.1, hbx0.2.1, hbx0.2.2.1, hTfree hbx0.2.2.2⟩
    · exact ⟨(hby i).1, (hby i).2.1, (hby i).2.2.1, hTfree (hby i).2.2.2⟩
  · 
    intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact hsx0 i
      · rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl 1)
          · exact h
        exact hssib i j hji

end StatMech.Walls
