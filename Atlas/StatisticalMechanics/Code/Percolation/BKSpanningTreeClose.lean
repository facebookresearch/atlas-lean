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
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.ForestLeafCountClose
import Code.Percolation.SingleLeafHallClose
import Code.Percolation.BoundaryPruningClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}









theorem bst_connected_has_spanningTree {V : Type*} (G : SimpleGraph V) (hG : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
  obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
  exact ⟨T, hle, hT⟩











theorem bst_treeForestData_one_cluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bpr_TreeForestData ω n)
    {x y : Site d} (hxbox : x ∈ box d n) (hxtri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y) :
    Connected d ω x y := by
  classical
  obtain ⟨W, _, _, G, _, π, ιT, br, lamL, hTree, _hWcard, hπ, _hπinj,
    hπιT, _hιinj, _hbr, _hlammap, _hlaminj⟩ := h
  
  set f : G →g (openSubgraph d ω) :=
    { toFun := π, map_rel' := fun {a b} hab => hπ a b hab } with hf
  
  have hreach : G.Reachable (ιT x) (ιT y) := hTree.connected.preconnected (ιT x) (ιT y)
  
  have hmap : (openSubgraph d ω).Reachable (π (ιT x)) (π (ιT y)) := hreach.map f
  rw [hπιT x hxbox hxtri, hπιT y hybox hytri] at hmap
  exact hmap










theorem bst_treeForestData_refutable_of_twoClusters (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y : Site d} (hxbox : x ∈ box d n) (hxtri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y)
    (hsep : ¬ Connected d ω x y) :
    ¬ bpr_TreeForestData ω n := fun h =>
  hsep (bst_treeForestData_one_cluster ω n h hxbox hxtri hybox hytri)












open Classical in

















def bst_BoxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F : SimpleGraph (↑Vset : Type))
    (_ : DecidableRel F.Adj) (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    F.IsAcyclic ∧
    (∀ v : (↑Vset : Type), 1 ≤ F.degree v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d n)







open Classical in



theorem bst_deg_ge_three_of_boxOpenForest {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ}
    {Vset : Finset (Site d)} {F : SimpleGraph (↑Vset : Type)} [DecidableRel F.Adj]
    {vx : Site d → (↑Vset : Type)} {b : Site d → Fin 3 → (↑Vset : Type)}
    (hπ : ∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
    {x : Site d} (_hxbox : x ∈ box d n) (_htri : IsTrifurcation d ω x)
    (hvx : (vx x : Site d) = x)
    (hreach : ∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x)
    (hcut : ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)) :
    3 ≤ F.degree (vx x) := by
  classical
  set p := vx x with hp
  obtain ⟨hr0, hb0⟩ := hreach 0
  obtain ⟨hr1, hb1⟩ := hreach 1
  obtain ⟨hr2, hb2⟩ := hreach 2
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  
  have hπinj : Function.Injective (fun u : (↑Vset : Type) => (u : Site d)) := Subtype.val_injective
  
  have hcutG : ∀ (u v : (↑Vset : Type)) (hup : u ≠ p) (hvp : v ≠ p),
      ¬ Connected d (removeSite x ω) (u : Site d) (v : Site d) →
      ¬ (F.induce ({p}ᶜ : Set (↑Vset : Type))).Reachable
        ⟨u, by simpa using hup⟩ ⟨v, by simpa using hvp⟩ := by
    intro u v hup hvp hc hreach2
    apply hc
    have := slh_connected_removeSite_of_G_induce (fun u : (↑Vset : Type) => (u : Site d))
      hπ hπinj hup hvp hreach2
    
    rw [show (fun u : (↑Vset : Type) => (u : Site d)) p = x from hvx] at this
    exact this
  exact slh_deg_ge_three_of_cut hr0 hr1 hr2 hb0.symm hb1.symm hb2.symm
    (hcutG _ _ hb0 hb1 hcut01)
    (hcutG _ _ hb0 hb2 hcut02)
    (hcutG _ _ hb1 hb2 hcut12)







open Classical in

theorem bst_Tcount_le_boundary_of_boxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  
  set Tf := tfc_trifFinset ω n with hTf
  
  have hdeg3 : ∀ x, x ∈ box d n → IsTrifurcation d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact bst_deg_ge_three_of_boxOpenForest hπ hxbox htri hvx hreach hcut
  
  have hvxinjOn : Set.InjOn vx Tf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    have hx' : (vx x : Site d) = x := (htriData x hx.1 hx.2).1
    have hy' : (vx y : Site d) = y := (htriData y hy.1 hy.2).1
    rw [← hx', ← hy', hxy]
  
  set Tw : Finset (↑Vset : Type) := Tf.image vx with hTw
  have hcardTw : Tw.card = Tf.card := by rw [hTw, Finset.card_image_of_injOn hvxinjOn]
  
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ F.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨x, hxT, rfl⟩ := hw
    rw [tfc_mem_trifFinset] at hxT
    exact hdeg3 x hxT.1 hxT.2
  
  have h1 : Tf.card ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := by
    rw [← hcardTw]; exact flc2_trifImage_card_le_deg3 F Tw hTwdeg
  
  have h2 : (univ.filter (fun v => 3 ≤ F.degree v)).card
      ≤ (univ.filter (fun v => F.degree v = 1)).card :=
    flc2_forest_internal_le_leaves F hacyc hmin
  
  have h3 : (univ.filter (fun v => F.degree v = 1)).card ≤ boxSV_boundaryCard d n := by
    rw [← tfc_boundaryFinset_card]
    apply Finset.card_le_card_of_injOn (fun v : (↑Vset : Type) => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, tfc_mem_boundaryFinset]
      exact hleaf v hv.2
    · intro u _ v _ huv; exact Subtype.val_injective huv
  calc Tcount d ω n = Tf.card := (tfc_trifFinset_card ω n).symm
    _ ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := h1
    _ ≤ (univ.filter (fun v => F.degree v = 1)).card := h2
    _ ≤ boxSV_boundaryCard d n := h3










open Classical in




theorem bst_boxOpenForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    bst_BoxOpenForest ω n := by
  classical
  
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set Vset : Finset (Site d) := Finset.univ.image lab with hVset
  have hmem : ∀ i : Fin 4, lab i ∈ Vset := fun i => by
    rw [hVset, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩
  
  set e : Fin 4 ≃ (↑Vset : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑Vset : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by
          rw [hVset, Finset.mem_image] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  
  let F : SimpleGraph (↑Vset : Type) := Flc2Witness.starG.map e.toEmbedding
  let hisoF : Flc2Witness.starG ≃g F := SimpleGraph.Iso.map e Flc2Witness.starG
  have hisoApp : ∀ i : Fin 4, hisoF i = e i := fun i =>
    SimpleGraph.Iso.map_apply e Flc2Witness.starG i
  
  have hFadj : ∀ u v : Fin 4, F.Adj (e u) (e v) ↔ Flc2Witness.starG.Adj u v := by
    intro u v
    have := hisoF.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  
  have hnbhd : ∀ i : Fin 4,
      F.neighborFinset (e i) = (Flc2Witness.starG.neighborFinset i).image e := by
    intro i
    ext w
    rw [mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hw
      obtain ⟨j, rfl⟩ := e.surjective w
      exact ⟨j, by rw [mem_neighborFinset]; exact (hFadj i j).mp hw, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rw [mem_neighborFinset] at hj
      exact (hFadj i j).mpr hj
  have hdeg : ∀ i : Fin 4, F.degree (e i) = Flc2Witness.starG.degree i := by
    intro i
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, hnbhd,
      Finset.card_image_of_injective _ e.injective]
  
  have hsurj : ∀ w : (↑Vset : Type), ∃ i : Fin 4, e i = w := fun w => e.surjective w
  
  set vx : Site d → (↑Vset : Type) := fun _ => e 0 with hvxdef
  set b : Site d → Fin 3 → (↑Vset : Type) := fun _ i => e i.succ with hbdef
  refine ⟨Vset, ⟨e 0⟩, F, inferInstance, vx, b, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro u v huv
    obtain ⟨iu, rfl⟩ := hsurj u
    obtain ⟨iv, rfl⟩ := hsurj v
    rw [hFadj] at huv
    
    rw [Flc2Witness.starG, fromRel_adj] at huv
    obtain ⟨hne, hor⟩ := huv
    rw [heval, heval]
    
    fin_cases iu <;> fin_cases iv <;>
      simp only [hlab] <;>
      first
        | exact hadj 0 | exact hadj 1 | exact hadj 2
        | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
        | (exfalso; revert hor; simp only [Flc2Witness.starE]; decide)
  · 
    exact (hisoF.symm.isAcyclic_iff).mpr Flc2Witness.starG_isTree.isAcyclic
  · 
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]
    fin_cases i <;> decide
  · 
    intro x' hx'box htri'
    have hxx : x' = x := hsingle x' hx'box htri'
    subst x'
    refine ⟨?_, ?_, hsep⟩
    · 
      change (e 0 : Site d) = x
      rw [heval]
    · 
      intro i
      refine ⟨?_, ?_⟩
      · 
        change F.Reachable (e 0) (e i.succ)
        refine Adj.reachable ?_
        rw [hFadj]
        rw [Flc2Witness.starG, fromRel_adj]
        exact ⟨(Fin.succ_ne_zero i).symm, Or.inl (Or.inl ⟨rfl, Fin.succ_ne_zero i⟩)⟩
      · 
        change e i.succ ≠ e 0
        intro hh
        exact Fin.succ_ne_zero i (e.injective hh)
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    fin_cases i
    · exact absurd hv (by decide)
    · rw [heval]; exact habdry 0
    · rw [heval]; exact habdry 1
    · rw [heval]; exact habdry 2

end Percolation

end StatMech
