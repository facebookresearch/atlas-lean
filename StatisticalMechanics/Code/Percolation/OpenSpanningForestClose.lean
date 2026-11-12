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
import Code.Percolation.BKSpanningTreeClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}









open Classical in

noncomputable def osf_spanForest {V : Type*} [Fintype V] (G : SimpleGraph V) : SimpleGraph V :=
  Classical.choose (exists_maximal_isAcyclic_of_le_isAcyclic (bot_le (a := G)) isAcyclic_bot)

theorem osf_spanForest_spec {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (osf_spanForest G) :=
  (Classical.choose_spec
    (exists_maximal_isAcyclic_of_le_isAcyclic (bot_le (a := G)) isAcyclic_bot)).2


theorem osf_spanForest_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (osf_spanForest G).IsAcyclic := (osf_spanForest_spec G).1.2


theorem osf_spanForest_le {V : Type*} [Fintype V] (G : SimpleGraph V) :
    osf_spanForest G ≤ G := (osf_spanForest_spec G).1.1




theorem osf_spanForest_reachable {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : (osf_spanForest G).Reachable u v := by
  classical
  by_contra hnr
  have hmax := osf_spanForest_spec G
  set T := osf_spanForest G with hT
  set T' := T ⊔ SimpleGraph.fromEdgeSet {s(u, v)} with hT'
  have huv_ne : u ≠ v := G.ne_of_adj h
  have hT'ac : T'.IsAcyclic := IsAcyclic.sup_edge_of_not_reachable hnr (osf_spanForest_acyclic G)
  have hT'le : T' ≤ G := by
    refine sup_le (osf_spanForest_le G) ?_
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    obtain ⟨hmem, hne⟩ := hab
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  have hle := hmax.2 ⟨hT'le, hT'ac⟩ le_sup_left
  have hadjT : T.Adj u v := by
    apply hle
    rw [hT']; right; rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, huv_ne⟩
  exact hnr hadjT.reachable



theorem osf_spanForest_reachable_of {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Reachable u v) : (osf_spanForest G).Reachable u v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih => exact (osf_spanForest_reachable G hab).trans ih




theorem osf_spanForest_degree_pos_of_reachable_ne {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj] {u v : V} (hv : v ≠ u)
    (h : G.Reachable u v) : 1 ≤ (osf_spanForest G).degree u := by
  classical
  have hr : (osf_spanForest G).Reachable u v := osf_spanForest_reachable_of G h
  have hex : ∃ w, (osf_spanForest G).Adj u w := by
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl hv
    | cons hadj _ => exact ⟨_, hadj⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, (osf_spanForest G).degree_pos_iff_exists_adj]
  exact hex





theorem osf_spanForest_of_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : osf_spanForest G = G := by
  have hmax := osf_spanForest_spec G
  have hle : osf_spanForest G ≤ G := (osf_spanForest_spec G).1.1
  have hge : G ≤ osf_spanForest G := hmax.2 ⟨le_refl G, hG⟩ hle
  exact le_antisymm hle hge




theorem osf_spanForest_degree_of_acyclic {V : Type*} [Fintype V] (F₀ : SimpleGraph V)
    (hac : F₀.IsAcyclic) [DecidableRel F₀.Adj] [DecidableRel (osf_spanForest F₀).Adj] (v : V) :
    (osf_spanForest F₀).degree v = F₀.degree v := by
  have heq : osf_spanForest F₀ = F₀ := osf_spanForest_of_acyclic F₀ hac
  have h1 : (osf_spanForest F₀).degree v = ((osf_spanForest F₀).neighborFinset v).card :=
    (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
  have h2 : F₀.degree v = (F₀.neighborFinset v).card :=
    (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
  rw [h1, h2, SimpleGraph.neighborFinset_def, SimpleGraph.neighborFinset_def]
  have hns : (osf_spanForest F₀).neighborSet v = F₀.neighborSet v := by rw [heq]
  rw [Set.toFinset_congr hns]






















open Classical in




def osf_PeeledBoxForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F₀ : SimpleGraph (↑Vset : Type))
    (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F₀.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    (∀ v : (↑Vset : Type), 1 ≤ (osf_spanForest F₀).degree v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F₀.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), (osf_spanForest F₀).degree v = 1 → (v : Site d) ∈ vertexBoundary d n)






theorem osf_boxOpenForest_of_peeled (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : osf_PeeledBoxForest ω n) : bst_BoxOpenForest ω n := by
  classical
  obtain ⟨Vset, hVne, F₀, vx, b, hπ0, hmin, htriData, hleaf⟩ := h
  refine ⟨Vset, hVne, osf_spanForest F₀, Classical.decRel _, vx, b, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro u v huv
    exact hπ0 u v (osf_spanForest_le F₀ huv)
  · 
    exact osf_spanForest_acyclic F₀
  · 
    exact hmin
  · 
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    refine ⟨hvx, ?_, hcut⟩
    intro i
    obtain ⟨hr, hne⟩ := hreach i
    exact ⟨osf_spanForest_reachable_of F₀ hr, hne⟩
  · 
    exact hleaf










open Classical in





theorem osf_peeledBoxForest_of_acyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (Vset : Finset (Site d)) (hVne : Nonempty (↑Vset : Type)) (F₀ : SimpleGraph (↑Vset : Type))
    [DecidableRel F₀.Adj] (hac : F₀.IsAcyclic)
    (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type))
    (hπ0 : ∀ u v, F₀.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
    (hmin : ∀ v : (↑Vset : Type), 1 ≤ F₀.degree v)
    (htriData : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F₀.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d))))
    (hleaf : ∀ v : (↑Vset : Type), F₀.degree v = 1 → (v : Site d) ∈ vertexBoundary d n) :
    osf_PeeledBoxForest ω n := by
  classical
  refine ⟨Vset, hVne, F₀, vx, b, hπ0, ?_, htriData, ?_⟩
  · intro v
    rw [osf_spanForest_degree_of_acyclic F₀ hac]
    exact hmin v
  · intro v hv
    rw [osf_spanForest_degree_of_acyclic F₀ hac] at hv
    exact hleaf v hv













open Classical in








theorem osf_peeledBoxForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    osf_PeeledBoxForest ω n := by
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
  
  let F₀ : SimpleGraph (↑Vset : Type) := Flc2Witness.starG.map e.toEmbedding
  let hisoF : Flc2Witness.starG ≃g F₀ := SimpleGraph.Iso.map e Flc2Witness.starG
  have hisoApp : ∀ i : Fin 4, hisoF i = e i := fun i =>
    SimpleGraph.Iso.map_apply e Flc2Witness.starG i
  have hF₀adj : ∀ u v : Fin 4, F₀.Adj (e u) (e v) ↔ Flc2Witness.starG.Adj u v := by
    intro u v
    have := hisoF.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  have hF₀ac : F₀.IsAcyclic := (hisoF.symm.isAcyclic_iff).mpr Flc2Witness.starG_isTree.isAcyclic
  have hsurj : ∀ w : (↑Vset : Type), ∃ i : Fin 4, e i = w := fun w => e.surjective w
  have hF₀dec : DecidableRel F₀.Adj := Classical.decRel _
  
  have hdeg : ∀ i : Fin 4, F₀.degree (e i) = Flc2Witness.starG.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : F₀.neighborFinset (e i) = (Flc2Witness.starG.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hF₀adj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj
        exact (hF₀adj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  refine osf_peeledBoxForest_of_acyclic ω n Vset ⟨e 0⟩ F₀ hF₀ac
    (fun _ => e 0) (fun _ i => e i.succ) ?_ ?_ ?_ ?_
  · 
    intro u v huv
    obtain ⟨iu, rfl⟩ := hsurj u
    obtain ⟨iv, rfl⟩ := hsurj v
    rw [hF₀adj] at huv
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
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]
    fin_cases i <;> decide
  · 
    intro x' hx'box htri'
    have hxx : x' = x := hsingle x' hx'box htri'
    subst x'
    refine ⟨?_, ?_, hsep⟩
    · change (e 0 : Site d) = x; rw [heval]
    · intro i
      refine ⟨?_, ?_⟩
      · 
        change F₀.Reachable (e 0) (e i.succ)
        refine Adj.reachable ?_
        rw [hF₀adj, Flc2Witness.starG, fromRel_adj]
        exact ⟨(Fin.succ_ne_zero i).symm, Or.inl (Or.inl ⟨rfl, Fin.succ_ne_zero i⟩)⟩
      · change e i.succ ≠ e 0
        intro hh; exact Fin.succ_ne_zero i (e.injective hh)
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    fin_cases i
    · exact absurd hv (by decide)
    · rw [heval]; exact habdry 0
    · rw [heval]; exact habdry 1
    · rw [heval]; exact habdry 2


















theorem osf_singleTree_refutable_forest_survives (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y : Site d} (hxbox : x ∈ box d n) (hxtri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y) (hsep : ¬ Connected d ω x y) :
    ¬ bpr_TreeForestData ω n :=
  bst_treeForestData_refutable_of_twoClusters ω n hxbox hxtri hybox hytri hsep











namespace OsfDoubleStar



def jdsAdj (a b : Fin 8) : Bool :=
  match a, b with
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 2, 0 | 3, 0 => true
  | 4, 5 | 4, 6 | 4, 7 | 5, 4 | 6, 4 | 7, 4 => true
  | 0, 4 | 4, 0 => true
  | _, _ => false


def jdsG : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun a b => jdsAdj a b = true)
instance : DecidableRel jdsG.Adj := by unfold jdsG fromRel; intro a b; simp only; infer_instance


theorem jdsG_isTree : jdsG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide



def dsAdj (a b : Fin 8) : Bool :=
  match a, b with
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 2, 0 | 3, 0 => true
  | 4, 5 | 4, 6 | 4, 7 | 5, 4 | 6, 4 | 7, 4 => true
  | _, _ => false


def dsG : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun a b => dsAdj a b = true)
instance : DecidableRel dsG.Adj := by unfold dsG fromRel; intro a b; simp only; infer_instance


theorem dsG_le_jdsG : dsG ≤ jdsG := by
  intro a b hab; revert hab; fin_cases a <;> fin_cases b <;> decide


theorem dsG_acyclic : dsG.IsAcyclic := IsAcyclic.anti dsG_le_jdsG jdsG_isTree.isAcyclic


theorem dsG_hub0_deg : dsG.degree 0 = 3 := by decide
theorem dsG_hub4_deg : dsG.degree 4 = 3 := by decide

theorem dsG_deg_pos (v : Fin 8) : 1 ≤ dsG.degree v := by fin_cases v <;> decide

end OsfDoubleStar

open Classical in











theorem osf_peeledBoxForest_twoStar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x x' : Site d} (a a' : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x ∨ y = x')
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (hadj' : ∀ i, (openSubgraph d ω).Adj x' (a' i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n) (habdry' : ∀ i, a' i ∈ vertexBoundary d n)
    (hxsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
             ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
             ¬ Connected d (removeSite x ω) (a 1) (a 2))
    (hx'sep : ¬ Connected d (removeSite x' ω) (a' 0) (a' 1) ∧
              ¬ Connected d (removeSite x' ω) (a' 0) (a' 2) ∧
              ¬ Connected d (removeSite x' ω) (a' 1) (a' 2))
    (lab : Fin 8 → Site d)
    (hlab : lab 0 = x ∧ lab 1 = a 0 ∧ lab 2 = a 1 ∧ lab 3 = a 2 ∧
            lab 4 = x' ∧ lab 5 = a' 0 ∧ lab 6 = a' 1 ∧ lab 7 = a' 2)
    (hlabinj : Function.Injective lab) :
    osf_PeeledBoxForest ω n := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hlab
  set Vset : Finset (Site d) := Finset.univ.image lab with hVset
  have hmem : ∀ i : Fin 8, lab i ∈ Vset := fun i => by
    rw [hVset, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩
  set e : Fin 8 ≃ (↑Vset : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑Vset : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by
          rw [hVset, Finset.mem_image] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  
  let F₀ : SimpleGraph (↑Vset : Type) := OsfDoubleStar.dsG.map e.toEmbedding
  let hisoF : OsfDoubleStar.dsG ≃g F₀ := SimpleGraph.Iso.map e OsfDoubleStar.dsG
  have hisoApp : ∀ i : Fin 8, hisoF i = e i := fun i =>
    SimpleGraph.Iso.map_apply e OsfDoubleStar.dsG i
  have hF₀adj : ∀ u v : Fin 8, F₀.Adj (e u) (e v) ↔ OsfDoubleStar.dsG.Adj u v := by
    intro u v
    have := hisoF.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  have hF₀ac : F₀.IsAcyclic := (hisoF.symm.isAcyclic_iff).mpr OsfDoubleStar.dsG_acyclic
  have hsurj : ∀ w : (↑Vset : Type), ∃ i : Fin 8, e i = w := fun w => e.surjective w
  
  have hdeg : ∀ i : Fin 8, F₀.degree (e i) = OsfDoubleStar.dsG.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : F₀.neighborFinset (e i) = (OsfDoubleStar.dsG.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hF₀adj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj
        exact (hF₀adj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  
  set lf0 : Fin 3 → Fin 8 := fun i => match i with | 0 => 1 | 1 => 2 | 2 => 3 with hlf0
  set lf4 : Fin 3 → Fin 8 := fun i => match i with | 0 => 5 | 1 => 6 | 2 => 7 with hlf4
  
  set vx : Site d → (↑Vset : Type) := fun y => if y = x then e 0 else e 4 with hvxdef
  set b : Site d → Fin 3 → (↑Vset : Type) :=
    fun y i => if y = x then e (lf0 i) else e (lf4 i) with hbdef
  refine osf_peeledBoxForest_of_acyclic ω n Vset ⟨e 0⟩ F₀ hF₀ac vx b ?_ ?_ ?_ ?_
  · 
    intro u v huv
    obtain ⟨iu, rfl⟩ := hsurj u
    obtain ⟨iv, rfl⟩ := hsurj v
    rw [hF₀adj, OsfDoubleStar.dsG, fromRel_adj] at huv
    obtain ⟨hne, hor⟩ := huv
    rw [heval, heval]
    fin_cases iu <;> fin_cases iv <;>
      first
        | (simp only [Fin.isValue, Fin.reduceFinMk, h0, h1, h2, h3, h4, h5, h6, h7]
           first
            | exact hadj 0 | exact hadj 1 | exact hadj 2
            | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
            | exact hadj' 0 | exact hadj' 1 | exact hadj' 2
            | exact (hadj' 0).symm | exact (hadj' 1).symm | exact (hadj' 2).symm)
        | (simp only [OsfDoubleStar.dsAdj, reduceCtorEq, or_self] at hor)
  · 
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]; exact OsfDoubleStar.dsG_deg_pos i
  · 
    intro y hybox htri
    have hxe0 : (vx x : Site d) = x := by
      simp only [hvxdef, if_pos rfl]; rw [heval, h0]
    
    have hbvalx : ∀ i : Fin 3, (b x i : Site d) = a i := by
      intro i; simp only [hbdef, if_pos rfl]; rw [heval]
      fin_cases i <;> simp only [hlf0, Fin.isValue, Fin.reduceFinMk, h1, h2, h3]
    rcases hsingle y hybox htri with hyx | hyx
    · 
      subst hyx
      refine ⟨hxe0, ?_, ?_⟩
      · intro i
        refine ⟨?_, ?_⟩
        · 
          simp only [hvxdef, hbdef, if_pos rfl]
          refine Adj.reachable ?_
          rw [hF₀adj]
          fin_cases i <;> simp only [hlf0] <;> decide
        · simp only [hvxdef, hbdef, if_pos rfl]
          intro hh
          exact absurd (e.injective hh) (by fin_cases i <;> simp only [hlf0] <;> decide)
      · rw [hbvalx 0, hbvalx 1, hbvalx 2]; exact hxsep
    · 
      subst hyx
      by_cases hxx' : y = x
      · 
        subst hxx'
        refine ⟨hxe0, ?_, ?_⟩
        · intro i
          refine ⟨?_, ?_⟩
          · simp only [hvxdef, hbdef, if_pos rfl]
            refine Adj.reachable ?_
            rw [hF₀adj]; fin_cases i <;> simp only [hlf0] <;> decide
          · simp only [hvxdef, hbdef, if_pos rfl]
            intro hh
            exact absurd (e.injective hh) (by fin_cases i <;> simp only [hlf0] <;> decide)
        · rw [hbvalx 0, hbvalx 1, hbvalx 2]; exact hxsep
      · 
        have hbvalx' : ∀ i : Fin 3, (b y i : Site d) = a' i := by
          intro i; simp only [hbdef, if_neg hxx']; rw [heval]
          fin_cases i <;> simp only [hlf4, Fin.isValue, Fin.reduceFinMk, h5, h6, h7]
        refine ⟨?_, ?_, ?_⟩
        · simp only [hvxdef, if_neg hxx']; rw [heval, h4]
        · intro i
          refine ⟨?_, ?_⟩
          · simp only [hvxdef, hbdef, if_neg hxx']
            refine Adj.reachable ?_
            rw [hF₀adj]; fin_cases i <;> simp only [hlf4] <;> decide
          · simp only [hvxdef, hbdef, if_neg hxx']
            intro hh
            exact absurd (e.injective hh) (by fin_cases i <;> simp only [hlf4] <;> decide)
        · rw [hbvalx' 0, hbvalx' 1, hbvalx' 2]; exact hx'sep
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    rw [heval]
    fin_cases i <;>
      simp only [Fin.isValue, Fin.reduceFinMk, h0, h1, h2, h3, h4, h5, h6, h7] <;>
      first
        | (exact absurd hv (by decide))
        | exact habdry 0 | exact habdry 1 | exact habdry 2
        | exact habdry' 0 | exact habdry' 1 | exact habdry' 2

end Percolation

end StatMech
