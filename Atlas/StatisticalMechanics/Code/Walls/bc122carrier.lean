/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Walls.bc121trifcount

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









open Classical in




def bc122_StarOfArms (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site d → (↑S : Type)),
    G.IsAcyclic ∧
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        G.Adj (ιU y) t₁ ∧ G.Adj (ιU y) t₂ ∧ G.Adj (ιU y) t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃) ∧
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v)












theorem bc122_carrier_closes (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc122_StarOfArms ω L R) : bc69_Gn_globalForest ω L R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hGac, harmAdj, hinj, hFmin⟩ := h
  refine bc121_globalForest_of_peel2 ω L R G hGac ιU ?_ hinj hFmin
  intro y hybox htri
  obtain ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, ha₁, ha₂, ha₃, hc₁₂, hc₁₃, hc₂₃⟩ := harmAdj y hybox htri
  exact ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃,
    ha₁.ne, ha₂.ne, ha₃.ne,
    ha₁.reachable, ha₂.reachable, ha₃.reachable, hc₁₂, hc₁₃, hc₂₃⟩



theorem bc122_count_via_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc122_StarOfArms ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R (bc122_carrier_closes ω L R h)


















def bc122_HubBoundaryArms (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) : Prop :=
  
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧
  
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ∀ j k, arm y j = arm z k → y = z ∧ j = k) ∧
  
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ∀ j, arm y j ≠ z)









open Classical in

noncomputable def bc122_hubs (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => bc67_IsGnTrifurcation ω L y)

theorem bc122_mem_hubs {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y : Site d} :
    y ∈ bc122_hubs ω L R ↔ y ∈ box d R ∧ bc67_IsGnTrifurcation ω L y := by
  classical
  unfold bc122_hubs
  rw [Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]


noncomputable def bc122_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) : Finset (Site d) := by
  classical
  exact (bc122_hubs ω L R) ∪
    (bc122_hubs ω L R).biUnion (fun y => (Finset.univ : Finset (Fin 3)).image (fun j => arm y j))

theorem bc122_hub_mem_carrier {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {y : Site d} (hy : y ∈ bc122_hubs ω L R) :
    y ∈ bc122_carrier ω L R arm := by
  classical
  unfold bc122_carrier; exact Finset.mem_union_left _ hy

theorem bc122_tip_mem_carrier {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {y : Site d} (hy : y ∈ bc122_hubs ω L R) (j : Fin 3) :
    arm y j ∈ bc122_carrier ω L R arm := by
  classical
  unfold bc122_carrier
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨y, hy, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩



def bc122_starRel (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d) :
    Site d → Site d → Prop :=
  fun u v => ∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3,
    (u = y ∧ v = arm y j) ∨ (v = y ∧ u = arm y j)


noncomputable def bc122_starGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) :
    SimpleGraph (↑(bc122_carrier ω L R arm) : Type) :=
  SimpleGraph.fromRel (fun u v => bc122_starRel ω L R arm (u : Site d) (v : Site d))





theorem bc122_starRel_tip_forces_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3} {w : Site d}
    (h : bc122_starRel ω L R arm (arm y j) w ∨ bc122_starRel ω L R arm w (arm y j)) :
    w = y := by
  obtain ⟨_, hdistinct, hnohub⟩ := hHBA
  obtain ⟨hybox, hytri⟩ := bc122_mem_hubs.mp hy
  
  have key : ∀ z ∈ bc122_hubs ω L R, ∀ k : Fin 3,
      (arm y j = z ∧ w = arm z k) ∨ (w = z ∧ arm y j = arm z k) → w = y := by
    intro z hz k hcase
    obtain ⟨hzbox, hztri⟩ := bc122_mem_hubs.mp hz
    rcases hcase with ⟨heq, _⟩ | ⟨hwz, hleafeq⟩
    · 
      exact absurd heq (hnohub y hybox hytri z hzbox hztri j)
    · 
      obtain ⟨hyz, _⟩ := hdistinct y hybox hytri z hzbox hztri j k hleafeq
      rw [hwz, hyz]
  rcases h with ⟨z, hz, k, hor⟩ | ⟨z, hz, k, hor⟩
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key z hz k (Or.inl ⟨h1, h2⟩)
    · exact key z hz k (Or.inr ⟨h1, h2⟩)
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key z hz k (Or.inr ⟨h1, h2⟩)
    · exact key z hz k (Or.inl ⟨h1, h2⟩)


theorem bc122_starGraph_tip_adj_forces_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    {lv w' : ↑(bc122_carrier ω L R arm)} (hlv : (lv : Site d) = arm y j)
    (hadj : (bc122_starGraph ω L R arm).Adj lv w') : (w' : Site d) = y := by
  rw [bc122_starGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨hne, hrel⟩ := hadj
  rw [hlv] at hrel
  exact bc122_starRel_tip_forces_hub hHBA hy hrel


theorem bc122_tip_isolated_in_cut {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    (hub lv : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = arm y j) (w' : ↑(bc122_carrier ω L R arm)) :
    ¬ ((bc122_starGraph ω L R arm).deleteIncidenceSet hub).Adj lv w' := by
  intro hadj
  rw [deleteIncidenceSet_adj] at hadj
  obtain ⟨hstar, hlvne, hw'ne⟩ := hadj
  have : (w' : Site d) = y := bc122_starGraph_tip_adj_forces_hub hHBA hy hlv hstar
  exact hw'ne (Subtype.ext (by rw [this, hhub]))


theorem bc122_tips_not_reachable_in_cut {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j k : Fin 3}
    (hub lv₁ lv₂ : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv₁ : (lv₁ : Site d) = arm y j) (hlv₂ : (lv₂ : Site d) = arm y k)
    (hne : lv₁ ≠ lv₂) :
    ¬ ((bc122_starGraph ω L R arm).deleteIncidenceSet hub).Reachable lv₁ lv₂ := by
  intro hreach
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => exact hne rfl
  | @cons _ c _ hadj q =>
    exact bc122_tip_isolated_in_cut hHBA hy hub lv₁ hhub hlv₁ c hadj


theorem bc122_starGraph_hub_adj_tip {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d}
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    (hub lv : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = arm y j)
    (hne : hub ≠ lv) :
    (bc122_starGraph ω L R arm).Adj hub lv := by
  rw [bc122_starGraph, SimpleGraph.fromRel_adj]
  refine ⟨hne, Or.inl ?_⟩
  rw [hhub, hlv]
  exact ⟨y, hy, j, Or.inl ⟨rfl, rfl⟩⟩









theorem bc122_starGraph_adj_tip_form {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d}
    {a b : ↑(bc122_carrier ω L R arm)} (hab : (bc122_starGraph ω L R arm).Adj a b) :
    (∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3, (a : Site d) = arm y j ∧ (b : Site d) = y) ∨
    (∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3, (b : Site d) = arm y j ∧ (a : Site d) = y) := by
  rw [bc122_starGraph, SimpleGraph.fromRel_adj] at hab
  obtain ⟨hne, hrel⟩ := hab
  rcases hrel with ⟨y, hy, j, hor⟩ | ⟨y, hy, j, hor⟩
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨y, hy, j, h2, h1⟩
    · exact Or.inl ⟨y, hy, j, h2, h1⟩
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨y, hy, j, h2, h1⟩
    · exact Or.inr ⟨y, hy, j, h2, h1⟩




theorem bc122_tip_isolated_after_edge_delete {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    (hub lv : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = arm y j) (w' : ↑(bc122_carrier ω L R arm)) :
    ¬ ((bc122_starGraph ω L R arm).deleteEdges {s(hub, lv)}).Adj lv w' := by
  intro hadj
  rw [SimpleGraph.deleteEdges_adj] at hadj
  obtain ⟨hstar, hnotdel⟩ := hadj
  
  have hw'y : (w' : Site d) = y := bc122_starGraph_tip_adj_forces_hub hHBA hy hlv hstar
  have hw'hub : w' = hub := Subtype.ext (by rw [hw'y, hhub])
  apply hnotdel
  rw [hw'hub, Set.mem_singleton_iff, Sym2.eq_swap]



theorem bc122_starGraph_edge_isBridge {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {a b : ↑(bc122_carrier ω L R arm)} (hab : (bc122_starGraph ω L R arm).Adj a b) :
    (bc122_starGraph ω L R arm).IsBridge s(a, b) := by
  rw [SimpleGraph.isBridge_iff]
  refine ⟨hab, ?_⟩
  intro hreach
  
  rcases bc122_starGraph_adj_tip_form hab with ⟨y, hy, j, haT, hbH⟩ | ⟨y, hy, j, hbT, haH⟩
  · 
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact hab.ne rfl
    | @cons _ c _ hadj q =>
      
      have hadj' : ((bc122_starGraph ω L R arm).deleteEdges {s(b, a)}).Adj a c := by
        rw [Sym2.eq_swap]; exact hadj
      exact bc122_tip_isolated_after_edge_delete hHBA hy b a hbH haT c hadj'
  · 
    obtain ⟨p⟩ := hreach
    
    have hreach' : ((bc122_starGraph ω L R arm).deleteEdges {s(a, b)}).Reachable b a := ⟨p.reverse⟩
    obtain ⟨q⟩ := hreach'
    cases q with
    | nil => exact hab.ne rfl
    | @cons _ c _ hadj r =>
      exact bc122_tip_isolated_after_edge_delete hHBA hy a b haH hbT c hadj


theorem bc122_starGraph_acyclic {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm) :
    (bc122_starGraph ω L R arm).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  exact bc122_starGraph_edge_isBridge hHBA hab

















open Classical in


noncomputable def bc122_ιU (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) (base : ↑(bc122_carrier ω L R arm)) :
    Site d → ↑(bc122_carrier ω L R arm) :=
  fun z => if hz : z ∈ bc122_carrier ω L R arm then ⟨z, hz⟩ else base

theorem bc122_ιU_carrier {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {base : ↑(bc122_carrier ω L R arm)}
    {z : Site d} (hz : z ∈ bc122_carrier ω L R arm) :
    (bc122_ιU ω L R arm base z : Site d) = z := by
  rw [bc122_ιU]; simp only [hz, dif_pos]

theorem bc122_ιU_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {base : ↑(bc122_carrier ω L R arm)}
    {z : Site d} (hz : z ∈ bc122_hubs ω L R) :
    (bc122_ιU ω L R arm base z : Site d) = z :=
  bc122_ιU_carrier (bc122_hub_mem_carrier hz)

open Classical in







theorem bc122_boundaryStar_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    (base : ↑(bc122_carrier ω L R arm))
    (hFmin : ∀ (F : SimpleGraph (↑(bc122_carrier ω L R arm) : Type)) [DecidableRel F.Adj],
      F ≤ bc122_starGraph ω L R arm → F.IsAcyclic →
      (∀ v : (↑(bc122_carrier ω L R arm) : Type), F.degree v = 1 →
        bc121_Protected ω L R (bc122_ιU ω L R arm base) v) →
      (∀ a b : (↑(bc122_carrier ω L R arm) : Type),
        bc121_Protected ω L R (bc122_ιU ω L R arm base) a →
        bc121_Protected ω L R (bc122_ιU ω L R arm base) b →
        (bc122_starGraph ω L R arm).Reachable a b → F.Reachable a b) →
      ∀ v : (↑(bc122_carrier ω L R arm) : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R := by
  classical
  obtain ⟨hbtip, hdistinct, hnohub⟩ := hHBA
  haveI hSne : Nonempty (↑(bc122_carrier ω L R arm) : Type) := ⟨base⟩
  set G : SimpleGraph (↑(bc122_carrier ω L R arm) : Type) := bc122_starGraph ω L R arm with hG
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  set ιU : Site d → (↑(bc122_carrier ω L R arm) : Type) := bc122_ιU ω L R arm base with hιU
  refine bc121_globalForest_of_peel2 ω L R G
    (bc122_starGraph_acyclic ⟨hbtip, hdistinct, hnohub⟩) ιU ?_ ?_ hFmin
  · 
    intro z hzbox hztri
    have hzhub : z ∈ bc122_hubs ω L R := bc122_mem_hubs.mpr ⟨hzbox, hztri⟩
    have hιUz : (ιU z : Site d) = z := bc122_ιU_hub hzhub
    have htc : ∀ j : Fin 3, arm z j ∈ bc122_carrier ω L R arm :=
      fun j => bc122_tip_mem_carrier hzhub j
    set t : Fin 3 → (↑(bc122_carrier ω L R arm) : Type) := fun j => ⟨arm z j, htc j⟩ with ht
    have hts : ∀ j, (t j : Site d) = arm z j := fun j => rfl
    have htne : ∀ j k : Fin 3, j ≠ k → t j ≠ t k := by
      intro j k hjk h
      have : arm z j = arm z k := congrArg Subtype.val h
      obtain ⟨_, hjkeq⟩ := hdistinct z hzbox hztri z hzbox hztri j k this
      exact hjk hjkeq
    have htP : ∀ j, bc121_Protected ω L R ιU (t j) := by
      intro j; exact Or.inl (by rw [hts j]; exact hbtip z hzbox hztri j)
    have hne : ∀ j, ιU z ≠ t j := by
      intro j h
      have hsite : (ιU z : Site d) = arm z j := by rw [h, hts j]
      have : z = arm z j := hιUz.symm.trans hsite
      exact hnohub z hzbox hztri z hzbox hztri j this.symm
    have hadj : ∀ j, G.Adj (ιU z) (t j) := by
      intro j
      exact bc122_starGraph_hub_adj_tip hzhub (ιU z) (t j) hιUz (hts j) (hne j)
    have hcut : ∀ j k : Fin 3, j ≠ k →
        ¬ (G.deleteIncidenceSet (ιU z)).Reachable (t j) (t k) := by
      intro j k hjk
      exact bc122_tips_not_reachable_in_cut ⟨hbtip, hdistinct, hnohub⟩ hzhub (ιU z) (t j) (t k)
        hιUz (hts j) (hts k) (htne j k hjk)
    exact ⟨t 0, t 1, t 2, htP 0, htP 1, htP 2, hne 0, hne 1, hne 2,
      (hadj 0).reachable, (hadj 1).reachable, (hadj 2).reachable,
      hcut 0 1 (by decide), hcut 0 2 (by decide), hcut 1 2 (by decide)⟩
  · 
    intro z hzbox hztri z' hz'box hz'tri hUeq
    have hzhub : z ∈ bc122_hubs ω L R := bc122_mem_hubs.mpr ⟨hzbox, hztri⟩
    have hz'hub : z' ∈ bc122_hubs ω L R := bc122_mem_hubs.mpr ⟨hz'box, hz'tri⟩
    have : (ιU z : Site d) = (ιU z' : Site d) := by rw [hUeq]
    rw [bc122_ιU_hub hzhub, bc122_ιU_hub hz'hub] at this
    exact this















theorem bc122_arm_boundary_reach (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z :=
  bc101_arm_reaches_boundary ω L R hR y a habox hinf




theorem bc122_hubBoundaryArms_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc122_HubBoundaryArms ω L R (fun _ _ => (0 : Site d)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro y hybox htri; exact absurd htri (hno y hybox)








































theorem bc122_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc122_StarOfArms ω L R → bc69_Gn_globalForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d),
      bc122_HubBoundaryArms ω L R arm → (bc122_starGraph ω L R arm).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc122_StarOfArms ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc122_carrier_closes ω L R h
  · intro ω L R arm h; exact bc122_starGraph_acyclic h
  · intro ω L R hR y a habox hinf; exact bc122_arm_boundary_reach ω L R hR y a habox hinf
  · intro ω L R h; exact bc122_count_via_carrier ω L R h

end StatMech.Walls
