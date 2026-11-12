/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Walls.bc121trifcount

open Finset Set SimpleGraph

namespace StatMech.FrontierA

open StatMech.Walls StatMech.Percolation



theorem finite_cutHub_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGac : G.IsAcyclic) (hubs boundary : Finset V)
    (harms : ∀ u ∈ hubs, ∃ t1 t2 t3 : V,
      t1 ∈ boundary ∧ t2 ∈ boundary ∧ t3 ∈ boundary ∧
      u ≠ t1 ∧ u ≠ t2 ∧ u ≠ t3 ∧
      G.Reachable u t1 ∧ G.Reachable u t2 ∧ G.Reachable u t3 ∧
      ¬ (G.deleteIncidenceSet u).Reachable t1 t2 ∧
      ¬ (G.deleteIncidenceSet u).Reachable t1 t3 ∧
      ¬ (G.deleteIncidenceSet u).Reachable t2 t3) :
    hubs.card ≤ boundary.card := by
  classical
  rcases hubs.eq_empty_or_nonempty with hempty | hnonempty
  · simp [hempty]
  let P : V → Prop := fun v => v ∈ boundary ∨ v ∈ hubs
  haveI : DecidablePred P := Classical.decPred _
  obtain ⟨F, hFdec, hFle, hFac, hFleafP, hFpres⟩ :=
    bc121_boundaryAnchored_subforest G P hGac
  have hdeg3 : ∀ u ∈ hubs, 3 ≤ F.degree u := by
    intro u hu
    obtain ⟨t1, t2, t3, ht1, ht2, ht3, hne1, hne2, hne3,
      hgr1, hgr2, hgr3, hcut12, hcut13, hcut23⟩ := harms u hu
    have huP : P u := Or.inr hu
    have ht1P : P t1 := Or.inl ht1
    have ht2P : P t2 := Or.inl ht2
    have ht3P : P t3 := Or.inl ht3
    have hdile : F.deleteIncidenceSet u ≤ G.deleteIncidenceSet u := by
      intro a b hab
      rw [SimpleGraph.deleteIncidenceSet_adj] at hab ⊢
      exact ⟨hFle hab.1, hab.2.1, hab.2.2⟩
    exact bc121_deg3_of_three_reached_targets F hne1 hne2 hne3
      (hFpres _ _ huP ht1P hgr1)
      (hFpres _ _ huP ht2P hgr2)
      (hFpres _ _ huP ht3P hgr3)
      (fun h => hcut12 (h.mono hdile))
      (fun h => hcut13 (h.mono hdile))
      (fun h => hcut23 (h.mono hdile))
  obtain ⟨u0, hu0⟩ := hnonempty
  have hu0support : u0 ∈ F.support := by
    rw [← F.degree_pos_iff_mem_support]
    have := hdeg3 u0 hu0
    omega
  letI : Nonempty F.support := ⟨⟨u0, hu0support⟩⟩
  let H : SimpleGraph F.support := F.induce F.support
  have hHac : H.IsAcyclic := hFac.induce _
  have hHmin : ∀ v, 1 ≤ H.degree v := by
    intro v
    rw [show H.degree v = F.degree v.1 by exact F.degree_induce_support v]
    exact (F.degree_pos_iff_mem_support v.1).mpr v.2
  let hubMap : V → F.support := fun u =>
    if hu : u ∈ hubs then
      ⟨u, (F.degree_pos_iff_mem_support u).mp (by
        have := hdeg3 u hu
        omega)⟩
    else ⟨u0, hu0support⟩
  have hubMap_val : ∀ u ∈ hubs, (hubMap u).1 = u := by
    intro u hu
    change (if hu' : u ∈ hubs then (⟨u, _⟩ : F.support)
      else ⟨u0, hu0support⟩).1 = u
    rw [dif_pos hu]
  have hHubBranch : ∀ u ∈ hubs, hubMap u ∈
      (Finset.univ.filter fun v : F.support => 3 ≤ H.degree v) := by
    intro u hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [show H.degree (hubMap u) = F.degree (hubMap u).1 by
      exact F.degree_induce_support (hubMap u), hubMap_val u hu]
    exact hdeg3 u hu
  have hHubCard : hubs.card ≤
      (Finset.univ.filter fun v : F.support => 3 ≤ H.degree v).card := by
    apply Finset.card_le_card_of_injOn hubMap hHubBranch
    intro a ha b hb hab
    rw [← hubMap_val a ha, ← hubMap_val b hb]
    exact congrArg Subtype.val hab
  have hLeafBoundary : ∀ v : F.support, H.degree v = 1 → v.1 ∈ boundary := by
    intro v hv
    have hvF : F.degree v.1 = 1 := by
      simpa [H] using hv
    rcases hFleafP v.1 hvF with hb | hhub
    · exact hb
    · exfalso
      have h3 := hdeg3 v.1 hhub
      omega
  have hLeafCard :
      (Finset.univ.filter fun v : F.support => H.degree v = 1).card ≤ boundary.card := by
    apply Finset.card_le_card_of_injOn (fun v : F.support => v.1)
    · intro v hv
      have hv' : H.degree v = 1 := by simpa using hv
      exact hLeafBoundary v hv'
    · intro a _ b _ hab
      exact Subtype.ext hab
  calc
    hubs.card ≤ (Finset.univ.filter fun v : F.support => 3 ≤ H.degree v).card := hHubCard
    _ ≤ (Finset.univ.filter fun v : F.support => H.degree v = 1).card :=
      flc2_forest_internal_le_leaves H hHac hHmin
    _ ≤ boundary.card := hLeafCard



theorem finite_cutHub_count_of_ambient
    {V : Type*} [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hubs boundary : Finset V)
    (harms : ∀ u ∈ hubs, ∃ t1 t2 t3 : V,
      t1 ∈ boundary ∧ t2 ∈ boundary ∧ t3 ∈ boundary ∧
      u ≠ t1 ∧ u ≠ t2 ∧ u ≠ t3 ∧
      A.Reachable u t1 ∧ A.Reachable u t2 ∧ A.Reachable u t3 ∧
      ¬ (A.deleteIncidenceSet u).Reachable t1 t2 ∧
      ¬ (A.deleteIncidenceSet u).Reachable t1 t3 ∧
      ¬ (A.deleteIncidenceSet u).Reachable t2 t3) :
    hubs.card ≤ boundary.card := by
  classical
  rcases hubs.eq_empty_or_nonempty with hempty | hnonempty
  · simp [hempty]
  choose t1 t2 t3 hspec using fun i : ↥hubs => harms i.1 i.2
  have ht1 : ∀ i : ↥hubs, t1 i ∈ boundary := fun i => (hspec i).1
  have ht2 : ∀ i : ↥hubs, t2 i ∈ boundary := fun i => (hspec i).2.1
  have ht3 : ∀ i : ↥hubs, t3 i ∈ boundary := fun i => (hspec i).2.2.1
  have hne1 : ∀ i : ↥hubs, i.1 ≠ t1 i := fun i => (hspec i).2.2.2.1
  have hne2 : ∀ i : ↥hubs, i.1 ≠ t2 i := fun i => (hspec i).2.2.2.2.1
  have hne3 : ∀ i : ↥hubs, i.1 ≠ t3 i := fun i => (hspec i).2.2.2.2.2.1
  have hr1 : ∀ i : ↥hubs, A.Reachable i.1 (t1 i) :=
    fun i => (hspec i).2.2.2.2.2.2.1
  have hr2 : ∀ i : ↥hubs, A.Reachable i.1 (t2 i) :=
    fun i => (hspec i).2.2.2.2.2.2.2.1
  have hr3 : ∀ i : ↥hubs, A.Reachable i.1 (t3 i) :=
    fun i => (hspec i).2.2.2.2.2.2.2.2.1
  have hc12 : ∀ i : ↥hubs, ¬ (A.deleteIncidenceSet i.1).Reachable (t1 i) (t2 i) :=
    fun i => (hspec i).2.2.2.2.2.2.2.2.2.1
  have hc13 : ∀ i : ↥hubs, ¬ (A.deleteIncidenceSet i.1).Reachable (t1 i) (t3 i) :=
    fun i => (hspec i).2.2.2.2.2.2.2.2.2.2.1
  have hc23 : ∀ i : ↥hubs, ¬ (A.deleteIncidenceSet i.1).Reachable (t2 i) (t3 i) :=
    fun i => (hspec i).2.2.2.2.2.2.2.2.2.2.2
  let p1 (i : ↥hubs) : A.Walk i.1 (t1 i) := (hr1 i).some
  let p2 (i : ↥hubs) : A.Walk i.1 (t2 i) := (hr2 i).some
  let p3 (i : ↥hubs) : A.Walk i.1 (t3 i) := (hr3 i).some
  let carrier : Finset V := Finset.univ.biUnion fun i : ↥hubs =>
    (p1 i).support.toFinset ∪ (p2 i).support.toFinset ∪ (p3 i).support.toFinset
  have hp1mem : ∀ i : ↥hubs, ∀ x ∈ (p1 i).support, x ∈ carrier := by
    intro i x hx
    change x ∈ Finset.univ.biUnion (fun i : ↥hubs =>
      (p1 i).support.toFinset ∪ (p2 i).support.toFinset ∪ (p3 i).support.toFinset)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, by simp [hx]⟩
  have hp2mem : ∀ i : ↥hubs, ∀ x ∈ (p2 i).support, x ∈ carrier := by
    intro i x hx
    change x ∈ Finset.univ.biUnion (fun i : ↥hubs =>
      (p1 i).support.toFinset ∪ (p2 i).support.toFinset ∪ (p3 i).support.toFinset)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, by simp [hx]⟩
  have hp3mem : ∀ i : ↥hubs, ∀ x ∈ (p3 i).support, x ∈ carrier := by
    intro i x hx
    change x ∈ Finset.univ.biUnion (fun i : ↥hubs =>
      (p1 i).support.toFinset ∪ (p2 i).support.toFinset ∪ (p3 i).support.toFinset)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, by simp [hx]⟩
  have hubMem : ∀ i : ↥hubs, i.1 ∈ carrier := fun i =>
    hp1mem i i.1 (p1 i).start_mem_support
  have t1Mem : ∀ i : ↥hubs, t1 i ∈ carrier := fun i =>
    hp1mem i (t1 i) (p1 i).end_mem_support
  have t2Mem : ∀ i : ↥hubs, t2 i ∈ carrier := fun i =>
    hp2mem i (t2 i) (p2 i).end_mem_support
  have t3Mem : ∀ i : ↥hubs, t3 i ∈ carrier := fun i =>
    hp3mem i (t3 i) (p3 i).end_mem_support
  let G0 : SimpleGraph (↥carrier) := A.induce (↑carrier : Set V)
  have r1 : ∀ i : ↥hubs, G0.Reachable
      ⟨i.1, hubMem i⟩ ⟨t1 i, t1Mem i⟩ := by
    intro i
    exact ⟨(p1 i).induce (↑carrier : Set V) (hp1mem i)⟩
  have r2 : ∀ i : ↥hubs, G0.Reachable
      ⟨i.1, hubMem i⟩ ⟨t2 i, t2Mem i⟩ := by
    intro i
    exact ⟨(p2 i).induce (↑carrier : Set V) (hp2mem i)⟩
  have r3 : ∀ i : ↥hubs, G0.Reachable
      ⟨i.1, hubMem i⟩ ⟨t3 i, t3Mem i⟩ := by
    intro i
    exact ⟨(p3 i).induce (↑carrier : Set V) (hp3mem i)⟩
  let T : SimpleGraph (↥carrier) := osf_spanForest G0
  haveI : DecidableRel T.Adj := Classical.decRel _
  let hubMap : ↥hubs → ↥carrier := fun i => ⟨i.1, hubMem i⟩
  let target1 : ↥hubs → ↥carrier := fun i => ⟨t1 i, t1Mem i⟩
  let target2 : ↥hubs → ↥carrier := fun i => ⟨t2 i, t2Mem i⟩
  let target3 : ↥hubs → ↥carrier := fun i => ⟨t3 i, t3Mem i⟩
  let hubSet : Finset (↥carrier) := Finset.univ.image hubMap
  let targetSet : Finset (↥carrier) :=
    (Finset.univ.image target1 ∪ Finset.univ.image target2) ∪
      Finset.univ.image target3
  have htargetBoundary : ∀ v ∈ targetSet, v.1 ∈ boundary := by
    intro v hv
    simp only [targetSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hv
    rcases hv with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
    · exact ht1 i
    · exact ht2 i
    · exact ht3 i
  have htargetCard : targetSet.card ≤ boundary.card := by
    apply Finset.card_le_card_of_injOn (fun v : ↥carrier => v.1)
    · exact htargetBoundary
    · intro a _ b _ hab
      exact Subtype.ext hab
  have hhubCard : hubs.card = hubSet.card := by
    change hubs.card = (Finset.univ.image hubMap).card
    have hinj : Function.Injective hubMap := by
      intro a b hab
      exact Subtype.ext (congrArg (fun v : ↥carrier => v.1) hab)
    rw [Finset.card_image_of_injective _ hinj]
    rw [Finset.card_univ, Fintype.card_coe]
  let cutMap : ∀ i : ↥hubs,
      T.deleteIncidenceSet (hubMap i) →g A.deleteIncidenceSet i.1 := fun i => {
      toFun := fun v => v.1
      map_rel' := by
        intro a b hab
        rw [SimpleGraph.deleteIncidenceSet_adj] at hab ⊢
        exact ⟨(osf_spanForest_le G0 hab.1),
          fun h => hab.2.1 (Subtype.ext h),
          fun h => hab.2.2 (Subtype.ext h)⟩ }
  have hcount : hubSet.card ≤ targetSet.card := by
    apply finite_cutHub_count T (osf_spanForest_acyclic G0) hubSet targetSet
    intro u hu
    change u ∈ Finset.univ.image hubMap at hu
    rw [Finset.mem_image] at hu
    obtain ⟨i, _, rfl⟩ := hu
    refine ⟨target1 i, target2 i, target3 i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [targetSet, target1]
    · simp [targetSet, target2]
    · simp [targetSet, target3]
    · intro h
      exact hne1 i (congrArg (fun v : ↥carrier => v.1) h)
    · intro h
      exact hne2 i (congrArg (fun v : ↥carrier => v.1) h)
    · intro h
      exact hne3 i (congrArg (fun v : ↥carrier => v.1) h)
    · exact osf_spanForest_reachable_of G0 (r1 i)
    · exact osf_spanForest_reachable_of G0 (r2 i)
    · exact osf_spanForest_reachable_of G0 (r3 i)
    · intro h
      have hm := h.map (cutMap i)
      have e1 : (cutMap i) (target1 i) = t1 i := by simp [cutMap, target1]
      have e2 : (cutMap i) (target2 i) = t2 i := by simp [cutMap, target2]
      rw [e1, e2] at hm
      exact hc12 i hm
    · intro h
      have hm := h.map (cutMap i)
      have e1 : (cutMap i) (target1 i) = t1 i := by simp [cutMap, target1]
      have e3 : (cutMap i) (target3 i) = t3 i := by simp [cutMap, target3]
      rw [e1, e3] at hm
      exact hc13 i hm
    · intro h
      have hm := h.map (cutMap i)
      have e2 : (cutMap i) (target2 i) = t2 i := by simp [cutMap, target2]
      have e3 : (cutMap i) (target3 i) = t3 i := by simp [cutMap, target3]
      rw [e2, e3] at hm
      exact hc23 i hm
  calc
    hubs.card = hubSet.card := hhubCard
    _ ≤ targetSet.card := hcount
    _ ≤ boundary.card := htargetCard

end StatMech.FrontierA
