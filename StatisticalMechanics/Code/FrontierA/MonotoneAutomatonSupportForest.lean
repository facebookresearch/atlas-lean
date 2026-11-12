/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Walls.bc121trifcount

open Set SimpleGraph Finset

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls

variable {d : ℕ}




theorem gnForestData_of_protected_arms
    (omega : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj]
    (hGac : G.IsAcyclic) (iotaU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      ∃ t1 t2 t3 : (↑S : Type),
        bc121_Protected omega L R iotaU t1 ∧
        bc121_Protected omega L R iotaU t2 ∧
        bc121_Protected omega L R iotaU t3 ∧
        iotaU y ≠ t1 ∧ iotaU y ≠ t2 ∧ iotaU y ≠ t3 ∧
        G.Reachable (iotaU y) t1 ∧ G.Reachable (iotaU y) t2 ∧
        G.Reachable (iotaU y) t3 ∧
        ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t2 ∧
        ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t3 ∧
        ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t2 t3)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      ∀ z, z ∈ box d R → bc67_IsGnTrifurcation omega L z →
        iotaU y = iotaU z → y = z)
    (hex : ∃ y, y ∈ box d R ∧ bc67_IsGnTrifurcation omega L y) :
    bc68_GnForestData omega L R := by
  classical
  let P : (↑S : Type) → Prop := bc121_Protected omega L R iotaU
  haveI : DecidablePred P := Classical.decPred _
  obtain ⟨F, hFdec, hFle, hFac, hFleafP, hFpres⟩ :=
    bc121_boundaryAnchored_subforest G P hGac
  have hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      3 ≤ F.degree (iotaU y) := by
    intro y hybox htri
    obtain ⟨t1, t2, t3, hp1, hp2, hp3, hne1, hne2, hne3,
      hgr1, hgr2, hgr3, hgc12, hgc13, hgc23⟩ := harm y hybox htri
    have hhubP : P (iotaU y) := Or.inr ⟨y, hybox, htri, rfl⟩
    have hfr1 : F.Reachable (iotaU y) t1 := hFpres _ _ hhubP hp1 hgr1
    have hfr2 : F.Reachable (iotaU y) t2 := hFpres _ _ hhubP hp2 hgr2
    have hfr3 : F.Reachable (iotaU y) t3 := hFpres _ _ hhubP hp3 hgr3
    have hdile : F.deleteIncidenceSet (iotaU y) ≤
        G.deleteIncidenceSet (iotaU y) := by
      intro a b hab
      rw [SimpleGraph.deleteIncidenceSet_adj] at hab ⊢
      exact ⟨hFle hab.1, hab.2.1, hab.2.2⟩
    exact bc121_deg3_of_three_reached_targets F hne1 hne2 hne3
      hfr1 hfr2 hfr3
      (fun h => hgc12 (h.mono hdile))
      (fun h => hgc13 (h.mono hdile))
      (fun h => hgc23 (h.mono hdile))
  obtain ⟨y0, hy0box, hy0tri⟩ := hex
  have hy0support : iotaU y0 ∈ F.support := by
    rw [← F.degree_pos_iff_mem_support]
    have := hdeg3 y0 hy0box hy0tri
    omega
  let base : F.support := ⟨iotaU y0, hy0support⟩
  let hub : Site d → F.support := fun y =>
    if hy : y ∈ box d R ∧ bc67_IsGnTrifurcation omega L y then
      ⟨iotaU y, (F.degree_pos_iff_mem_support (iotaU y)).mp (by
        have := hdeg3 y hy.1 hy.2
        omega)⟩
    else base
  let leaf : F.support → Site d := fun v => v.1.1
  let H : SimpleGraph F.support := F.induce F.support
  have hub_val : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      (hub y).1 = iotaU y := by
    intro y hybox htri
    change (if hy : y ∈ box d R ∧ bc67_IsGnTrifurcation omega L y then
      (⟨iotaU y, _⟩ : F.support) else base).1 = iotaU y
    rw [dif_pos ⟨hybox, htri⟩]
  have hHmin : ∀ v, 1 ≤ H.degree v := by
    intro v
    rw [show H.degree v = F.degree v.1 by
      exact F.degree_induce_support v]
    exact (F.degree_pos_iff_mem_support v.1).mpr v.2
  have hHdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      3 ≤ H.degree (hub y) := by
    intro y hybox htri
    rw [show H.degree (hub y) = F.degree (hub y).1 by
      exact F.degree_induce_support (hub y)]
    rw [hub_val y hybox htri]
    exact hdeg3 y hybox htri
  have hHubInj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      ∀ z, z ∈ box d R → bc67_IsGnTrifurcation omega L z →
        hub y = hub z → y = z := by
    intro y hybox htri z hzbox hztri hyz
    apply hinj y hybox htri z hzbox hztri
    rw [← hub_val y hybox htri, ← hub_val z hzbox hztri]
    exact congrArg (fun v : F.support => v.1) hyz
  have hLeafBoundary : ∀ v, H.degree v = 1 → leaf v ∈ vertexBoundary d R := by
    intro v hv
    have hvF : F.degree v.1 = 1 := by
      simpa [H] using hv
    rcases hFleafP v.1 hvF with hb | ⟨y, hybox, htri, hy⟩
    · exact hb
    · exfalso
      have h3 : 3 ≤ F.degree v.1 := hy ▸ hdeg3 y hybox htri
      omega
  have hLeafInj : Set.InjOn leaf
      (↑(Finset.univ.filter fun v : F.support => H.degree v = 1) : Set F.support) := by
    intro a _ b _ hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  exact ⟨F.support, inferInstance, ⟨base⟩, inferInstance,
    H, inferInstance, hub, leaf, hFac.induce _, hHmin, hHdeg3,
    hHubInj, hLeafBoundary, hLeafInj⟩




theorem coarseTcount_le_boundary_of_protected_arms
    (omega : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj]
    (hGac : G.IsAcyclic) (iotaU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      ∃ t1 t2 t3 : (↑S : Type),
        bc121_Protected omega L R iotaU t1 ∧
        bc121_Protected omega L R iotaU t2 ∧
        bc121_Protected omega L R iotaU t3 ∧
        iotaU y ≠ t1 ∧ iotaU y ≠ t2 ∧ iotaU y ≠ t3 ∧
        G.Reachable (iotaU y) t1 ∧ G.Reachable (iotaU y) t2 ∧
        G.Reachable (iotaU y) t3 ∧
        ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t2 ∧
        ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t3 ∧
        ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t2 t3)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y →
      ∀ z, z ∈ box d R → bc67_IsGnTrifurcation omega L z →
        iotaU y = iotaU z → y = z) :
    bc61_coarseTcount omega L R ≤ boxSV_boundaryCard d R := by
  classical
  by_cases hex : ∃ y, y ∈ box d R ∧ bc67_IsGnTrifurcation omega L y
  · exact bc68_coarseTcount_le_boundary_of_GnForestData omega L R
      (gnForestData_of_protected_arms omega L R G hGac iotaU harm hinj hex)
  · have hzero : bc61_coarseTcount omega L R = 0 := by
      rw [bc61_coarseTcount, Finset.card_eq_zero]
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      obtain ⟨y, hy⟩ := hnonempty
      have hymem := bc61_mem_coarseTrifFinset.mp hy
      apply hex
      exact ⟨y, hymem.1,
        (bc67_coarseTrif_is_G_n_trifurcation omega L y).mp hymem.2⟩
    rw [hzero]
    exact Nat.zero_le _

end StatMech.FrontierA
