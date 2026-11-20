/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching










open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankThreeDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem randomCurrent_sources_singleton_of_ends_eq
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι → Sym2 W) (c : ι) {x y : W} (hxy : x ≠ y)
    (hc : ends c = s(x, y)) :
    StatMech.Sharpness.RandomCurrent.sources ends {c} = {x, y} := by
  ext v
  rw [StatMech.Sharpness.RandomCurrent.mem_sources]
  simp only [StatMech.Sharpness.RandomCurrent.degK,
    Finset.filter_singleton, Finset.mem_insert, Finset.mem_singleton]
  by_cases hvc : v ∈ ends c
  · rw [if_pos hvc, Finset.card_singleton]
    rw [hc] at hvc
    simp only [Sym2.mem_iff] at hvc
    exact ⟨fun _ => by tauto, fun _ => ⟨0, rfl⟩⟩
  · rw [if_neg hvc, Finset.card_empty]
    rw [hc] at hvc
    simp only [Sym2.mem_iff, not_or] at hvc
    exact ⟨fun h => absurd h (by decide), by
      rintro (rfl | rfl) <;> tauto⟩



theorem lpReplicaProfileCopyEquivCommonSlot_eq_inl_of_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
    ∃ x, lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c =
      Sum.inl x := by
  classical
  let d := lpReplicaProfileCopyEquivOrbitCoord G sites m c
  let e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites) := ⟨c.1, hfixed⟩
  have hdFst : d.1 = Sum.inl e := by
    dsimp only [d]
    rw [lpReplicaProfileCopyEquivOrbitCoord_fst]
    apply (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm.injective
    simp [e]
  change ∃ x, lpReplicaOrbitProfileCoordEquivCommonSlot
      G sites q m hm L d = Sum.inl x
  rcases d with ⟨de, dk⟩
  dsimp only at hdFst
  subst de
  rw [lpReplicaOrbitProfileCoordEquivCommonSlot_fixed]
  exact ⟨_, rfl⟩



theorem lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflect G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c}) s = s := by
  classical
  obtain ⟨x, hx⟩ := lpReplicaProfileCopyEquivCommonSlot_eq_inl_of_fixed
    G sites q m hm L c hfixed
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    change s.allocation e ∆
        lpReplicaOrbitFourColorSelectedStrictSlots G sites q
          (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c}) e =
      s.allocation e
    have hempty : lpReplicaOrbitFourColorSelectedStrictSlots G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c}) e = ∅ := by
      ext k
      simp [lpReplicaOrbitFourColorSelectedStrictSlots,
        lpReplicaOrbitCommonSlotsOfCopies, hx]
      intro h
      have heq := Finset.mem_singleton.mp h
      cases heq
    rw [hempty]
    ext k
    simp [Finset.mem_symmDiff]
  · rfl


theorem lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
    (G : SimpleGraph V) (sites : I -> V) (i : I)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hc : c.1.1 = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i)) :
    c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites := by
  rw [mem_lpReplicaCurrentEdgeOrbitFixed]
  apply Subtype.ext
  rw [lpReplicaCurrentEdgeReflect_val, hc]
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentReflect_left, lpReplicaCurrentReflect_right]

theorem card_lpReplicaMatchingSeamSource
    (sites : I -> V) (i : I) :
    (lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i).card = 2 := by
  have h : ({lpReplicaCurrentLeft sites i} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites i} =
      {lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  unfold lpMatchingSeamSource
  rw [h]
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]

theorem card_lpReplicaMatchingSeamSymmDiffGhost
    (sites : I -> V) (i : I) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).card = 4 := by
  have hs : ({lpReplicaCurrentLeft sites i} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites i} =
      {lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hg : ({(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)} :
      Finset (LPReplicaCurrentVertex V)) ∆ {lpReplicaCurrentGhost1} =
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  unfold lpMatchingSeamSource lpMatchingGhostSource
  rw [hs, hg, Finset.symmDiff_eq_union]
  · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]



theorem lpReplicaOrientedFourColorSlotState_cast_boundary
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    lpReplicaOrientedFourColorSlotState G sites A E q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A E q
          (cast (congrArg
            (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x)) =
      lpReplicaOrientedFourColorSlotState G sites A D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A D q x) := by
  subst E
  rfl

theorem lpReplicaOffdiagDecoratedTargetBranchedSlotState_right_eq_left
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
      (Sum.inr y)).2 =
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
      (Sum.inl y)).2 := rfl

theorem lpReplicaCurrentGraph_adj_ghost0_iff
    (G : SimpleGraph V) (sites : I -> V) (x : LPReplicaCurrentVertex V) :
    (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) x ↔
      ∃ v : V, x = .inl (.inl v) := by
  rcases x with (x | b)
  · rcases x with x | x <;>
      simp [lpReplicaCurrentGraph, SimpleGraph.fromRel_adj,
        lpReplicaCurrentRel, lpReplicaCurrentGhost0]
  · cases b <;>
      simp [lpReplicaCurrentGraph, SimpleGraph.fromRel_adj,
        lpReplicaCurrentRel, lpReplicaCurrentGhost0]

theorem lpReplicaCurrentGraph_adj_ghost1_iff
    (G : SimpleGraph V) (sites : I -> V) (x : LPReplicaCurrentVertex V) :
    (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) x ↔
      ∃ v : V, x = .inl (.inr v) := by
  rcases x with (x | b)
  · rcases x with x | x <;>
      simp [lpReplicaCurrentGraph, SimpleGraph.fromRel_adj,
        lpReplicaCurrentRel, lpReplicaCurrentGhost1]
  · cases b <;>
      simp [lpReplicaCurrentGraph, SimpleGraph.fromRel_adj,
        lpReplicaCurrentRel, lpReplicaCurrentGhost1]


theorem lpReplicaCurrentEdge_eq_ghost0_left_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (e : Sym2 (LPReplicaCurrentVertex V))
    (he : e ∈ (lpReplicaCurrentGraph G sites).edgeFinset)
    (hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ e) :
    ∃ v : V, e = s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
      (.inl (.inl v) : LPReplicaCurrentVertex V)) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : (lpReplicaCurrentGraph G sites).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact SimpleGraph.mem_edgeFinset.mp he
      simp only [Sym2.mem_iff] at hghost
      rcases hghost with ha | hb
      · subst a
        obtain ⟨v, hv⟩ :=
          (lpReplicaCurrentGraph_adj_ghost0_iff G sites b).mp hab
        subst b
        exact ⟨v, rfl⟩
      · subst b
        obtain ⟨v, hv⟩ :=
          (lpReplicaCurrentGraph_adj_ghost0_iff G sites a).mp hab.symm
        subst a
        exact ⟨v, Sym2.eq_swap⟩


theorem lpReplicaCurrentEdge_eq_ghost1_right_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (e : Sym2 (LPReplicaCurrentVertex V))
    (he : e ∈ (lpReplicaCurrentGraph G sites).edgeFinset)
    (hghost : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ e) :
    ∃ v : V, e = s((lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V),
      (.inl (.inr v) : LPReplicaCurrentVertex V)) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : (lpReplicaCurrentGraph G sites).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact SimpleGraph.mem_edgeFinset.mp he
      simp only [Sym2.mem_iff] at hghost
      rcases hghost with ha | hb
      · subst a
        obtain ⟨v, hv⟩ :=
          (lpReplicaCurrentGraph_adj_ghost1_iff G sites b).mp hab
        subst b
        exact ⟨v, rfl⟩
      · subst b
        obtain ⟨v, hv⟩ :=
          (lpReplicaCurrentGraph_adj_ghost1_iff G sites a).mp hab.symm
        subst a
        exact ⟨v, Sym2.eq_swap⟩

theorem sym2_eq_mk_of_mem_of_mem_of_ne
    {W : Type*} {e : Sym2 W} {x y : W}
    (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y) : e = s(x, y) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim



theorem lpReplicaOffdiagDecoratedSource_rank_three_endpointSupport
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let E := StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) z.1.1.1
    (Finset.univ.biUnion fun c => (E c).toFinset) =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  let support : Finset (LPReplicaCurrentVertex V) :=
    Finset.univ.biUnion fun c => (E c).toFinset
  have hall := lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies
    G sites hsite hij q hcard z
  dsimp only at hall
  have hsources : StatMech.Sharpness.RandomCurrent.sources E Finset.univ =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    rw [← hall.1]
    exact d.2.2.2.2.1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 3 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 3 := hcard
  have hsupportCard : support.card <= 6 := by
    calc
      support.card <= ∑ c ∈ (Finset.univ : Finset
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1)),
          (E c).toFinset.card := Finset.card_biUnion_le
      _ <= ∑ _c ∈ (Finset.univ : Finset
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1)), 2 := by
        apply Finset.sum_le_sum
        intro c _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 6 := by simp [hcopyCard]
  have hsubset :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 ⊆ support := by
    rw [← hsources]
    exact randomCurrent_sources_subset_endpointSupport E Finset.univ
  have hoffdiagCard := card_lpReplica_offdiagSource sites hsite hij
  have heq :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 = support := by
    apply Finset.eq_of_subset_of_card_le hsubset
    omega
  exact heq.symm


theorem lpReplicaOffdiagDecoratedSource_rank_three_endpoints_disjoint
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1) (hcd : c ≠ d) :
    Disjoint
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1 c).toFinset
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1 d).toFinset := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  let support : Finset (LPReplicaCurrentVertex V) :=
    Finset.univ.biUnion fun c => (E c).toFinset
  let Incidence := Σ c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1,
    {x : LPReplicaCurrentVertex V // x ∈ (E c).toFinset}
  let endpoint : Incidence -> {x // x ∈ support} := fun p =>
    ⟨p.2.1, Finset.mem_biUnion.mpr
      ⟨p.1, Finset.mem_univ _, p.2.2⟩⟩
  have hsupport :=
    lpReplicaOffdiagDecoratedSource_rank_three_endpointSupport
      G sites hsite hij q hcard z
  have hsupport' : support =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    simpa only [support, E] using hsupport
  have hsupportCard : support.card = 6 := by
    rw [hsupport']
    exact card_lpReplica_offdiagSource sites hsite hij
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 3 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 3 := hcard
  have hincidenceCard : Fintype.card Incidence = 6 := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc
      _ = ∑ _c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1, 2 := by
        apply Finset.sum_congr rfl
        intro e _
        exact Sym2.card_toFinset_of_not_isDiag _
          (StatMech.Sharpness.FluxEdgeCopy.endsM_not_isDiag
            (lpReplicaCurrentGraph G sites) z.1.1.1 e)
      _ = 6 := by simp [hcopyCard]
  have hendpointSurj : Function.Surjective endpoint := by
    intro x
    obtain ⟨c, _, hxc⟩ := Finset.mem_biUnion.mp x.2
    refine ⟨⟨c, ⟨x.1, hxc⟩⟩, ?_⟩
    exact Subtype.ext rfl
  have hendpointCard : Fintype.card Incidence =
      Fintype.card {x // x ∈ support} := by
    rw [hincidenceCard, Fintype.card_coe, hsupportCard]
  have hendpointInj : Function.Injective endpoint :=
    ((Fintype.bijective_iff_surjective_and_card endpoint).mpr
      ⟨hendpointSurj, hendpointCard⟩).1
  rw [Finset.disjoint_left]
  intro x hxc hxd
  have hinc : (⟨c, ⟨x, hxc⟩⟩ : Incidence) = ⟨d, ⟨x, hxd⟩⟩ := by
    apply hendpointInj
    exact Subtype.ext rfl
  exact hcd (congrArg Sigma.fst hinc)



theorem lpReplicaOffdiagDecoratedSource_rank_three_exists_seamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
    ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites j := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  let B :=
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
  have hsupport :=
    lpReplicaOffdiagDecoratedSource_rank_three_endpointSupport
      G sites hsite hij q hcard z
  have hsupport' : Finset.univ.biUnion (fun c => (E c).toFinset) = B := by
    simpa only [E, B] using hsupport
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hex (x : LPReplicaCurrentVertex V) (hx : x ∈ B) :
      ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
        x ∈ E c := by
    have hx' : x ∈ Finset.univ.biUnion fun c => (E c).toFinset := by
      rw [hsupport']
      exact hx
    obtain ⟨c, _, hxc⟩ := Finset.mem_biUnion.mp hx'
    exact ⟨c, Sym2.mem_toFinset.mp hxc⟩
  have hg0B : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ B := by
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  have hg1B : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ B := by
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  obtain ⟨c0, hc0ghost⟩ := hex _ hg0B
  obtain ⟨c1, hc1ghost⟩ := hex _ hg1B
  obtain ⟨x0, hc0edge⟩ := lpReplicaCurrentEdge_eq_ghost0_left_of_mem
    G sites c0.1.1 c0.1.2 hc0ghost
  obtain ⟨x1, hc1edge⟩ := lpReplicaCurrentEdge_eq_ghost1_right_of_mem
    G sites c1.1.1 c1.1.2 hc1ghost
  have hx0B : (.inl (.inl x0) : LPReplicaCurrentVertex V) ∈ B := by
    rw [← hsupport']
    apply Finset.mem_biUnion.mpr
    exact ⟨c0, Finset.mem_univ _, Sym2.mem_toFinset.mpr (by
      have h : (.inl (.inl x0) : LPReplicaCurrentVertex V) ∈ c0.1.1 := by
        rw [hc0edge]
        simp
      simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using h)⟩
  have hx1B : (.inl (.inr x1) : LPReplicaCurrentVertex V) ∈ B := by
    rw [← hsupport']
    apply Finset.mem_biUnion.mpr
    exact ⟨c1, Finset.mem_univ _, Sym2.mem_toFinset.mpr (by
      have h : (.inl (.inr x1) : LPReplicaCurrentVertex V) ∈ c1.1.1 := by
        rw [hc1edge]
        simp
      simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using h)⟩
  have hx0 : x0 = sites i ∨ x0 = sites j := by
    have h := hx0B
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff, hsij, hsij.symm] at h
    exact h.imp And.left And.left
  have hx1 : x1 = sites i ∨ x1 = sites j := by
    have h := hx1B
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff, hsij, hsij.symm] at h
    exact h.imp And.left And.left
  have hc01 : c0 ≠ c1 := by
    intro h
    subst c1
    change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ c0.1.1 at hc1ghost
    rw [hc0edge] at hc1ghost
    simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] at hc1ghost
  have ne_c0_of_mem {a : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1}
      {v : LPReplicaCurrentVertex V} (ha : v ∈ E a)
      (hv : v ∉ c0.1.1) : a ≠ c0 := by
    intro h
    subst a
    exact hv ha
  have ne_c1_of_mem {a : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1}
      {v : LPReplicaCurrentVertex V} (ha : v ∈ E a)
      (hv : v ∉ c1.1.1) : a ≠ c1 := by
    intro h
    subst a
    exact hv ha
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 3 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 3 := hcard
  have third_eq {a b : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1}
      (ha0 : a ≠ c0) (ha1 : a ≠ c1)
      (hb0 : b ≠ c0) (hb1 : b ≠ c1) : a = b := by
    by_contra hab
    have hfour : ({c0, c1, a, b} : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1)).card = 4 := by
      simp [hc01, ha0, ha1, hb0, hb1, hab,
        Ne.symm hc01, Ne.symm ha0, Ne.symm ha1,
        Ne.symm hb0, Ne.symm hb1, Ne.symm hab]
    have hle := Finset.card_le_card
      (Finset.subset_univ ({c0, c1, a, b} : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1)))
    rw [hfour, Finset.card_univ, hcopyCard] at hle
    omega
  rcases hx0 with rfl | rfl <;> rcases hx1 with rfl | rfl
  · right
    have hLjB : lpReplicaCurrentLeft sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRjB : lpReplicaCurrentRight sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, ha⟩ := hex _ hLjB
    obtain ⟨b, hb⟩ := hex _ hRjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq ha0 ha1 hb0 hb1
    subst b
    exact ⟨a, sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])⟩
  · exfalso
    have hRiB : lpReplicaCurrentRight sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hLjB : lpReplicaCurrentLeft sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, ha⟩ := hex _ hRiB
    obtain ⟨b, hb⟩ := hex _ hLjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq ha0 ha1 hb0 hb1
    subst b
    have hedge : a.1.1 = s(lpReplicaCurrentRight sites i,
        lpReplicaCurrentLeft sites j) :=
      sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])
    have hadj : (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentLeft sites j) (lpReplicaCurrentRight sites i) := by
      rw [← SimpleGraph.mem_edgeSet]
      have hm := SimpleGraph.mem_edgeFinset.mp a.1.2
      rw [hedge] at hm
      simpa only [Sym2.eq_swap] using hm
    obtain ⟨k, hkj, hki⟩ :=
      (lpReplicaCurrentGraph_adj_left_right_iff
        G sites (sites j) (sites i)).mp hadj
    exact hsij (hki.symm.trans hkj)
  · exfalso
    have hLiB : lpReplicaCurrentLeft sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRjB : lpReplicaCurrentRight sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, ha⟩ := hex _ hLiB
    obtain ⟨b, hb⟩ := hex _ hRjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq ha0 ha1 hb0 hb1
    subst b
    have hedge : a.1.1 = s(lpReplicaCurrentLeft sites i,
        lpReplicaCurrentRight sites j) :=
      sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])
    have hadj : (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites j) := by
      rw [← SimpleGraph.mem_edgeSet]
      have hm := SimpleGraph.mem_edgeFinset.mp a.1.2
      rwa [hedge] at hm
    obtain ⟨k, hki, hkj⟩ :=
      (lpReplicaCurrentGraph_adj_left_right_iff
        G sites (sites i) (sites j)).mp hadj
    exact hsij (hki.symm.trans hkj)
  · left
    have hLiB : lpReplicaCurrentLeft sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRiB : lpReplicaCurrentRight sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, ha⟩ := hex _ hLiB
    obtain ⟨b, hb⟩ := hex _ hRiB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq ha0 ha1 hb0 hb1
    subst b
    exact ⟨a, sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])⟩


theorem lpReplicaOffdiagDecoratedSource_rank_three_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      Finset.univ := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hall := lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies
    G sites hsite hij q hcard z
  dsimp only at hall
  ext x
  simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
    Finset.mem_univ, true_and]
  let c := (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2).symm x
  have hc : d.1 c = (true, false) := hall.2 c
  have hc' :
      lpReplicaOrientedFourColorTag G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q
          (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q z) c =
        (true, false) := by
    simpa only [d, lpReplicaDecoratedSourceRowGateData,
      lpReplicaOrientedFourColorTag,
      lpReplicaDecoratedOrbitAtomEquivOrientedFourColor] using hc
  simpa only [lpReplicaOffdiagDecoratedSourceSlotState,
    lpReplicaOrientedFourColorSlotState,
    lpReplicaOrbitFourColorSlotStateOfTag, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, iff_true] using congrArg Prod.fst hc'



theorem lpReplicaOffdiagDecoratedSource_rank_three_swapped_all_false
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
    ∀ c, d.1 c = (false, false) := by
  dsimp only
  intro c
  have hall := (lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies
    G sites hsite hij q hcard z).2 c
  simpa only [lpReplicaDecoratedSourceSwappedRowGateData,
    lpReplicaSwapRowsTag, hall, Bool.not_true]



theorem lpReplicaOffdiagDecoratedSource_rank_three_orientedTag
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B :=
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
      G sites ∅ B q z
    ∀ c, lpReplicaOrientedFourColorTag G sites ∅ B q oz c =
      (true, false) := by
  dsimp only
  intro c
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hc := (lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies
    G sites hsite hij q hcard z).2 c
  simpa only [d, lpReplicaDecoratedSourceRowGateData,
    lpReplicaOrientedFourColorTag,
    lpReplicaDecoratedOrbitAtomEquivOrientedFourColor] using hc



theorem lpReplicaOrientedFourColorAtom_rank_three_all_falseCurrent
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (hA : A.card = 2)
    (hB : (B.map lpReplicaCurrentReflect.toEmbedding).card = 4)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    ∀ c, (lpReplicaOrientedFourColorTag G sites A B q z c).2 = false := by
  classical
  let m := z.1.1
  let tag := lpReplicaOrientedFourColorTag G sites A B q z
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaCurrentCopies G sites m tag false false
  let K1 := lpReplicaCurrentCopies G sites m tag true false
  have hgate : LPReplicaRowGate G sites m A
      (B.map lpReplicaCurrentReflect.toEmbedding) tag :=
    (lpReplicaRowGate_iff_leftPattern_tagFourColor G sites m A
      (B.map lpReplicaCurrentReflect.toEmbedding) tag).mpr
      (lpReplicaOrientedFourColorTag_leftPattern G sites A B q z)
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m) = 3 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q m z.1.2
            z.2.2.1.2)
      _ = 3 := hcard
  have hK0source : StatMech.Sharpness.RandomCurrent.sources E K0 = A :=
    hgate.1
  have hK1source : StatMech.Sharpness.RandomCurrent.sources E K1 =
      B.map lpReplicaCurrentReflect.toEmbedding := hgate.2.2.2.1
  have hK0lower : 1 ≤ K0.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K0
    rw [hK0source, hA] at hbound
    omega
  have hK1lower : 2 ≤ K1.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K1
    rw [hK1source, hB] at hbound
    omega
  have hdisj : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [K0, K1, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc0 hc1
    have hrow : false = true :=
      (congrArg Prod.fst hc0).symm.trans (congrArg Prod.fst hc1)
    exact Bool.false_ne_true hrow
  have hunionLe : (K0 ∪ K1).card ≤ 3 := by
    calc
      (K0 ∪ K1).card ≤ Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) m) := Finset.card_le_univ _
      _ = 3 := hcopyCard
  have hunionCard : (K0 ∪ K1).card = 3 := by
    have hsumLe : K0.card + K1.card ≤ 3 := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact hunionLe
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have huniv : K0 ∪ K1 = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcopyCard, hunionCard]
  intro c
  have hc : c ∈ K0 ∪ K1 := by rw [huniv]; simp
  simp only [Finset.mem_union, K0, K1, lpReplicaCurrentCopies,
    Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases hc with hc | hc
  · exact congrArg Prod.snd hc
  · exact congrArg Prod.snd hc



theorem lpReplicaBalancedSelector_rank_three_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) s.profile)
    (sourceTag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
    (hbase : ∀ a, s.tag a = (false, false))
    (hsource : ∀ a, sourceTag a = (true, false))
    (hselector : s.selector = Finset.univ \ {c})
    (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites)
    (hSiCard : Si.card = 2)
    (hDCard : (Sj ∆ T).card = 4) :
    lpReplicaOrientedFourColorSlotState G sites Si
        ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
          ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
          (lpReplicaDecoratedOrbitAtomOfBalancedSelector
            G sites Si Sj T q s)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c})
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag) := by
  classical
  let moved := lpReplicaToggleRows G sites s.profile s.selector s.tag
  let atom := lpReplicaDecoratedOrbitAtomOfBalancedSelector
    G sites Si Sj T q s
  let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q atom
  let targetTag := lpReplicaOrientedFourColorTag G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q oz
  have htargetFalse : ∀ a, (targetTag a).2 = false := by
    apply lpReplicaOrientedFourColorAtom_rank_three_all_falseCurrent
      G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding)
      q hcard hSiCard
    · simpa only [Finset.card_map] using hDCard
  have htargetRows : lpReplicaRowCopies G sites s.profile targetTag false =
      lpReplicaRowCopies G sites s.profile moved false := by
    dsimp only [targetTag, oz, atom, moved,
      lpReplicaOrientedFourColorTag,
      lpReplicaDecoratedOrbitAtomEquivOrientedFourColor,
      lpReplicaDecoratedOrbitAtomOfBalancedSelector]
    apply lpReplicaOrbitCollisionSplitTag_rowCopies_false
  have hbaseRows : lpReplicaRowCopies G sites s.profile s.tag false =
      Finset.univ := by
    ext a
    simp [lpReplicaRowCopies, hbase]
  have hmovedRows : lpReplicaRowCopies G sites s.profile moved false = {c} := by
    calc
      lpReplicaRowCopies G sites s.profile moved false =
          lpReplicaRowCopies G sites s.profile s.tag false ∆ s.selector :=
        lpReplicaRowCopies_toggle G sites s.profile s.selector s.tag false
      _ = Finset.univ ∆ (Finset.univ \ {c}) := by
        rw [hbaseRows, hselector]
      _ = {c} := by
        ext a
        simp [Finset.mem_symmDiff]
  have htargetRows' : lpReplicaRowCopies G sites s.profile targetTag false =
      {c} := htargetRows.trans hmovedRows
  have htag : targetTag =
      lpReplicaToggleRows G sites s.profile {c} sourceTag := by
    funext a
    have hrow := Finset.ext_iff.mp htargetRows' a
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton] at hrow
    by_cases hac : a = c
    · subst a
      apply Prod.ext
      · simp only [lpReplicaToggleRows, Finset.mem_singleton, if_pos]
        rw [hsource c]
        exact hrow.mpr rfl
      · simp only [lpReplicaToggleRows, Finset.mem_singleton, if_pos]
        rw [hsource c]
        exact htargetFalse c
    · apply Prod.ext
      · have hnfalse : (targetTag a).1 ≠ false := by
          intro ha
          exact hac (hrow.mp ha)
        have hnotmem : a ∉ ({c} : Finset _) := by
          intro ha
          exact hac (Finset.mem_singleton.mp ha)
        have htoggle : lpReplicaToggleRows G sites s.profile {c} sourceTag a =
            sourceTag a := by
          unfold lpReplicaToggleRows
          exact if_neg hnotmem
        cases hfirst : (targetTag a).1
        · exact (hnfalse hfirst).elim
        · rw [htoggle, hsource a]
      · have hnotmem : a ∉ ({c} : Finset _) := by
          intro ha
          exact hac (Finset.mem_singleton.mp ha)
        have htoggle : lpReplicaToggleRows G sites s.profile {c} sourceTag a =
            sourceTag a := by
          unfold lpReplicaToggleRows
          exact if_neg hnotmem
        rw [htoggle, hsource a]
        exact htargetFalse a
  change lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
      s.orbitLabel targetTag = _
  rw [lpReplicaOrbitFourColorSlotCrossToggle,
    lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed
      G sites q s.profile s.orbit s.orbitLabel c hfixed,
    lpReplicaOrbitFourColorSlotRowToggle_stateOfTag, htag]

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_three_exists_balancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (∃ s : LPReplicaBalancedSelector G sites
        (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
        s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
          c.1.1 = s(lpReplicaCurrentLeft sites i,
            lpReplicaCurrentRight sites i) ∧
          HEq s.selector (Finset.univ \ {c}) ∧
          (∀ a, s.tag a = (false, false)) ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
              (Sum.inl (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
                G sites i j q s))).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                z.1.1.2 z.2.2 {c})
              (lpReplicaOffdiagDecoratedSourceSlotState
                G sites i j q z)) ∨
      (∃ s : LPReplicaBalancedSelector G sites
        (Sj ∆ Si ∆ T) (Si ∆ T) q,
      ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
        s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
          c.1.1 = s(lpReplicaCurrentLeft sites j,
            lpReplicaCurrentRight sites j) ∧
          HEq s.selector (Finset.univ \ {c}) ∧
          (∀ a, s.tag a = (false, false)) ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
              (Sum.inr (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
                G sites j i q s))).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                z.1.1.2 z.2.2 {c})
              (lpReplicaOffdiagDecoratedSourceSlotState
                G sites i j q z)) := by
  classical
  dsimp only
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  have hdall : ∀ c, d.1 c = (false, false) :=
    lpReplicaOffdiagDecoratedSource_rank_three_swapped_all_false
      G sites hsite hij q hcard z
  have hrow0 : lpReplicaRowCopies G sites m d.1 false = Finset.univ := by
    ext c
    simp [lpReplicaRowCopies, hdall]
  have hrow1 : lpReplicaRowCopies G sites m d.1 true = ∅ := by
    ext c
    simp [lpReplicaRowCopies, hdall]
  have htotal : StatMech.Sharpness.RandomCurrent.sources E Finset.univ = B := by
    have h := lpReplicaRowGate_fullSources G sites m B ∅ d.1 d.2
    calc
      StatMech.Sharpness.RandomCurrent.sources E Finset.univ = B ∆ ∅ := by
        simpa only [E] using h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hBswap : B = Sj ∆ Si ∆ T := by
    change Si ∆ Sj ∆ T = Sj ∆ Si ∆ T
    rw [symmDiff_comm Si Sj]
  rcases lpReplicaOffdiagDecoratedSource_rank_three_exists_seamCopy
      G sites hsite hij q hcard z with ⟨c, hc⟩ | ⟨c, hc⟩
  · let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
    have hfalseFilter : P.filter (fun a => (d.1 a).2 = false) = P := by
      ext a
      simp [P, hdall]
    have htrueFilter : P.filter (fun a => (d.1 a).2 = true) = ∅ := by
      ext a
      simp [P, hdall]
    have hcends : E c = s(lpReplicaCurrentLeft sites i,
        lpReplicaCurrentRight sites i) := by
      simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
    have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
      simpa only [Si, lpMatchingSeamSource] using
        (randomCurrent_sources_singleton_of_ends_eq E c (by
          simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends)
    have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
      rw [hfalseFilter]
      calc
        StatMech.Sharpness.RandomCurrent.sources E P =
            StatMech.Sharpness.RandomCurrent.sources E Finset.univ ∆
              StatMech.Sharpness.RandomCurrent.sources E {c} := by
          exact StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp [P])
        _ = B ∆ Si := by rw [htotal, hsingle]
        _ = Sj ∆ T := by
          change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
          rw [symmDiff_assoc Si Sj T,
            symmDiff_symmDiff_self']
    have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = true) = ∅ := by
      rw [htrueFilter]
      simp [StatMech.Sharpness.RandomCurrent.sources,
        StatMech.Sharpness.RandomCurrent.degK]
    have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow1, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    let s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T)
        (Sj ∆ T) q := {
      profile := m
      orbit := z.1.1.2
      tag := d.1
      gate := d.2
      orbitLabel := z.2.2
      selector := P
      falseSource := hfalseSource
      trueSource := htrueSource
      row0Disconn := hrow0Disconn
      row1Disconn := hrow1Disconn }
    let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
      (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
    have hsourceTag : ∀ a, sourceTag a = (true, false) := by
      exact lpReplicaOffdiagDecoratedSource_rank_three_orientedTag
        G sites hsite hij q hcard z
    have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
      lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc
    have hSiCard : Si.card = 2 := by
      exact card_lpReplicaMatchingSeamSource sites i
    have hDCard : (Sj ∆ T).card = 4 := by
      exact card_lpReplicaMatchingSeamSymmDiffGhost sites j
    have hgeneric := lpReplicaBalancedSelector_rank_three_slotState
      G sites Si Sj T q hcard s c sourceTag hdall hsourceTag rfl hfixed
        hSiCard hDCard
    have hmask : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c} =
        lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c} := rfl
    have hsourceState : lpReplicaOffdiagDecoratedSourceSlotState
        G sites i j q z =
        lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag := rfl
    have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
        Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
    exact Or.inl ⟨s, c, rfl, HEq.rfl, hc, HEq.rfl, hdall, by
      rw [hmask, hsourceState]
      unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
      unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
      dsimp only
      rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
        ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q
        hfixedD]
      exact hgeneric⟩
  · let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
    have hfalseFilter : P.filter (fun a => (d.1 a).2 = false) = P := by
      ext a
      simp [P, hdall]
    have htrueFilter : P.filter (fun a => (d.1 a).2 = true) = ∅ := by
      ext a
      simp [P, hdall]
    have hcends : E c = s(lpReplicaCurrentLeft sites j,
        lpReplicaCurrentRight sites j) := by
      simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
    have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
      simpa only [Sj, lpMatchingSeamSource] using
        (randomCurrent_sources_singleton_of_ends_eq E c (by
          simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends)
    have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
      rw [hfalseFilter]
      calc
        StatMech.Sharpness.RandomCurrent.sources E P =
            StatMech.Sharpness.RandomCurrent.sources E Finset.univ ∆
              StatMech.Sharpness.RandomCurrent.sources E {c} := by
          exact StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp [P])
        _ = B ∆ Sj := by rw [htotal, hsingle]
        _ = Si ∆ T := by
          rw [hBswap, symmDiff_assoc Sj Si T,
            symmDiff_symmDiff_self']
    have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = true) = ∅ := by
      rw [htrueFilter]
      simp [StatMech.Sharpness.RandomCurrent.sources,
        StatMech.Sharpness.RandomCurrent.degK]
    have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow1, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    have hgate : LPReplicaRowGate G sites m (Sj ∆ Si ∆ T) ∅ d.1 := by
      rw [← hBswap]
      exact d.2
    let s : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T)
        (Si ∆ T) q := {
      profile := m
      orbit := z.1.1.2
      tag := d.1
      gate := hgate
      orbitLabel := z.2.2
      selector := P
      falseSource := hfalseSource
      trueSource := htrueSource
      row0Disconn := hrow0Disconn
      row1Disconn := hrow1Disconn }
    let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
      (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
    have hsourceTag : ∀ a, sourceTag a = (true, false) := by
      exact lpReplicaOffdiagDecoratedSource_rank_three_orientedTag
        G sites hsite hij q hcard z
    have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
      lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hc
    have hSjCard : Sj.card = 2 := by
      exact card_lpReplicaMatchingSeamSource sites j
    have hDCard : (Si ∆ T).card = 4 := by
      exact card_lpReplicaMatchingSeamSymmDiffGhost sites i
    have hgeneric := lpReplicaBalancedSelector_rank_three_slotState
      G sites Sj Si T q hcard s c sourceTag hdall hsourceTag rfl hfixed
        hSjCard hDCard
    have hmask : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c} =
        lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c} := rfl
    have hsourceState : lpReplicaOffdiagDecoratedSourceSlotState
        G sites i j q z =
        lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag := rfl
    have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
        Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
    exact Or.inr ⟨s, c, rfl, HEq.rfl, hc, HEq.rfl, hdall, by
      rw [hmask, hsourceState]
      unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
      unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
      dsimp only
      rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
        ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q
        hfixedD]
      exact hgeneric⟩


theorem lpReplicaOffdiagDecoratedSource_rank_three_eq_of_crossTrace_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) :
    z = w := by
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq]
  exact ⟨htrace,
    (lpReplicaOffdiagDecoratedSource_rank_three_rowMask_eq_univ
      G sites hsite hij q hcard z).trans
      (lpReplicaOffdiagDecoratedSource_rank_three_rowMask_eq_univ
        G sites hsite hij q hcard w).symm⟩



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_three_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  apply lpReplicaOffdiagDecoratedSource_rank_three_eq_of_crossTrace_eq
    G sites hsite hij q hcard
  exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_three_nonempty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
  classical
  rcases lpReplicaOffdiagDecoratedSource_rank_three_exists_balancedSelector
      G sites hsite hij q hcard z with
    ⟨s, c, _, _, _, _, _, hstate⟩ | ⟨s, c, _, _, _, _, _, hstate⟩
  · let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
      Sum.inl (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
        G sites i j q s)
    refine ⟨y, ?_⟩
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and, LPReplicaOffdiagBalancedOutput]
      exact Or.inl ⟨s, rfl⟩
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  · let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
      Sum.inr (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
        G sites j i q s)
    refine ⟨y, ?_⟩
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and, LPReplicaOffdiagBalancedOutput]
      exact Or.inr ⟨s, rfl⟩
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _


theorem lpReplicaOffdiagCrossTraceFiberCards_rank_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
  classical
  by_cases hs : (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).Nonempty
  · obtain ⟨z, hz⟩ := hs
    have hztrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
        u := (Finset.mem_filter.mp hz).2
    have ht := lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_three_nonempty
      G sites hsite hij q hcard z
    have ht' : (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).Nonempty := by
      simpa only [hztrace] using ht
    exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_three_card_le_one
      G sites hsite hij q hcard u).trans ht'.card_pos
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    exact Nat.zero_le _


theorem lpReplicaOffdiagCrossToggleMaskHall_rank_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  apply lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards
  intro u
  exact lpReplicaOffdiagCrossTraceFiberCards_rank_three
    G sites hsite hij q hcard u



theorem lpReplicaOffdiagOrbitAtomCardInequality_rank_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    G sites i j q
      (lpReplicaOffdiagCrossToggleMaskHall_rank_three
        G sites hsite hij q hcard)

end

end StatMech.Ising
