/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFive












open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveAggregateFiberDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  K.card = 3 /\
    exists c, c ∈ Finset.univ \ K /\ (d.1 c).1 = false



def LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive G sites i j q z \/
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    K.card = 3 /\
      exists c, c ∈ Finset.univ \ K /\ (d.1 c).1 = true

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaCurrentCopies G sites z.1.1.1
          (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
          true false) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  change K.card = 3 /\ exists c, c ∈ C /\ (d.1 c).1 = false at hlow
  obtain ⟨hthree, c, hcC, hcrow⟩ := hlow
  have hconst : ∀ a ∈ C, d.1 a = d.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hrow1 : lpReplicaRowCopies G sites z.1.1.1 d.1 true = K := by
    ext a
    constructor
    · intro ha
      have harow : (d.1 a).1 = true := by
        simpa only [lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra haactive
      have haNotK : a ∉ K := by
        intro haK
        have hatag : d.1 a = (true, false) := by
          simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using haK
        exact haactive hatag
      have haC : a ∈ C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, haNotK⟩
      have htag := hconst a haC
      have := congrArg Prod.fst htag
      rw [harow, hcrow] at this
      exact Bool.false_ne_true this.symm
    · intro ha
      have hatag : d.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      simpa only [lpReplicaRowCopies, Finset.mem_filter,
        Finset.mem_univ, true_and, hatag]
  have hsourceTag :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  change lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 _) = _
  rw [hsourceTag, lpReplicaOrbitFourColorSlotRowMask_stateOfTag, hrow1]


theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)).card = 3 := by
  rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
    G sites hsite hij q hcard z hlow,
    lpReplicaOrbitCommonSlotsOfCopies, Finset.card_map]
  exact hlow.1



theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)
        (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 e) = e.1 := by
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 e
  have hmask :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow
  have hslot : slot ∉ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask, mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [slot, Equiv.symm_apply_apply] using
      (Finset.mem_sdiff.mp heC).2
  unfold lpReplicaOffdiagDecoratedSourceCrossTrace
    lpReplicaOrbitFourColorSlotCrossNormalize
  rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem
    G sites q _ state slot hslot]
  exact lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    G sites q z.1.1.1 z.1.1.2 z.2.2 _ e



theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    Set.InjOn (lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z))
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaCurrentCopies G sites z.1.1.1
          (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
          true false)) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  have hmask : lpReplicaOrbitFourColorSlotRowMask G sites q state =
      lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 K :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow
  have hKsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := d.2.2.2.2.1
  have hrawInj := lpReplica_threeCopyOffdiag_edge_injective
    G sites hsite hij z.1.1.1 K hlow.1 hKsource
  intro x hx y hy hedge
  let cx := E.symm x
  let cy := E.symm y
  have hcxK : cx ∈ K :=
    (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K x).mp hx
  have hcyK : cy ∈ K :=
    (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K y).mp hy
  have hxmask : x ∈ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask]
    exact hx
  have hymask : y ∈ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask]
    exact hy
  have hstateEdge (a : LPReplicaOrbitCommonSlot G sites q) :
      lpReplicaOrbitFourColorSlotEdge G sites q state a = (E.symm a).1 := by
    let ca := E.symm a
    have h := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
      G sites q z.1.1.1 z.1.1.2 z.2.2
        (lpReplicaOrientedFourColorTag G sites ∅
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
                  lpReplicaCurrentGhost1) q z)) ca
    simpa only [state, lpReplicaOffdiagDecoratedSourceSlotState,
      lpReplicaOrientedFourColorSlotState, ca, E,
      Equiv.apply_symm_apply] using h
  have hxnorm := lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q state)
      state x hxmask
  have hynorm := lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q state)
      state y hymask
  have hreflect : lpReplicaCurrentEdgeReflect G sites cx.1 =
      lpReplicaCurrentEdgeReflect G sites cy.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) x := by
        simpa only [lpReplicaOffdiagDecoratedSourceCrossTrace,
          lpReplicaOrbitFourColorSlotCrossNormalize, state, cx,
          hstateEdge] using hxnorm.symm
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) y := hedge
      _ = _ := by
        simpa only [lpReplicaOffdiagDecoratedSourceCrossTrace,
          lpReplicaOrbitFourColorSlotCrossNormalize, state, cy,
          hstateEdge] using hynorm
  have hedgeFin : cx.1 = cy.1 :=
    (lpReplicaCurrentEdgeReflect_involutive G sites).injective hreflect
  have hcxy : cx = cy := hrawInj hcxK hcyK
    (congrArg Subtype.val hedgeFin)
  exact E.symm.injective hcxy



theorem lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∈
      lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let C := Finset.univ \ M
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  have hM : M = lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 K :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow
  have hMcard : M.card = 3 :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
      G sites hsite hij q hcard z hlow
  have hCcard : C.card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ M),
      Finset.card_univ, hcard, hMcard]
  have hactive :=
    lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active
      G sites hsite hij q hcard z hlow
  have hsame :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hlow.1
  have hinactive (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ C) :
      E.symm x ∈ Finset.univ \ K := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxK
    have hxM : x ∈ M := by
      rw [hM, mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [E, Equiv.symm_apply_apply] using hxK
    exact (Finset.mem_sdiff.mp hx).2 hxM
  have hedge (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ C) :
      lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) x =
        (E.symm x).1 := by
    simpa only [E, Equiv.apply_symm_apply] using
      (lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive
        G sites hsite hij q hcard z hlow (E.symm x) (hinactive x hx))
  simp only [lpReplicaEligibleInactivePairs, Finset.mem_filter,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  change C.card = 2 /\ _
  refine ⟨hCcard, ?_, ?_⟩
  · have hdouble : Finset.univ \ C = M := by
      ext x
      simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    rw [hdouble, hM]
    exact hactive
  · intro x hx y hy
    rw [hedge x hx, hedge y hy]
    exact Subtype.ext
      (hsame (E.symm x) (hinactive x hx) (E.symm y) (hinactive y hy))


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).filter
      (LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q)



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u).card ≤ 3 := by
  classical
  let inactivePair := fun z : LPReplicaOffdiagDecoratedSource G sites i j q =>
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  calc
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u).card ≤
      (lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q u)).card := by
      apply Finset.card_le_card_of_injOn inactivePair
      · intro z hz
        have hz' := (Finset.mem_filter.mp hz)
        have htrace := (Finset.mem_filter.mp hz'.1).2
        simpa only [inactivePair, htrace] using
          (lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible
            G sites hsite hij q hcard z hz'.2)
      · intro z hz w hw hpairs
        have hz' := (Finset.mem_filter.mp hz)
        have hw' := (Finset.mem_filter.mp hw)
        apply lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
          G sites i j q u hz'.1 hw'.1
        exact (sdiff_right_inj (Finset.subset_univ _)
          (Finset.subset_univ _)).mp hpairs
    _ ≤ 3 := lpReplicaEligibleInactivePairs_card_le_three _



theorem lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
      G sites i j q z) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      Finset.univ := by
  classical
  rcases hhigh with hsat | hhigh
  · exact lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
      G sites hsite hij q hcard z hsat
  · let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    let C := Finset.univ \ K
    change K.card = 3 /\ exists c, c ∈ C /\ (d.1 c).1 = true at hhigh
    obtain ⟨hthree, c, hcC, hcrow⟩ := hhigh
    have hconst : ∀ a ∈ C, d.1 a = d.1 c := by
      intro a ha
      exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
        G sites hsite hij q hcard z hthree a ha c hcC
    have hall (a) : (d.1 a).1 = true := by
      by_cases haK : a ∈ K
      · have hatag : d.1 a = (true, false) := by
          simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using haK
        simp [hatag]
      · have haC : a ∈ C := Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, haK⟩
        exact congrArg Prod.fst (hconst a haC) |>.trans hcrow
    ext x
    simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
      Finset.mem_univ, true_and]
    let e := (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
      z.1.1.2 z.2.2).symm x
    have he := hall e
    have htag := lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
    have he' := congrFun htag e
    simpa only [lpReplicaOffdiagDecoratedSourceSlotState,
      lpReplicaOrientedFourColorSlotState,
      lpReplicaOrbitFourColorSlotStateOfTag, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, iff_true] using
        (congrArg Prod.fst he').trans he


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).filter
      (LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q)


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
      G sites i j q u).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  have hz' := Finset.mem_filter.mp hz
  have hw' := Finset.mem_filter.mp hw
  apply lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
    G sites i j q u hz'.1 hw'.1
  exact (lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
    G sites hsite hij q hcard z hz'.2).trans
      (lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
        G sites hsite hij q hcard w hw'.2).symm


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u ∪
    lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
      G sites i j q u

set_option maxHeartbeats 1000000 in



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u =
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
        G sites i j q u := by
  classical
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
  apply Finset.Subset.antisymm
  · intro z hz
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    have hsplit := lpReplicaOffdiagDecoratedSource_rank_five_active_card
      G sites hsite hij q hcard z
    dsimp only at hsplit
    rcases hsplit with hthree | hsat
    · have hCnonempty : (Finset.univ \ K).Nonempty := by
        have hCcard : (Finset.univ \ K).card = 2 := by
          simpa only [K, d] using hthree.2.1
        exact Finset.card_pos.mp (by omega)
      obtain ⟨c, hc⟩ := hCnonempty
      by_cases hrow : (d.1 c).1 = false
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        exact ⟨hz, by
          change K.card = 3 /\ exists c, c ∈ Finset.univ \ K /\
            (d.1 c).1 = false
          exact ⟨hthree.1, c, hc, hrow⟩⟩
      · have hrow' : (d.1 c).1 = true := by
          cases h : (d.1 c).1 <;> simp_all
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨hz, Or.inr (by
          change K.card = 3 /\ exists c, c ∈ Finset.univ \ K /\
            (d.1 c).1 = true
          exact ⟨hthree.1, c, hc, hrow'⟩)⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hz, Or.inl hsat⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).card ≤ 4 := by
  classical
  rw [lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
    G sites hsite hij q hcard u]
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
  calc
    _ ≤ (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
          G sites i j q u).card +
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
          G sites i j q u).card := Finset.card_union_le _ _
    _ ≤ 3 + 1 := Nat.add_le_add
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
        G sites hsite hij q hcard u)
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
        G sites hsite hij q hcard u)
    _ = 4 := rfl

end

end StatMech.Ising
