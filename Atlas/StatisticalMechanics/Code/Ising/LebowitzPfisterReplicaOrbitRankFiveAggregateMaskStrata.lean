/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow










open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveAggregateMaskStrataDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


noncomputable def lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) (k : Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u).filter fun y =>
      (lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2).card = k



theorem lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
      G sites i j q z)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {c})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2).card = 4 := by
  classical
  let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 c
  have hsourceMask :=
    lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
      G sites hsite hij q hcard z hhigh
  rw [hstate, lpReplicaOrbitFourColorSlotRowMask_crossToggle, hsourceMask]
  have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 {c} = {slot} := by
    unfold lpReplicaOrbitCommonSlotsOfCopies
    rw [Finset.map_singleton]
    rfl
  have hdiff : (Finset.univ ∆ ({slot} : Finset
      (LPReplicaOrbitCommonSlot G sites q))) = Finset.univ \ {slot} := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hslots, hdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hcard, Finset.card_singleton]



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hresolve : LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
      G sites i j q z) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
      G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 4).Nonempty := by
  classical
  rcases hresolve.1 with hsat | hthree
  · rcases hresolve.2 hsat with ⟨c, hc⟩ | ⟨c, hc⟩
    · obtain ⟨y, hyBal, hyTrace, hyMask⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam
          G sites hsite hij q hcard z hsat c hc
      refine ⟨y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
        lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨⟨hyBal, hyTrace⟩, hyMask⟩
    · obtain ⟨y, hyBal, hstate⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
          G sites q z hsat c hc
      let Y : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr y
      have hyMask :=
        lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four
          G sites hsite hij q hcard z (Or.inl hsat) Y c hstate
      refine ⟨Y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
        lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨⟨hyBal, ?_⟩, hyMask⟩
      unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  · obtain ⟨y, c, hyBal, _, hstate⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three
        G sites hsite hij q hcard z hthree.1
    have hyMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four
        G sites hsite hij q hcard z (Or.inr hthree) y c hstate
    refine ⟨y, ?_⟩
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
      lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨⟨hyBal, ?_⟩, hyMask⟩
    unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [hstate]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q _ _



theorem lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    d.output ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
      G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 2 := by
  classical
  simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
    Finset.mem_filter]
  exact ⟨lpReplicaLowRowMarkedOutputData_mem_targetFiber
      G sites q z d,
    lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two
      G sites hsite hij q hcard z hlow d⟩



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    ¬ (y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
          G sites i j q u 2 ∧
        y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
          G sites i j q u 4) := by
  classical
  intro hy
  have htwo := (Finset.mem_filter.mp hy.1).2
  have hfour := (Finset.mem_filter.mp hy.2).2
  omega



theorem lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
        G sites i j q u 4).card := by
  classical
  have hsource :=
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
      G sites hsite hij q hcard u
  by_cases hempty :
      (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
        G sites i j q u).Nonempty
  · obtain ⟨z, hz⟩ := hempty
    have hz' := Finset.mem_filter.mp hz
    have htarget :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow
        G sites hsite hij q hcard z hz'.2
    have htrace := (Finset.mem_filter.mp hz'.1).2
    rw [htrace] at htarget
    exact Nat.le_trans hsource (Finset.card_pos.mpr htarget)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    exact Nat.zero_le _


noncomputable def
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u ∪
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u



noncomputable def lpReplicaLowRowCrossTraceOutputRowMaskTwo
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u) →
      ↑(lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
        G sites i j q u 2) := by
  classical
  intro z
  let hz := Finset.mem_filter.mp z.2
  let d := lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard z.1 hz.2
  refine ⟨d.output, ?_⟩
  have hmem := lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo
    G sites hsite hij q hcard z.1 hz.2 d
  have htrace := (Finset.mem_filter.mp hz.1).2
  simpa only [htrace] using hmem



theorem lpReplicaLowRowCrossTraceOutputRowMaskTwo_val
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u)) :
    (lpReplicaLowRowCrossTraceOutputRowMaskTwo
      G sites hsite hij q hcard u z).1 =
      (lpReplicaLowRowCrossTraceOutput
        G sites hsite hij q hcard u z).1 := by
  rfl




theorem
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (hinjective : Function.Injective
      (lpReplicaLowRowCrossTraceOutput
        G sites hsite hij q hcard u)) :
    (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
      G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  let low := lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
    G sites i j q u
  let high := lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
    G sites i j q u
  let target := lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u
  let targetTwo := lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
    G sites i j q u 2
  let targetFour := lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
    G sites i j q u 4
  let lowOutput : ↑low -> ↑targetTwo :=
    lpReplicaLowRowCrossTraceOutputRowMaskTwo
      G sites hsite hij q hcard u
  have hlowOutput : Function.Injective lowOutput := by
    intro z w hzw
    apply hinjective
    apply Subtype.ext
    rw [← lpReplicaLowRowCrossTraceOutputRowMaskTwo_val
        G sites hsite hij q hcard u z,
      ← lpReplicaLowRowCrossTraceOutputRowMaskTwo_val
        G sites hsite hij q hcard u w]
    exact congrArg Subtype.val hzw
  have hlowCard : low.card <= targetTwo.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective lowOutput hlowOutput
  have hhighCard : high.card <= targetFour.card := by
    exact lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget
      G sites hsite hij q hcard u
  have hsourceDisjoint : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro z hzLow hzHigh
    have hzLow' := Finset.mem_filter.mp hzLow
    have hzHigh' := Finset.mem_filter.mp hzHigh
    have hlowMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
        G sites hsite hij q hcard z hzLow'.2
    have hhighMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
        G sites hsite hij q hcard z hzHigh'.2.1
    rw [hhighMask, Finset.card_univ, hcard] at hlowMask
    omega
  have htargetDisjoint : Disjoint targetTwo targetFour := by
    rw [Finset.disjoint_left]
    intro y hyTwo hyFour
    exact lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four
      G sites i j q u y ⟨hyTwo, hyFour⟩
  have htargetSubset : targetTwo ∪ targetFour ⊆ target := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyTwo | hyFour
    · exact (Finset.mem_filter.mp hyTwo).1
    · exact (Finset.mem_filter.mp hyFour).1
  rw [lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive,
    Finset.card_union_of_disjoint hsourceDisjoint]
  calc
    low.card + high.card <= targetTwo.card + targetFour.card :=
      Nat.add_le_add hlowCard hhighCard
    _ = (targetTwo ∪ targetFour).card :=
      (Finset.card_union_of_disjoint htargetDisjoint).symm
    _ <= target.card := Finset.card_le_card htargetSubset



noncomputable def
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFiveEmbedding_of_lowOutputInjective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (hinjective : Function.Injective
      (lpReplicaLowRowCrossTraceOutput
        G sites hsite hij q hcard u)) :
    ↑(lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
        G sites i j q u) ↪
      ↑(lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective
      G sites hsite hij q hcard u hinjective

end

end StatMech.Ising
