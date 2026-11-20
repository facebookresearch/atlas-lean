/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata










open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveCollisionAllocationDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

local instance lpReplicaRankFiveCollisionAllocationFintypeState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitFourColorSlotState G sites q) := by
  classical
  let encode := fun s : LPReplicaOrbitFourColorSlotState G sites q =>
    (s.allocation, s.color)
  exact Fintype.ofInjective encode (by
    intro s t h
    exact LPReplicaOrbitFourColorSlotState.ext
      (congrArg Prod.fst h) (congrArg Prod.snd h))

set_option maxHeartbeats 1200000 in




theorem lpReplicaLowRow_parallelInactive_exists_maskFourTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (k c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i ∨
      k.1.1 = lpReplicaCurrentSeamEdge sites j)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
        G sites i j q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 4 ∧
      lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotRowMask G sites q
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∪
          {lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2 c} := by
  classical
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q
    (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  let a := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 c
  have haNotM : a ∉ M := by
    change a ∉ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [a, Equiv.symm_apply_apply] using
      (Finset.mem_sdiff.mp hcC).2
  have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 {c} = {a} := by
    unfold lpReplicaOrbitCommonSlotsOfCopies
    rw [Finset.map_singleton]
    rfl
  have htarget : ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagBalancedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
    rcases hk with hi | hj
    · obtain ⟨y, hyBal, hstate⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
          G sites hsite hij q hcard z hlow.1 k c hkK hi hcC hck hctag
      exact ⟨(Sum.inl y : LPReplicaOffdiagDecoratedTarget G sites i j q),
        hyBal, hstate⟩
    · obtain ⟨y, hyBal, hstate⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
          G sites hsite hij q hcard z hlow.1 k c hkK hj hcC hck hctag
      exact ⟨(Sum.inr y : LPReplicaOffdiagDecoratedTarget G sites i j q),
        hyBal, hstate⟩
  obtain ⟨y, hyBal, hstate⟩ := htarget
  have hmask : lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 = M ∪ {a} := by
    rw [hstate, lpReplicaOrbitFourColorSlotRowMask_crossToggle, hslots]
    rw [Finset.symmDiff_eq_union]
    exact Finset.disjoint_singleton_right.mpr haNotM
  have hmaskCard : (M ∪ {a}).card = 4 := by
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_singleton_right.mpr haNotM),
      Finset.card_singleton,
      lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
        G sites hsite hij q hcard z hlow]
  refine ⟨y, ?_, ?_⟩
  · simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
      lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨⟨hyBal, ?_⟩, ?_⟩
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
    · rw [hmask]
      exact hmaskCard
  · exact hmask

set_option maxHeartbeats 800000 in



theorem lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowCollisionParallelData G sites i j q z) :
    ({lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 d.inactiveCopy₀,
        lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 d.inactiveCopy₁} :
      Finset (LPReplicaOrbitCommonSlot G sites q)) =
      Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q
    (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  let a := E d.inactiveCopy₀
  let b := E d.inactiveCopy₁
  have haC : a ∈ Finset.univ \ M := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change a ∉ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [a, E, Equiv.symm_apply_apply] using
      (Finset.mem_sdiff.mp d.inactive₀_mem).2
  have hbC : b ∈ Finset.univ \ M := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change b ∉ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [b, E, Equiv.symm_apply_apply] using
      (Finset.mem_sdiff.mp d.inactive₁_mem).2
  have hab : a ≠ b := fun h => d.inactive_ne (E.injective h)
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haC
    · exact hbC
  · have hMcard : M.card = 3 := by
      simpa only [M] using
        lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
          G sites hsite hij q hcard z hlow
    have hCcard : (Finset.univ \ M).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ M),
        Finset.card_univ, hcard, hMcard]
    rw [hCcard, Finset.card_pair hab]



theorem finset_union_singleton_eq_sdiff_of_pair_eq_complement
    {A : Type*} [Fintype A] [DecidableEq A]
    (M : Finset A) {a b : A} (hab : a ≠ b)
    (hpair : ({a, b} : Finset A) = Finset.univ \ M) :
    M ∪ {b} = Finset.univ \ {a} := by
  ext x
  have hx := Finset.ext_iff.mp hpair x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
  constructor
  · intro h hxa
    subst x
    rcases h with haM | hab'
    · exact (hx.mp (Or.inl rfl)) haM
    · exact hab hab'
  · intro hxa
    by_cases hxM : x ∈ M
    · exact Or.inl hxM
    · rcases hx.mpr hxM with hxa' | hxb
      · exact False.elim (hxa hxa')
      · exact Or.inr hxb

set_option maxHeartbeats 200000 in



theorem lpReplicaLowRowCrossTraceOutput_collision_maskFour_card_ge_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z w : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u)) (hzw : z ≠ w)
    (hout : lpReplicaLowRowCrossTraceOutput
      G sites hsite hij q hcard u z =
        lpReplicaLowRowCrossTraceOutput
          G sites hsite hij q hcard u w) :
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
      G sites i j q u 4).card := by
  classical
  have hzmem := Finset.mem_filter.mp z.2
  have hwmem := Finset.mem_filter.mp w.2
  obtain ⟨dz⟩ :=
    lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty
      G sites hsite hij q hcard u z w hzw hout
  obtain ⟨dw⟩ :=
    lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty
      G sites hsite hij q hcard u w z hzw.symm hout.symm
  let Ez := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.1.2 z.1.2.2
  let Ew := lpReplicaProfileCopyEquivCommonSlot G sites q w.1.1.1
    w.1.1.1.2 w.1.2.2
  let Mz := lpReplicaOrbitFourColorSlotRowMask G sites q
    (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1)
  let Mw := lpReplicaOrbitFourColorSlotRowMask G sites q
    (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w.1)
  let z₀ := Ez dz.inactiveCopy₀
  let z₁ := Ez dz.inactiveCopy₁
  let w₀ := Ew dw.inactiveCopy₀
  let w₁ := Ew dw.inactiveCopy₁
  have hzpair : ({z₀, z₁} : Finset
      (LPReplicaOrbitCommonSlot G sites q)) = Finset.univ \ Mz := by
    simpa only [z₀, z₁, Ez, Mz] using
      lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement
        G sites hsite hij q hcard z.1 hzmem.2 dz
  have hwpair : ({w₀, w₁} : Finset
      (LPReplicaOrbitCommonSlot G sites q)) = Finset.univ \ Mw := by
    simpa only [w₀, w₁, Ew, Mw] using
      lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement
        G sites hsite hij q hcard w.1 hwmem.2 dw
  have hz₀z₁ : z₀ ≠ z₁ := fun h => dz.inactive_ne (Ez.injective h)
  have hw₀w₁ : w₀ ≠ w₁ := fun h => dw.inactive_ne (Ew.injective h)
  have hmaskNe : Mz ≠ Mw := by
    intro hmask
    have hsource := lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
      G sites i j q u hzmem.1 hwmem.1 hmask
    exact hzw (Subtype.ext hsource)
  have hpairNe : ({z₀, z₁} : Finset
      (LPReplicaOrbitCommonSlot G sites q)) ≠ {w₀, w₁} := by
    intro hpairs
    apply hmaskNe
    apply (sdiff_right_inj (Finset.subset_univ Mz)
      (Finset.subset_univ Mw)).mp
    rw [← hzpair, ← hwpair, hpairs]
  have hwOutside : w₀ ∉ ({z₀, z₁} : Finset
      (LPReplicaOrbitCommonSlot G sites q)) ∨
      w₁ ∉ ({z₀, z₁} : Finset
        (LPReplicaOrbitCommonSlot G sites q)) := by
    by_contra h
    push Not at h
    apply hpairNe
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h.1
      · exact h.2
    · rw [Finset.card_pair hz₀z₁, Finset.card_pair hw₀w₁]
  have hzmask₀ : Mz ∪ {z₁} = Finset.univ \ {z₀} := by
    exact finset_union_singleton_eq_sdiff_of_pair_eq_complement
      Mz hz₀z₁ hzpair
  have hzmask₁ : Mz ∪ {z₀} = Finset.univ \ {z₁} := by
    rw [Finset.pair_comm] at hzpair
    exact finset_union_singleton_eq_sdiff_of_pair_eq_complement
      Mz hz₀z₁.symm hzpair
  obtain ⟨Y₀, hY₀, hY₀mask⟩ :=
    lpReplicaLowRow_parallelInactive_exists_maskFourTarget
      G sites hsite hij q hcard z.1 hzmem.2 dz.activeCopy dz.inactiveCopy₁
        dz.active_mem dz.markedSeam dz.inactive₁_mem
        dz.inactive₁_parallel dz.inactive₁_tag
  obtain ⟨Y₁, hY₁, hY₁mask⟩ :=
    lpReplicaLowRow_parallelInactive_exists_maskFourTarget
      G sites hsite hij q hcard z.1 hzmem.2 dz.activeCopy dz.inactiveCopy₀
        dz.active_mem dz.markedSeam dz.inactive₀_mem
        dz.inactive₀_parallel dz.inactive₀_tag
  have htracez := (Finset.mem_filter.mp hzmem.1).2
  rw [htracez] at hY₀ hY₁
  have hY₀mask' : lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q Y₀).2 = Finset.univ \ {z₀} := by
    simpa only [Mz, z₁, Ez] using hY₀mask.trans hzmask₀
  have hY₁mask' : lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q Y₁).2 = Finset.univ \ {z₁} := by
    simpa only [Mz, z₀, Ez] using hY₁mask.trans hzmask₁
  have targetNe {Y Z : LPReplicaOffdiagDecoratedTarget G sites i j q}
      {a b : LPReplicaOrbitCommonSlot G sites q} (hab : a ≠ b)
      (hY : lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q Y).2 = Finset.univ \ {a})
      (hZ : lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q Z).2 = Finset.univ \ {b}) : Y ≠ Z := by
    intro h
    subst Z
    have hm : Finset.univ \ ({a} : Finset
        (LPReplicaOrbitCommonSlot G sites q)) = Finset.univ \ {b} :=
      hY.symm.trans hZ
    exact hab (Finset.singleton_inj.mp
      ((sdiff_right_inj (Finset.subset_univ {a})
        (Finset.subset_univ {b})).mp hm))
  rcases hwOutside with hw₀Outside | hw₁Outside
  · have hwmask₀ : Mw ∪ {w₁} = Finset.univ \ {w₀} := by
      exact finset_union_singleton_eq_sdiff_of_pair_eq_complement
        Mw hw₀w₁ hwpair
    obtain ⟨Y₂, hY₂, hY₂mask⟩ :=
      lpReplicaLowRow_parallelInactive_exists_maskFourTarget
        G sites hsite hij q hcard w.1 hwmem.2 dw.activeCopy dw.inactiveCopy₁
          dw.active_mem dw.markedSeam dw.inactive₁_mem
          dw.inactive₁_parallel dw.inactive₁_tag
    have htracew := (Finset.mem_filter.mp hwmem.1).2
    rw [htracew] at hY₂
    have hY₂mask' : lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q Y₂).2 = Finset.univ \ {w₀} := by
      simpa only [Mw, w₁, Ew] using hY₂mask.trans hwmask₀
    have hz₀w₀ : z₀ ≠ w₀ := by
      intro h
      apply hw₀Outside
      simp [h]
    have hz₁w₀ : z₁ ≠ w₀ := by
      intro h
      apply hw₀Outside
      simp [h]
    have hY₀Y₁ : Y₀ ≠ Y₁ :=
      targetNe hz₀z₁ hY₀mask' hY₁mask'
    have hY₀Y₂ : Y₀ ≠ Y₂ :=
      targetNe hz₀w₀ hY₀mask' hY₂mask'
    have hY₁Y₂ : Y₁ ≠ Y₂ :=
      targetNe hz₁w₀ hY₁mask' hY₂mask'
    calc
      3 = ({Y₀, Y₁, Y₂} : Finset
          (LPReplicaOffdiagDecoratedTarget G sites i j q)).card := by
        simp [hY₀Y₁, hY₀Y₂, hY₁Y₂]
      _ ≤ _ := Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hY₀
        · exact hY₁
        · exact hY₂)
  · have hwmask₁ : Mw ∪ {w₀} = Finset.univ \ {w₁} := by
      rw [Finset.pair_comm] at hwpair
      exact finset_union_singleton_eq_sdiff_of_pair_eq_complement
        Mw hw₀w₁.symm hwpair
    obtain ⟨Y₂, hY₂, hY₂mask⟩ :=
      lpReplicaLowRow_parallelInactive_exists_maskFourTarget
        G sites hsite hij q hcard w.1 hwmem.2 dw.activeCopy dw.inactiveCopy₀
          dw.active_mem dw.markedSeam dw.inactive₀_mem
          dw.inactive₀_parallel dw.inactive₀_tag
    have htracew := (Finset.mem_filter.mp hwmem.1).2
    rw [htracew] at hY₂
    have hY₂mask' : lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q Y₂).2 = Finset.univ \ {w₁} := by
      simpa only [Mw, w₀, Ew] using hY₂mask.trans hwmask₁
    have hz₀w₁ : z₀ ≠ w₁ := by
      intro h
      apply hw₁Outside
      simp [h]
    have hz₁w₁ : z₁ ≠ w₁ := by
      intro h
      apply hw₁Outside
      simp [h]
    have hY₀Y₁ : Y₀ ≠ Y₁ :=
      targetNe hz₀z₁ hY₀mask' hY₁mask'
    have hY₀Y₂ : Y₀ ≠ Y₂ :=
      targetNe hz₀w₁ hY₀mask' hY₂mask'
    have hY₁Y₂ : Y₁ ≠ Y₂ :=
      targetNe hz₁w₁ hY₁mask' hY₂mask'
    calc
      3 = ({Y₀, Y₁, Y₂} : Finset
          (LPReplicaOffdiagDecoratedTarget G sites i j q)).card := by
        simp [hY₀Y₁, hY₀Y₂, hY₁Y₂]
      _ ≤ _ := Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hY₀
        · exact hY₁
        · exact hY₂)




theorem
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
      G sites i j q u).card ≤
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
  let f := lpReplicaLowRowCrossTraceOutput
    G sites hsite hij q hcard u
  by_cases hf : Function.Injective f
  · exact
      lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective
        G sites hsite hij q hcard u hf
  · obtain ⟨z, w, hout, hzw⟩ := Function.not_injective_iff.mp hf
    have hsource :
        (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
          G sites i j q u).card ≤ 4 := by
      calc
        _ ≤ low.card + high.card := by
          simpa only [low, high,
            lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive] using
            Finset.card_union_le low high
        _ ≤ 3 + 1 := Nat.add_le_add
          (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
            G sites hsite hij q hcard u)
          (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
            G sites hsite hij q hcard u)
        _ = 4 := rfl
    have htwo : 1 ≤ targetTwo.card := by
      apply Finset.card_pos.mpr
      exact ⟨lpReplicaLowRowCrossTraceOutputRowMaskTwo
          G sites hsite hij q hcard u z,
        (lpReplicaLowRowCrossTraceOutputRowMaskTwo
          G sites hsite hij q hcard u z).2⟩
    have hfour : 3 ≤ targetFour.card := by
      exact lpReplicaLowRowCrossTraceOutput_collision_maskFour_card_ge_three
        G sites hsite hij q hcard u z w hzw hout
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
    have htarget : 4 ≤ target.card := by
      calc
        4 = 1 + 3 := rfl
        _ ≤ targetTwo.card + targetFour.card := Nat.add_le_add htwo hfour
        _ = (targetTwo ∪ targetFour).card :=
          (Finset.card_union_of_disjoint htargetDisjoint).symm
        _ ≤ target.card := Finset.card_le_card htargetSubset
    exact hsource.trans htarget



noncomputable def
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFiveEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    ↑(lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
        G sites i j q u) ↪
      ↑(lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target
      G sites hsite hij q hcard u


noncomputable def lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact lpReplicaOffdiagLowRowSourcesRankFive G sites i j q ∪
    lpReplicaOffdiagResolvableHighRowSourcesRankFive G sites i j q



theorem
    lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
      G sites i j q).card =
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
          G sites i j q u).card := by
  classical
  let trace := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q
  simpa only [lpReplicaOffdiagLowOrResolvableHighSourcesRankFive,
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive,
    lpReplicaOffdiagLowRowSourcesRankFive,
    lpReplicaOffdiagResolvableHighRowSourcesRankFive,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive,
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber, trace,
    Finset.filter_union, Finset.filter_filter,
    and_comm, and_left_comm, and_assoc] using
      Finset.card_eq_sum_card_fiberwise
        (s := lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
          G sites i j q)
        (t := (Finset.univ : Finset
          (LPReplicaOrbitFourColorSlotState G sites q)))
        (f := trace) (fun _ _ => Finset.mem_univ _)



theorem lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
      G sites i j q).card ≤
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  rw [lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers]
  calc
    (∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
          G sites i j q u).card) ≤
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
      exact Finset.sum_le_sum fun u _ =>
        lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target
          G sites hsite hij q hcard u
    _ = (lpReplicaOffdiagBalancedOutputs G sites i j q).card := by
      symm
      simpa using
        (lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers
          G sites i j q
          (Finset.univ : Finset
            (LPReplicaOrbitFourColorSlotState G sites q))
          (fun _ _ => Finset.mem_univ _))
    _ ≤ Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)


def LPReplicaAggregateLowOrResolvableHighSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => Sigma fun j : I =>
    Fin (if i = j then 0 else 1) ×
      ↑(lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q)

noncomputable instance
    instFintypeLPReplicaAggregateLowOrResolvableHighSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype
      (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) := by
  unfold LPReplicaAggregateLowOrResolvableHighSourceRankFive
  infer_instance


theorem card_lpReplicaAggregateLowOrResolvableHighSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) =
      ∑ i : I, ∑ j : I, if i = j then 0 else
        (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
          G sites i j q).card := by
  classical
  unfold LPReplicaAggregateLowOrResolvableHighSourceRankFive
  change Fintype.card
      (Sigma fun i : I => Sigma fun j : I =>
        Fin (if i = j then 0 else 1) ×
          ↑(lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
            G sites i j q)) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_prod, Fintype.card_coe]
  by_cases hij : i = j <;>
    simp [hij, lpReplicaOffdiagLowOrResolvableHighSourcesRankFive]


theorem card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) ≤
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  rw [card_lpReplicaAggregateLowOrResolvableHighSourceRankFive,
    ← sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simpa only [hij, ↓reduceIte] using
      lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target
        G sites hsite hij q hcard



noncomputable def lpReplicaAggregateLowOrResolvableHighRankFiveEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  exact card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target
    G sites hsite q hcard

end

end StatMech.Ising
