/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow











open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveAggregateLowRowDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

local instance lpReplicaRankFiveAggregateLowRowFintypeState
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


@[simp] theorem lpReplicaRowTagEquivFin4_symm_rowToggleFin4_snd
    (a : Fin 4) :
    (lpReplicaRowTagEquivFin4.symm (lpReplicaRowToggleFin4 a)).2 =
      (lpReplicaRowTagEquivFin4.symm a).2 := by
  fin_cases a <;> rfl


theorem lpReplicaOrbitFourColorSlotCrossToggle_current
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) :
    (lpReplicaRowTagEquivFin4.symm
      ((lpReplicaOrbitFourColorSlotCrossToggle G sites q P s).color
        ⟨x, Finset.mem_univ _⟩)).2 =
      (lpReplicaRowTagEquivFin4.symm
        (s.color ⟨x, Finset.mem_univ _⟩)).2 := by
  change (lpReplicaRowTagEquivFin4.symm
      (if x ∈ P then lpReplicaRowToggleFin4
          (s.color ⟨x, Finset.mem_univ _⟩)
        else s.color ⟨x, Finset.mem_univ _⟩)).2 = _
  by_cases hx : x ∈ P
  · simp [hx]
  · simp [hx]



structure LPReplicaLowRowMarkedOutputData
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) where
  output : LPReplicaOffdiagDecoratedTarget G sites i j q
  copy : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  copy_active : copy ∈ lpReplicaCurrentCopies G sites z.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  balanced : LPReplicaOffdiagBalancedOutput G sites i j q output
  branch :
    (∃ y, output = Sum.inl y ∧
      copy.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
    (∃ y, output = Sum.inr y ∧
      copy.1.1 = lpReplicaCurrentSeamEdge sites j)
  state_eq :
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q output).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {copy})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)


theorem nonempty_lpReplicaLowRowMarkedOutputData
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    Nonempty (LPReplicaLowRowMarkedOutputData G sites q z) := by
  classical
  rcases lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three
      G sites hsite hij q hcard z hlow.1 with
    ⟨c, hcK, hc⟩ | ⟨c, hcK, hc⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hyRest⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hlow.1 c hcK hc
    have hyState := hyRest.1
    exact ⟨{
      output := Sum.inl y
      copy := c
      copy_active := hcK
      balanced := hyBal
      branch := Or.inl ⟨y, rfl, hc⟩
      state_eq := hyState }⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hyRest⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hlow.1 c hcK hc
    have hyState := hyRest.1
    exact ⟨{
      output := Sum.inr y
      copy := c
      copy_active := hcK
      balanced := hyBal
      branch := Or.inr ⟨y, rfl, hc⟩
      state_eq := hyState }⟩


noncomputable def lpReplicaLowRowMarkedOutputData
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    LPReplicaLowRowMarkedOutputData G sites q z :=
  Classical.choice (nonempty_lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard z hlow)



theorem lpReplicaLowRowMarkedOutputData_mem_targetFiber
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    d.output ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
  classical
  simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
    Finset.mem_filter]
  constructor
  · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact d.balanced
  · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [d.state_eq]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle G sites q _ _


theorem lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q d.output).2).card = 2 := by
  classical
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  let slot := E d.copy
  have hMcard : M.card = 3 := by
    exact lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
      G sites hsite hij q hcard z hlow
  have hslotM : slot ∈ M := by
    change slot ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [slot, E, Equiv.symm_apply_apply] using d.copy_active
  have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 {d.copy} = {slot} := by
    simp [lpReplicaOrbitCommonSlotsOfCopies, slot, E]
  have hdiff : M ∆ {slot} = M \ {slot} := by
    ext x
    by_cases hx : x = slot
    · subst x
      simp [Finset.mem_symmDiff, hslotM]
    · simp [Finset.mem_symmDiff, hx]
  rw [d.state_eq, lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    hslots]
  change (M ∆ {slot}).card = 2
  rw [hdiff, Finset.card_sdiff_of_subset (by simpa using hslotM),
    hMcard, Finset.card_singleton]

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagDecoratedSourceSlotState_current_copy
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1) :
    (lpReplicaRowTagEquivFin4.symm
      ((lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z).color
        ⟨lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 c, Finset.mem_univ _⟩)).2 =
      ((lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c).2 := by
  have htag :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  change (lpReplicaRowTagEquivFin4.symm
      ((lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 _).color
        ⟨lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 c, Finset.mem_univ _⟩)).2 = _
  rw [lpReplicaOrbitFourColorSlotStateOfTag_color_copy, htag]
  simp


noncomputable def lpReplicaLowRowCrossTraceOutput
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u) →
      ↑(lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u) := by
  classical
  intro z
  exact by
    let hz := Finset.mem_filter.mp z.2
    let d := lpReplicaLowRowMarkedOutputData
      G sites hsite hij q hcard z.1 hz.2
    refine ⟨d.output, ?_⟩
    have hmem := lpReplicaLowRowMarkedOutputData_mem_targetFiber
      G sites q z.1 d
    have htrace := (Finset.mem_filter.mp hz.1).2
    simpa only [htrace] using hmem

set_option maxHeartbeats 800000 in




structure LPReplicaLowRowCollisionParallelData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) where
  activeCopy : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  inactiveCopy₀ : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  inactiveCopy₁ : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  active_mem : activeCopy ∈ lpReplicaCurrentCopies G sites z.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  inactive₀_mem : inactiveCopy₀ ∈ Finset.univ \
    lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  inactive₁_mem : inactiveCopy₁ ∈ Finset.univ \
    lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  inactive₀_parallel : inactiveCopy₀.1.1 = activeCopy.1.1
  inactive₁_parallel : inactiveCopy₁.1.1 = activeCopy.1.1
  inactive₀_tag :
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 inactiveCopy₀ =
      (false, false)
  inactive₁_tag :
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 inactiveCopy₁ =
      (false, false)
  inactive_ne : inactiveCopy₀ ≠ inactiveCopy₁
  markedSeam : activeCopy.1.1 = lpReplicaCurrentSeamEdge sites i ∨
    activeCopy.1.1 = lpReplicaCurrentSeamEdge sites j

set_option maxHeartbeats 1600000 in



theorem lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty
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
    Nonempty (LPReplicaLowRowCollisionParallelData G sites i j q z.1) := by
  classical
  have hzmem := Finset.mem_filter.mp z.2
  have hwmem := Finset.mem_filter.mp w.2
  have hzsource := hzmem.1
  have hwsource := hwmem.1
  have hzlow := hzmem.2
  have hwlow := hwmem.2
  have htracez := (Finset.mem_filter.mp hzsource).2
  have htracew := (Finset.mem_filter.mp hwsource).2
  let dz := lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard z.1 hzlow
  let dw := lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard w.1 hwlow
  have hout' : dz.output = dw.output := congrArg Subtype.val hout
  let sz := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1
  let sw := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w.1
  let Mz := lpReplicaOrbitFourColorSlotRowMask G sites q sz
  let Mw := lpReplicaOrbitFourColorSlotRowMask G sites q sw
  let Ez := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1.1
    z.1.1.1.2 z.1.2.2
  let Ew := lpReplicaProfileCopyEquivCommonSlot G sites q w.1.1.1.1
    w.1.1.1.2 w.1.2.2
  let az := Ez dz.copy
  let aw := Ew dw.copy
  have hsinglez : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1.1
      z.1.1.1.2 z.1.2.2 {dz.copy} = {az} := by
    simp [lpReplicaOrbitCommonSlotsOfCopies, az, Ez]
  have hsinglew : lpReplicaOrbitCommonSlotsOfCopies G sites q w.1.1.1.1
      w.1.1.1.2 w.1.2.2 {dw.copy} = {aw} := by
    simp [lpReplicaOrbitCommonSlotsOfCopies, aw, Ew]
  have hazM : az ∈ Mz := by
    change az ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z.1 hzlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [az, Ez, Equiv.symm_apply_apply] using dz.copy_active
  have hawM : aw ∈ Mw := by
    change aw ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w.1)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard w.1 hwlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [aw, Ew, Equiv.symm_apply_apply] using dw.copy_active
  have htargetState :
      lpReplicaOrbitFourColorSlotCrossToggle G sites q {az} sz =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q {aw} sw := by
    calc
      _ = (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q dz.output).2 := by
        simpa only [sz, hsinglez] using dz.state_eq.symm
      _ = (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q dw.output).2 := congrArg
        (fun y => (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2) hout'
      _ = _ := by simpa only [sw, hsinglew] using dw.state_eq
  have hmask : Mz ∆ {az} = Mw ∆ {aw} := by
    have h := congrArg (lpReplicaOrbitFourColorSlotRowMask G sites q)
      htargetState
    simpa only [lpReplicaOrbitFourColorSlotRowMask_crossToggle, Mz, Mw]
      using h
  have hzwVal : z.1 ≠ w.1 := fun h => hzw (Subtype.ext h)
  have hazaw : az ≠ aw := by
    intro h
    have ht : lpReplicaOrbitFourColorSlotCrossToggle G sites q {az} sz =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q {az} sw := by
      simpa only [h] using htargetState
    have hstate : sz = sw :=
      (lpReplicaOrbitFourColorSlotCrossToggle_involutive
        G sites q {az}).injective ht
    exact hzwVal (lpReplicaOffdiagDecoratedSourceSlotState_injective
      G sites i j q hstate)
  have hawNotMz : aw ∉ Mz := by
    intro hawMz
    have hawLeft : aw ∈ Mz ∆ {az} := by
      simp [Finset.mem_symmDiff, hawMz, hazaw.symm]
    rw [hmask] at hawLeft
    simp [Finset.mem_symmDiff, hawM] at hawLeft
  let e := Ez.symm aw
  let Kz := lpReplicaCurrentCopies G sites z.1.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1 true false
  let Cz := Finset.univ \ Kz
  have heC : e ∈ Cz := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heK
    have hawMz : aw ∈ Mz := by
      change aw ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z.1)
      rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
        G sites hsite hij q hcard z.1 hzlow]
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [e, Ez, Equiv.apply_symm_apply] using heK
    exact hawNotMz hawMz
  have hrawCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr Ez
      _ = 5 := hcard
  have hCcard : Cz.card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Kz),
      Finset.card_univ, hrawCard]
    change 5 - (lpReplicaCurrentCopies G sites z.1.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1
        true false).card = 2
    rw [hzlow.1]
  have hexists : ∃ f ∈ Cz, f ≠ e :=
    Finset.exists_mem_ne (s := Cz) (by omega) e
  let f := Classical.choose hexists
  have hfC : f ∈ Cz := (Classical.choose_spec hexists).1
  have hfe : f ≠ e := (Classical.choose_spec hexists).2
  have hcur :
      (lpReplicaRowTagEquivFin4.symm
        (sz.color ⟨aw, Finset.mem_univ _⟩)).2 =
      (lpReplicaRowTagEquivFin4.symm
        (sw.color ⟨aw, Finset.mem_univ _⟩)).2 := by
    calc
      _ = (lpReplicaRowTagEquivFin4.symm
          ((lpReplicaOrbitFourColorSlotCrossToggle
            G sites q {az} sz).color ⟨aw, Finset.mem_univ _⟩)).2 :=
        (lpReplicaOrbitFourColorSlotCrossToggle_current
          G sites q {az} sz aw).symm
      _ = (lpReplicaRowTagEquivFin4.symm
          ((lpReplicaOrbitFourColorSlotCrossToggle
            G sites q {aw} sw).color ⟨aw, Finset.mem_univ _⟩)).2 := by
        rw [htargetState]
      _ = _ := lpReplicaOrbitFourColorSlotCrossToggle_current
        G sites q {aw} sw aw
  have hwtag : (lpReplicaDecoratedSourceRowGateData
      G sites i j q w.1).1 dw.copy = (true, false) := by
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using dw.copy_active
  have hecurrent :
      ((lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1 e).2 =
        false := by
    calc
      _ = (lpReplicaRowTagEquivFin4.symm
          (sz.color ⟨aw, Finset.mem_univ _⟩)).2 := by
        simpa only [sz, e, Ez, Equiv.apply_symm_apply] using
          (lpReplicaOffdiagDecoratedSourceSlotState_current_copy
            G sites i j q z.1 e).symm
      _ = (lpReplicaRowTagEquivFin4.symm
          (sw.color ⟨aw, Finset.mem_univ _⟩)).2 := hcur
      _ = ((lpReplicaDecoratedSourceRowGateData
          G sites i j q w.1).1 dw.copy).2 := by
        simpa only [sw, aw, Ew] using
          lpReplicaOffdiagDecoratedSourceSlotState_current_copy
            G sites i j q w.1 dw.copy
      _ = false := by rw [hwtag]
  let c0 := Classical.choose hzlow.2
  have hc0C := (Classical.choose_spec hzlow.2).1
  have hc0row := (Classical.choose_spec hzlow.2).2
  have heconst :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z.1 hzlow.1 e heC c0 hc0C
  have herow :
      ((lpReplicaDecoratedSourceRowGateData G sites i j q z.1).1 e).1 =
        false := (congrArg Prod.fst heconst).trans hc0row
  have hetag : (lpReplicaDecoratedSourceRowGateData
      G sites i j q z.1).1 e = (false, false) := by
    exact Prod.ext herow hecurrent
  have hftag : (lpReplicaDecoratedSourceRowGateData
      G sites i j q z.1).1 f = (false, false) := by
    rw [lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z.1 hzlow.1 f hfC e heC, hetag]
  have heTraceEdge : lpReplicaOrbitFourColorSlotEdge G sites q u aw = e.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace
            G sites i j q z.1) aw := congrArg
        (fun s => lpReplicaOrbitFourColorSlotEdge G sites q s aw)
          htracez |>.symm
      _ = e.1 := by
        simpa only [e, Ez, Equiv.apply_symm_apply] using
          lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive
            G sites hsite hij q hcard z.1 hzlow e heC
  have hwSourceEdge : lpReplicaOrbitFourColorSlotEdge G sites q sw aw =
      dw.copy.1 := by
    simpa only [sw, aw, Ew] using
      lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy G sites q
        w.1.1.1.1 w.1.1.1.2 w.1.2.2
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
                  lpReplicaCurrentGhost1) q w.1)) dw.copy
  have hwTraceEdge : lpReplicaOrbitFourColorSlotEdge G sites q u aw =
      lpReplicaCurrentEdgeReflect G sites dw.copy.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace
            G sites i j q w.1) aw := congrArg
        (fun s => lpReplicaOrbitFourColorSlotEdge G sites q s aw)
          htracew |>.symm
      _ = _ := by
        unfold lpReplicaOffdiagDecoratedSourceCrossTrace
          lpReplicaOrbitFourColorSlotCrossNormalize
        rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
          G sites q Mw sw aw hawM, hwSourceEdge]
  have hmarked : dz.copy.1.1 = lpReplicaCurrentSeamEdge sites i ∨
      dz.copy.1.1 = lpReplicaCurrentSeamEdge sites j := by
    rcases dz.branch with ⟨_yz, _hyz, hzseam⟩ | ⟨_yz, _hyz, hzseam⟩
    · exact Or.inl hzseam
    · exact Or.inr hzseam
  have heparallel : e.1 = dz.copy.1 := by
    rcases dz.branch with ⟨_yz, hyz, hzseam⟩ | ⟨_yz, hyz, hzseam⟩
    · rcases dw.branch with ⟨_yw, _hyw, hwseam⟩ | ⟨_yw, hyw, _hwseam⟩
      · have hwfixed : dw.copy.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
          lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
            G sites i w.1.1.1.1 dw.copy hwseam
        have hwreflect := (mem_lpReplicaCurrentEdgeOrbitFixed
          G sites dw.copy.1).mp hwfixed
        calc
          e.1 = lpReplicaOrbitFourColorSlotEdge G sites q u aw :=
            heTraceEdge.symm
          _ = lpReplicaCurrentEdgeReflect G sites dw.copy.1 := hwTraceEdge
          _ = dw.copy.1 := hwreflect.symm
          _ = dz.copy.1 := Subtype.ext (hwseam.trans hzseam.symm)
      · rw [hyz, hyw] at hout'
        cases hout'
    · rcases dw.branch with ⟨_yw, hyw, _hwseam⟩ | ⟨_yw, _hyw, hwseam⟩
      · rw [hyz, hyw] at hout'
        cases hout'
      · have hwfixed : dw.copy.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
          lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
            G sites j w.1.1.1.1 dw.copy hwseam
        have hwreflect := (mem_lpReplicaCurrentEdgeOrbitFixed
          G sites dw.copy.1).mp hwfixed
        calc
          e.1 = lpReplicaOrbitFourColorSlotEdge G sites q u aw :=
            heTraceEdge.symm
          _ = lpReplicaCurrentEdgeReflect G sites dw.copy.1 := hwTraceEdge
          _ = dw.copy.1 := hwreflect.symm
          _ = dz.copy.1 := Subtype.ext (hwseam.trans hzseam.symm)
  have hfparallel : f.1.1 = dz.copy.1.1 :=
    (lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z.1 hzlow.1 f hfC e heC).trans
        (congrArg Subtype.val heparallel)
  exact ⟨{
    activeCopy := dz.copy
    inactiveCopy₀ := e
    inactiveCopy₁ := f
    active_mem := dz.copy_active
    inactive₀_mem := heC
    inactive₁_mem := hfC
    inactive₀_parallel := congrArg Subtype.val heparallel
    inactive₁_parallel := hfparallel
    inactive₀_tag := hetag
    inactive₁_tag := hftag
    inactive_ne := hfe.symm
    markedSeam := hmarked }⟩




noncomputable opaque lpReplicaLowRowCrossTraceOutput_collision_parallelData
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
    LPReplicaLowRowCollisionParallelData G sites i j q z.1 :=
  Classical.choice
    (lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty
      G sites hsite hij q hcard u z w hzw hout)



theorem lpReplicaLowRowCrossTraceOutput_collision_card_ge_three
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
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber
      G sites i j q u).card := by
  classical
  let d := lpReplicaLowRowCrossTraceOutput_collision_parallelData
    G sites hsite hij q hcard u z w hzw hout
  have hzmem := Finset.mem_filter.mp z.2
  rcases d.markedSeam with hi | hj
  · have hthree :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair
        G sites hsite hij q hcard z.1 hzmem.2.1 d.activeCopy
        d.inactiveCopy₀ d.inactiveCopy₁ d.active_mem hi d.inactive₀_mem
        d.inactive₁_mem d.inactive₀_parallel d.inactive₁_parallel
        d.inactive₀_tag d.inactive₁_tag d.inactive_ne
    have htrace := (Finset.mem_filter.mp hzmem.1).2
    simpa only [htrace] using hthree
  · have hthree :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair
        G sites hsite hij q hcard z.1 hzmem.2.1 d.activeCopy
        d.inactiveCopy₀ d.inactiveCopy₁ d.active_mem hj d.inactive₀_mem
        d.inactive₁_mem d.inactive₀_parallel d.inactive₁_parallel
        d.inactive₀_tag d.inactive₁_tag d.inactive_ne
    have htrace := (Finset.mem_filter.mp hzmem.1).2
    simpa only [htrace] using hthree




theorem lpReplicaOffdiagLowRowCrossTraceFiberRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u).card ≤
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  let f := lpReplicaLowRowCrossTraceOutput
    G sites hsite hij q hcard u
  by_cases hf : Function.Injective f
  · simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  · obtain ⟨z, w, houtput, hzw⟩ := Function.not_injective_iff.mp hf
    exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
      G sites hsite hij q hcard u).trans
        (lpReplicaLowRowCrossTraceOutput_collision_card_ge_three
          G sites hsite hij q hcard u z w hzw houtput)


noncomputable def lpReplicaOffdiagLowRowSourcesRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter
    (LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q)



theorem lpReplicaOffdiagLowRowSourcesRankFive_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagLowRowSourcesRankFive G sites i j q).card =
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
          G sites i j q u).card := by
  classical
  let trace := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q
  simpa only [lpReplicaOffdiagLowRowSourcesRankFive,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive, trace,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
    Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
      Finset.card_eq_sum_card_fiberwise
        (s := lpReplicaOffdiagLowRowSourcesRankFive G sites i j q)
        (t := (Finset.univ : Finset
          (LPReplicaOrbitFourColorSlotState G sites q)))
        (f := trace) (fun _ _ => Finset.mem_univ _)



theorem lpReplicaOffdiagLowRowSourcesRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    (lpReplicaOffdiagLowRowSourcesRankFive G sites i j q).card ≤
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  rw [lpReplicaOffdiagLowRowSourcesRankFive_card_eq_sum_traceFibers]
  calc
    (∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
          G sites i j q u).card) ≤
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
      exact Finset.sum_le_sum fun u _ =>
        lpReplicaOffdiagLowRowCrossTraceFiberRankFive_card_le_target
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


def LPReplicaAggregateLowRowSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => Sigma fun j : I =>
    Fin (if i = j then 0 else 1) ×
      ↑(lpReplicaOffdiagLowRowSourcesRankFive G sites i j q)

noncomputable instance instFintypeLPReplicaAggregateLowRowSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateLowRowSourceRankFive G sites q) := by
  unfold LPReplicaAggregateLowRowSourceRankFive
  infer_instance


theorem card_lpReplicaAggregateLowRowSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaAggregateLowRowSourceRankFive G sites q) =
      ∑ i : I, ∑ j : I, if i = j then 0 else
        (lpReplicaOffdiagLowRowSourcesRankFive G sites i j q).card := by
  classical
  unfold LPReplicaAggregateLowRowSourceRankFive
  change Fintype.card
      (Sigma fun i : I => Sigma fun j : I =>
        Fin (if i = j then 0 else 1) ×
          ↑(lpReplicaOffdiagLowRowSourcesRankFive G sites i j q)) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_prod, Fintype.card_coe]
  by_cases hij : i = j <;>
    simp [hij, lpReplicaOffdiagLowRowSourcesRankFive]



theorem card_lpReplicaAggregateLowRowSourceRankFive_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Fintype.card (LPReplicaAggregateLowRowSourceRankFive G sites q) ≤
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  rw [card_lpReplicaAggregateLowRowSourceRankFive,
    ← sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simpa only [hij, ↓reduceIte] using
      lpReplicaOffdiagLowRowSourcesRankFive_card_le_target
        G sites hsite hij q hcard


noncomputable def lpReplicaAggregateLowRowRankFiveEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateLowRowSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  exact card_lpReplicaAggregateLowRowSourceRankFive_le_target
    G sites hsite q hcard

end

end StatMech.Ising
