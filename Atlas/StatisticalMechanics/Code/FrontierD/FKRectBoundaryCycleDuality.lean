/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnMixedCandidates
import Code.FrontierD.FKRectVerticalWindingCutFiberReduction



open Equiv SimpleGraph

namespace StatMech.FrontierD

noncomputable section


@[simp] theorem fkMedialCheckerColor_dualShift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkMedialCheckerColor (fkRectMedialDualShiftDart R d) =
      !fkMedialCheckerColor d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [fkRectMedialDualShiftDart, fkRectMedialDualShiftVertex,
      fkMedialCheckerColor, fkMedialSideVertical]


@[simp] theorem fkMedialCheckerColor_dualUnshift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkMedialCheckerColor (fkRectMedialDualUnshiftDart R d) =
      !fkMedialCheckerColor d := by
  have h := fkMedialCheckerColor_dualShift R
    (fkRectMedialDualUnshiftDart R d)
  rw [fkRectMedialDualShiftDart_unshift] at h
  cases hc : fkMedialCheckerColor d <;> simp_all



def fkRectDualBlackDartEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    FKMedialBlackDart R.medialTorus ≃ FKMedialBlackDart R.medialTorus where
  toFun d := ⟨fkMedialLocalMate
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))
      (fkRectMedialDualShiftDart R d.1), by
    rw [fkMedialCheckerColor_localMate_eq_not,
      fkMedialCheckerColor_dualShift, d.2]
    rfl⟩
  invFun d := ⟨fkRectMedialDualUnshiftDart R
      (fkMedialLocalMate
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega)) d.1), by
    rw [fkMedialCheckerColor_dualUnshift,
      fkMedialCheckerColor_localMate_eq_not, d.2]
    rfl⟩
  left_inv d := by
    apply Subtype.ext
    simp only [fkMedialLocalMate_involutive,
      fkRectMedialDualUnshiftDart_shift]
  right_inv d := by
    apply Subtype.ext
    simp only [fkRectMedialDualShiftDart_unshift,
      fkMedialLocalMate_involutive]


theorem fkRectDualBlackDartEquiv_reachable_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d e : FKMedialBlackDart R.medialTorus) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))).Reachable
        ((fkRectDualBlackDartEquiv R omega d).1)
        ((fkRectDualBlackDartEquiv R omega e).1) ↔
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 := by
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  change (fkMedialLoopGraph R.medialTorus dualPairing).Reachable
      (fkMedialLocalMate dualPairing
        (fkRectMedialDualShiftDart R d.1))
      (fkMedialLocalMate dualPairing
        (fkRectMedialDualShiftDart R e.1)) ↔ _
  constructor
  · intro h
    have hshift : (fkMedialLoopGraph R.medialTorus dualPairing).Reachable
        (fkRectMedialDualShiftDart R d.1)
        (fkRectMedialDualShiftDart R e.1) :=
      (fkMedial_reachable_localMate dualPairing _).trans
        (h.trans (fkMedial_reachable_localMate dualPairing _).symm)
    exact (fkRectMedialDualShiftGraphIso R omega).reachable_iff.mp hshift
  · intro h
    have hshift :=
      (fkRectMedialDualShiftGraphIso R omega).reachable_iff.mpr h
    exact (fkMedial_reachable_localMate dualPairing _).symm.trans
      (hshift.trans (fkMedial_reachable_localMate dualPairing _))



def fkRectBlackBoundaryCycleDualEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectConfigurationBlackBoundaryCycle R omega ≃
      FKRectConfigurationBlackBoundaryCycle R
        (fkRectDualConfigurationEquiv R omega) where
  toFun := Quot.map (fkRectDualBlackDartEquiv R omega) (by
    intro d e hde
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).2
    apply (fkRectDualBlackDartEquiv_reachable_iff R omega d e).2
    exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).1 hde)
  invFun := Quot.map (fkRectDualBlackDartEquiv R omega).symm (by
    intro d e hde
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).2
    apply (fkRectDualBlackDartEquiv_reachable_iff R omega
      ((fkRectDualBlackDartEquiv R omega).symm d)
      ((fkRectDualBlackDartEquiv R omega).symm e)).1
    simpa using
      (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).1 hde)
  left_inv := by
    intro C
    induction C using Quot.ind with
    | _ d =>
        apply Quot.sound
        simp
  right_inv := by
    intro C
    induction C using Quot.ind with
    | _ d =>
        apply Quot.sound
        simp

@[simp] theorem fkRectBlackBoundaryCycleDualEquiv_mk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ d) =
      Quot.mk _ (fkRectDualBlackDartEquiv R omega d) :=
  rfl


theorem fkMedialBoundaryStep_sameCycle_dualShift_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d e : FKMedialDart R.medialTorus) :
    (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))).SameCycle
        (fkRectMedialDualShiftDart R d)
        (fkRectMedialDualShiftDart R e) ↔
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)).SameCycle d e := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    change (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega)))^[n]
        (fkRectMedialDualShiftDart R d) =
      fkRectMedialDualShiftDart R e at hn
    refine ⟨n, ?_⟩
    change (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega))^[n] d = e
    apply (fkRectMedialDualShiftDartEquiv R).injective
    change fkRectMedialDualShiftDart R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[n] d) =
      fkRectMedialDualShiftDart R e
    rw [fkRectMedialDualShiftDart_boundaryStep_iterate, hn]
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    change (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega))^[n] d = e at hn
    refine ⟨n, ?_⟩
    change (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega)))^[n]
        (fkRectMedialDualShiftDart R d) =
      fkRectMedialDualShiftDart R e
    rw [← fkRectMedialDualShiftDart_boundaryStep_iterate, hn]


theorem fkMedialBoundaryStep_mem_support_dualShift_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualShiftDart R d ∈
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R
            (fkRectDualConfigurationEquiv R omega))).support ↔
      d ∈ (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)).support := by
  simp only [Equiv.Perm.mem_support]
  constructor <;> intro h
  · intro hold
    apply h
    rw [← fkRectMedialDualShiftDart_boundaryStep, hold]
  · intro hdual
    apply h
    apply (fkRectMedialDualShiftDartEquiv R).injective
    change fkRectMedialDualShiftDart R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d) =
      fkRectMedialDualShiftDart R d
    rw [fkRectMedialDualShiftDart_boundaryStep, hdual]

private theorem fkRectMedialBoundaryPrimalSeamTrace_eq_sum_range_duality
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d n =
      ∑ i ∈ Finset.range n,
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[i] d) := by
  induction n generalizing d with
  | zero => simp [fkRectMedialBoundaryPrimalSeamTrace]
  | succ n ih =>
      rw [fkRectMedialBoundaryPrimalSeamTrace, ih,
        Finset.sum_range_succ']
      have htail :
          (∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i]
                (fkMedialBoundaryStep pairing d))) =
            ∑ i ∈ Finset.range n,
              fkRectMedialBoundaryPrimalSeamIncrement R pairing
                ((fkMedialBoundaryStep pairing)^[i + 1] d) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.iterate_succ_apply]
      rw [htail]
      simp only [Function.iterate_zero_apply]
      exact add_comm _ _


theorem fkRectMedialBoundaryPrimalSeamTrace_toList_eq_cycleClass
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus)
    (hd : d ∈ (fkMedialBoundaryStep pairing).support) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d
        ((fkMedialBoundaryStep pairing).toList d).length =
      fkRectBoundaryCycleClassWinding R pairing d := by
  classical
  let sigma := fkMedialBoundaryStep pairing
  let l := sigma.toList d
  let f := fkRectMedialBoundaryPrimalSeamIncrement R pairing
  rw [fkRectMedialBoundaryPrimalSeamTrace_eq_sum_range_duality]
  change (∑ i ∈ Finset.range l.length, f ((sigma^[i]) d)) = _
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin l.length, f ((sigma^[i.val]) d)) =
        (l.map f).sum := by
      rw [← List.sum_ofFn]
      have hlist :
          List.ofFn (fun i : Fin l.length => f ((sigma^[i.val]) d)) =
            l.map f := by
        rw [← List.ofFn_getElem_eq_map l f]
        congr 1
        funext i
        apply congrArg f
        simpa [l, sigma] using
          (Equiv.Perm.getElem_toList sigma d i i.isLt).symm
      rw [hlist]
    _ = ∑ x ∈ l.toFinset, f x := by
      exact (List.sum_toFinset f (Equiv.Perm.nodup_toList sigma d)).symm
    _ = fkRectBoundaryCycleClassWinding R pairing d := by
      unfold fkRectBoundaryCycleClassWinding permCycleClassWeightSum
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change x ∈ sigma.toList d ↔ sigma.SameCycle d x
      rw [Equiv.Perm.mem_toList_iff]
      have hdne : sigma d ≠ d := by
        simpa [sigma, Equiv.Perm.mem_support] using hd
      simp [hdne]


theorem fkMedialBoundaryStep_toList_length_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    ((fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))).toList
          (fkRectMedialDualShiftDart R d)).length =
      ((fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)).toList d).length := by
  classical
  let sigma := fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R omega)
  let dualSigma := fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R
      (fkRectDualConfigurationEquiv R omega))
  let shift := fkRectMedialDualShiftDartEquiv R
  let l := sigma.toList d
  let ld := dualSigma.toList (shift d)
  have hfinset : ld.toFinset = l.toFinset.image shift := by
    ext y
    constructor
    · intro hy
      have hylist : y ∈ dualSigma.toList (shift d) := by
        simpa [ld] using hy
      have hyspec := (Equiv.Perm.mem_toList_iff).1
        hylist
      let x := shift.symm y
      have hyx : shift x = y := shift.apply_symm_apply y
      have hxcycle : sigma.SameCycle d x := by
        apply (fkMedialBoundaryStep_sameCycle_dualShift_iff
          R omega d x).1
        change dualSigma.SameCycle (shift d) (shift x)
        rw [hyx]
        exact hyspec.1
      have hxsupport : d ∈ sigma.support := by
        apply (fkMedialBoundaryStep_mem_support_dualShift_iff
          R omega d).1
        simpa [shift] using hyspec.2
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, hyx⟩
      simpa [l] using
        (Equiv.Perm.mem_toList_iff).2 ⟨hxcycle, hxsupport⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxlist : x ∈ sigma.toList d := by
        simpa [l] using hx
      have hxspec := (Equiv.Perm.mem_toList_iff).1
        hxlist
      have hdualCycle :=
        (fkMedialBoundaryStep_sameCycle_dualShift_iff
          R omega d x).2 hxspec.1
      have hdualSupport :=
        (fkMedialBoundaryStep_mem_support_dualShift_iff
          R omega d).2 hxspec.2
      have hylist : y ∈ dualSigma.toList (shift d) := by
        apply (Equiv.Perm.mem_toList_iff).2
        rw [← hxy]
        simpa [shift] using And.intro hdualCycle hdualSupport
      simpa [ld] using hylist
  calc
    ld.length = ld.toFinset.card :=
      (List.toFinset_card_of_nodup (Equiv.Perm.nodup_toList _ _)).symm
    _ = (l.toFinset.image shift).card := by rw [hfinset]
    _ = l.toFinset.card := Finset.card_image_of_injective _ shift.injective
    _ = l.length := List.toFinset_card_of_nodup
      (Equiv.Perm.nodup_toList _ _)



theorem fkRectBoundaryCycleClassWinding_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d.1) =
      fkRectBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R omega) d.1 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  let sigma := fkMedialBoundaryStep pairing
  let n := (sigma.toList d.1).length
  have hsupport : d.1 ∈ sigma.support := by
    rw [Equiv.Perm.mem_support]
    intro hfix
    apply fkMedialBlackBoundaryPerm_apply_ne pairing d
    apply Subtype.ext
    exact hfix
  have hdualSupport : fkRectMedialDualShiftDart R d.1 ∈
      (fkMedialBoundaryStep dualPairing).support :=
    (fkMedialBoundaryStep_mem_support_dualShift_iff R omega d.1).2 hsupport
  have hclosed : sigma^[n] d.1 = d.1 := by
    change (sigma ^ n) d.1 = d.1
    rw [show n = (sigma.cycleOf d.1).support.card by
      exact Equiv.Perm.length_toList sigma d.1]
    rw [← (Equiv.Perm.isCycle_cycleOf sigma
      (Equiv.Perm.mem_support.mp hsupport)).orderOf,
      ← Equiv.Perm.cycleOf_pow_apply_self, pow_orderOf_eq_one,
      Equiv.Perm.one_apply]
  have htrace := fkRectMedialBoundaryPrimalSeamTrace_dualShift
    R omega d.1 n hclosed
  have horig := fkRectMedialBoundaryPrimalSeamTrace_toList_eq_cycleClass
    R pairing d.1 hsupport
  have hdual := fkRectMedialBoundaryPrimalSeamTrace_toList_eq_cycleClass
    R dualPairing (fkRectMedialDualShiftDart R d.1) hdualSupport
  have hlen := fkMedialBoundaryStep_toList_length_dualShift R omega d.1
  change fkRectBoundaryCycleClassWinding R dualPairing
      (fkRectMedialDualShiftDart R d.1) = _
  change fkRectMedialBoundaryPrimalSeamTrace R dualPairing
      (fkRectMedialDualShiftDart R d.1)
        ((fkMedialBoundaryStep dualPairing).toList
          (fkRectMedialDualShiftDart R d.1)).length = _ at hdual
  rw [hlen] at hdual
  exact hdual.symm.trans (htrace.trans horig)



theorem fkRectBlackBoundaryCycleWinding_dualEquiv
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega C) =
      -fkRectBlackBoundaryCycleWinding R omega C := by
  induction C using Quot.ind with
  | _ d =>
      rw [fkRectBlackBoundaryCycleDualEquiv_mk,
        fkRectBlackBoundaryCycleWinding_mk,
        fkRectBlackBoundaryCycleWinding_mk,
        ← fkRectBoundaryCycleClassWinding_eq_black,
        ← fkRectBoundaryCycleClassWinding_eq_black]
      change fkRectBoundaryCycleClassWinding R
          (fkRectConfigurationToMedialPairing R
            (fkRectDualConfigurationEquiv R omega))
          (fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R
              (fkRectDualConfigurationEquiv R omega))
            (fkRectMedialDualShiftDart R d.1)) = _
      rw [fkRectBoundaryCycleClassWinding_localMate,
        fkRectBoundaryCycleClassWinding_dualShift]



noncomputable def fkRectBlackBoundaryCycleDualComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent :=
  fkRectBlackBoundaryCyclePrimalComponent R
    (fkRectDualConfigurationEquiv R omega)
    (fkRectBlackBoundaryCycleDualEquiv R omega C)



theorem fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔
      fkRectBlackBoundaryCyclePrimalComponent R omega C =
        (fkRectOpenGraph R omega).connectedComponentMk x := by
  induction C using Quot.ind with
  | _ d =>
      rw [fkRectBlackBoundaryCycleInPrimalCluster_mk,
        fkRectBlackBoundaryCyclePrimalComponent_mk,
        ConnectedComponent.eq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩



noncomputable def fkRectDualClusterBoundaryCycleWindingSum
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) : Int × Int := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      if fkRectBlackBoundaryCycleDualComponent R omega C = L then
        fkRectBlackBoundaryCycleWinding R omega C else 0

set_option maxHeartbeats 600000 in


theorem fkRectDualClusterBoundaryCycleWindingSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) :
    fkRectDualClusterBoundaryCycleWindingSum R omega L = 0 := by
  classical
  let dual := fkRectDualConfigurationEquiv R omega
  let e := fkRectBlackBoundaryCycleDualEquiv R omega
  have hzero := fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero
    R dual L.out
  unfold fkRectPrimalClusterBoundaryCycleWindingSum at hzero
  have hcomponent (D : FKRectConfigurationBlackBoundaryCycle R dual) :
      fkRectBlackBoundaryCycleInPrimalCluster R dual L.out D ↔
        fkRectBlackBoundaryCyclePrimalComponent R dual D = L := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
    have hout : (fkRectOpenGraph R dual).connectedComponentMk L.out = L := by
      exact L.out_eq
    rw [hout]
  simp_rw [hcomponent] at hzero
  rw [← e.sum_comp] at hzero
  unfold fkRectDualClusterBoundaryCycleWindingSum
  have hreindexed :
      (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleDualComponent R omega C = L then
          -fkRectBlackBoundaryCycleWinding R omega C else 0) = 0 := by
    simpa only [fkRectBlackBoundaryCycleWinding_dualEquiv,
      fkRectBlackBoundaryCycleDualComponent, dual, e] using hzero
  have hneg :
      -(∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleDualComponent R omega C = L then
          fkRectBlackBoundaryCycleWinding R omega C else 0) = 0 := by
    calc
      _ = ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
          -(if fkRectBlackBoundaryCycleDualComponent R omega C = L then
            fkRectBlackBoundaryCycleWinding R omega C else 0) := by
        rw [Finset.sum_neg_distrib]
      _ = ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
          if fkRectBlackBoundaryCycleDualComponent R omega C = L then
            -fkRectBlackBoundaryCycleWinding R omega C else 0 := by
        apply Finset.sum_congr rfl
        intro C _
        split <;> simp_all
      _ = 0 := hreindexed
  exact neg_eq_zero.mp hneg

end

end StatMech.FrontierD
