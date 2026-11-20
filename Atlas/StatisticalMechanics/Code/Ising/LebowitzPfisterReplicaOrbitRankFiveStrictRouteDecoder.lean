/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute
import Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection









namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRouteDecoderDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def lpReplicaOrbitFourColorSlotReflectRowToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotRowToggle G sites q row
    (lpReplicaOrbitFourColorSlotReflect G sites q spatial s)

@[simp] theorem lpReplicaOrbitFourColorSlotReflectRowToggle_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOrbitFourColorSlotReflectRowToggle
      G sites q spatial row s).allocation =
      (lpReplicaOrbitFourColorSlotReflect
        G sites q spatial s).allocation := rfl

@[simp] theorem lpReplicaOrbitFourColorSlotReflectRowToggle_color
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : ↑(Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q))) :
    (lpReplicaOrbitFourColorSlotReflectRowToggle
      G sites q spatial row s).color x =
      if x.1 ∈ row then lpReplicaRowToggleFin4 (s.color x)
      else s.color x := rfl



theorem lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial row s) =
      lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ row := by
  have h := lpReplicaOrbitFourColorSlotRowMask_crossToggle
    G sites q row s
  change lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOrbitFourColorSlotReflectRowToggle
        G sites q spatial row s) = _
  exact h

@[simp] theorem lpReplicaOrbitFourColorSlotStateOfTag_color
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (x : ↑(Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q))) :
    (lpReplicaOrbitFourColorSlotStateOfTag
      G sites q m hm L tag).color x =
      lpReplicaRowTagEquivFin4
        (tag ((lpReplicaProfileCopyEquivCommonSlot
          G sites q m hm L).symm x.1)) := rfl



theorem lpReplicaSingletonFalseRowTag_equivFin4
    {C : Type*} [DecidableEq C] (c a : C) :
    lpReplicaRowTagEquivFin4 (lpReplicaSingletonFalseRowTag c a) =
      if a = c then
        lpReplicaRowToggleFin4 (lpReplicaRowTagEquivFin4 (true, false))
      else lpReplicaRowTagEquivFin4 (true, false) := by
  by_cases h : a = c
  · subst a
    simp [lpReplicaSingletonFalseRowTag, lpReplicaRowToggleFin4,
      lpReplicaRowTagEquivFin4]
  · simp [lpReplicaSingletonFalseRowTag, lpReplicaRowTagEquivFin4, h]


theorem lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotReflectRowToggle
        G sites q spatial row) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · exact congrArg (fun z => z.allocation)
      (lpReplicaOrbitFourColorSlotReflect_involutive
        G sites q spatial s)
  · exact congrArg (fun z => z.color)
      (lpReplicaOrbitFourColorSlotRowToggle_involutive
        G sites q row s)




theorem lpReplicaOrbitFourColorSlotReflectRowToggle_comm
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial₀ spatial₁ row :
      Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row
        (lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial₁ row s) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row
        (lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial₀ row s) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    change (s.allocation e ∆
        lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₁ e) ∆
          lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₀ e =
      (s.allocation e ∆
        lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₀ e) ∆
          lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₁ e
    rw [symmDiff_assoc, symmDiff_assoc]
    congr 1
    exact symmDiff_comm _ _
  · funext x
    simp only [lpReplicaOrbitFourColorSlotReflectRowToggle_color]



theorem lpReplicaOrbitFourColorSlotReflectRowToggle_crossed
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial₀ spatial₁ row :
      Finset (LPReplicaOrbitCommonSlot G sites q))
    (s t : LPReplicaOrbitFourColorSlotState G sites q)
    (hcross :
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row s =
        lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial₁ row t) :
    lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row s =
      lpReplicaOrbitFourColorSlotReflectRowToggle
        G sites q spatial₀ row t := by
  let F₀ := lpReplicaOrbitFourColorSlotReflectRowToggle
    G sites q spatial₀ row
  let F₁ := lpReplicaOrbitFourColorSlotReflectRowToggle
    G sites q spatial₁ row
  change F₀ s = F₁ t at hcross
  change F₁ s = F₀ t
  calc
    F₁ s = F₁ (F₀ (F₀ s)) := congrArg F₁
      (lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
        G sites q spatial₀ row s).symm
    _ = F₀ (F₁ (F₀ s)) :=
      (lpReplicaOrbitFourColorSlotReflectRowToggle_comm
        G sites q spatial₀ spatial₁ row (F₀ s)).symm
    _ = F₀ (F₁ (F₁ t)) := congrArg (fun u => F₀ (F₁ u)) hcross
    _ = F₀ t := congrArg F₀
      (lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
        G sites q spatial₁ row t)



theorem lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (rawTag : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P)) ->
      LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hraw : LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      A B rawTag) :
    let target := lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
      G sites q m hm L P
    let tag := lpReplicaTransportTag G sites relabel rawTag
    let atom := lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
      G sites q m hm L P rawTag A B hraw
    lpReplicaOrientedFourColorSlotState G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
          (B.map lpReplicaCurrentReflect.toEmbedding) q atom) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q target
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L) tag := by
  dsimp only
  unfold lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
  apply lpReplicaOrientedFourColorSlotState_ofRowGate

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 := by
  change lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
      z.1.1.2 z.2.2
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
              lpReplicaCurrentGhost1) q z)) = _
  rw [lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData]



theorem lpReplicaStrictRouteSingletonTag_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (c d : Copy (lpReplicaCurrentGraph G sites) m)
    (sourceTag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hsource : ∀ e, sourceTag e = (true, false)) :
    let rawCopy := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
    let rawTag := lpReplicaSingletonFalseRowTag (rawCopy c)
    let target := lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
      G sites q m hm L {d}
    let targetTag := lpReplicaTransportTag G sites relabel rawTag
    let spatial := lpReplicaOrbitCommonSlotsOfCopies
      G sites q m hm L {d}
    let row := lpReplicaOrbitCommonSlotsOfCopies
      G sites q m hm L {c}
    lpReplicaOrbitFourColorSlotStateOfTag G sites q target
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m {d}).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm {d} L) targetTag =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L sourceTag) := by
  classical
  dsimp only
  apply LPReplicaOrbitFourColorSlotState.ext
  · exact lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots
      G sites q m hm L {d} sourceTag
  · funext x
    let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let target := lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let Lt := lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm {d} L
    let Et := lpReplicaProfileCopyEquivCommonSlot G sites q target
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m {d}).trans hm) Lt
    let Ecanon := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L {d}
    let Eraw := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
    have hslot : Ecanon (Es.symm x.1) = Et.symm x.1 := by
      apply Et.injective
      dsimp only [Ecanon, lpReplicaPartialReflectCanonicalCopyEquiv,
        Equiv.trans_apply]
      rw [Es.apply_symm_apply, Et.apply_symm_apply]
    have hpre :
        (lpReplicaPartialReflectCanonicalRelabelEquiv
          G sites q m hm L {d}).symm (Et.symm x.1) =
          Eraw (Es.symm x.1) := by
      unfold lpReplicaPartialReflectCanonicalRelabelEquiv
      change Eraw (Ecanon.symm (Et.symm x.1)) = Eraw (Es.symm x.1)
      rw [← hslot, Ecanon.symm_apply_apply]
    have hrow : x.1 ∈ lpReplicaOrbitCommonSlotsOfCopies
        G sites q m hm L {c} ↔ Es.symm x.1 = c := by
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      change Es.symm x.1 ∈ {c} ↔ Es.symm x.1 = c
      simp only [Finset.mem_singleton]
    rw [lpReplicaOrbitFourColorSlotStateOfTag_color,
      lpReplicaOrbitFourColorSlotReflectRowToggle_color,
      lpReplicaOrbitFourColorSlotStateOfTag_color]
    simp only [lpReplicaTransportTag]
    rw [hpre, hsource,
      lpReplicaSingletonFalseRowTag_equivFin4]
    change (if Eraw (Es.symm x.1) = Eraw c then _ else _) = _
    by_cases hxc : Es.symm x.1 = c
    · rw [if_pos (congrArg Eraw hxc), if_pos (hrow.mpr hxc)]
    · rw [if_neg (fun h => hxc (Eraw.injective h)),
        if_neg (fun hx => hxc (hrow.mp hx))]

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagDecoratedSourceCanonicalSingletonStrictRoute_slotState
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hraw : LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
          (Finset.univ \ {d}))
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d}))
      A B
      (lpReplicaSingletonFalseRowTag
        (lpReplicaPartialReflectCopyEquivRaw
          G sites z.1.1.1 {d} c)))
    (hsource : ∀ e,
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e =
        (true, false)) :
    let atom := lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
      G sites q z.1.1.1 z.1.1.2 z.2.2 {d}
      (lpReplicaSingletonFalseRowTag
        (lpReplicaPartialReflectCopyEquivRaw
          G sites z.1.1.1 {d} c)) A B hraw
    lpReplicaOrientedFourColorSlotState G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
          (B.map lpReplicaCurrentReflect.toEmbedding) q atom) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {d})
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {c})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  dsimp only
  rw [lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState]
  rw [lpReplicaStrictRouteSingletonTag_slotState G sites q z.1.1.1
    z.1.1.2 z.2.2 c d
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 hsource]
  exact congrArg
    (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {d})
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c}))
    (lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData
      G sites i j q z).symm




theorem lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (spatialZ rowZ spatialW rowW :
      Finset (LPReplicaOrbitCommonSlot G sites q))
    (targetZ targetW : LPReplicaOrbitFourColorSlotState G sites q)
    (hz : targetZ =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatialZ rowZ
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
    (hw : targetW =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatialW rowW
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w))
    (hspatial : spatialZ = spatialW) (hrow : rowZ = rowW)
    (htarget : targetZ = targetW) :
    z = w := by
  subst spatialW
  subst rowW
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  apply (lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
    G sites q spatialZ rowZ).injective
  exact hz.symm.trans (htarget.trans hw)



abbrev LPReplicaStrictRouteMaskKey
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  ↑((Finset.univ : Finset (LPReplicaOrbitCommonSlot G sites q)).offDiag)



theorem card_lpReplicaStrictRouteMaskKey_rankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Fintype.card (LPReplicaStrictRouteMaskKey G sites q) = 20 := by
  calc
    Fintype.card (LPReplicaStrictRouteMaskKey G sites q) =
        ((Finset.univ : Finset
          (LPReplicaOrbitCommonSlot G sites q)).offDiag).card :=
      Fintype.card_coe _
    _ = 20 := by
      rw [Finset.offDiag_card, Finset.card_univ, hcard]




structure LPReplicaStrictRouteStateFamily
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Source Target : Type*) where
  source : Source ↪ LPReplicaOffdiagDecoratedSource G sites i j q
  spatialSlot : Source -> LPReplicaOrbitCommonSlot G sites q
  rowSlot : Source -> LPReplicaOrbitCommonSlot G sites q
  target : Source -> Target
  targetState : Target -> LPReplicaOrbitFourColorSlotState G sites q
  slots_ne : ∀ x, spatialSlot x ≠ rowSlot x
  output_state : ∀ x,
    targetState (target x) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
        {spatialSlot x} {rowSlot x}
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (source x))


noncomputable def LPReplicaStrictRouteStateFamily.routeKey
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target) (x : Source) :
    LPReplicaStrictRouteMaskKey G sites q :=
  ⟨(F.spatialSlot x, F.rowSlot x), by
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact F.slots_ne x⟩


noncomputable def
    LPReplicaStrictRouteStateFamily.targetFiberRouteKeyEmbedding
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target) (t : Target) :
    {x : Source // F.target x = t} ↪
      LPReplicaStrictRouteMaskKey G sites q where
  toFun := fun x => F.routeKey x.1
  inj' := by
    intro x y hkey
    apply Subtype.ext
    apply F.source.injective
    have hpair := congrArg Subtype.val hkey
    have hspatial := congrArg Prod.fst hpair
    have hrow := congrArg Prod.snd hpair
    apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
      G sites i j q (F.source x.1) (F.source y.1)
      {F.spatialSlot x.1} {F.rowSlot x.1}
      {F.spatialSlot y.1} {F.rowSlot y.1}
      (F.targetState (F.target x.1)) (F.targetState (F.target y.1))
      (F.output_state x.1) (F.output_state y.1)
    · exact congrArg
        (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
        hspatial
    · exact congrArg
        (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
        hrow
    · exact congrArg F.targetState (x.2.trans y.2.symm)



theorem LPReplicaStrictRouteStateFamily.target_fiber_card_le_twenty
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*} [Fintype Source] [DecidableEq Target]
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (t : Target) :
    Fintype.card {x : Source // F.target x = t} ≤ 20 := by
  classical
  calc
    Fintype.card {x : Source // F.target x = t} ≤
        Fintype.card (LPReplicaStrictRouteMaskKey G sites q) :=
      Fintype.card_le_of_embedding (F.targetFiberRouteKeyEmbedding t)
    _ = 20 := card_lpReplicaStrictRouteMaskKey_rankFive G sites q hcard



theorem LPReplicaStrictRouteStateFamily.rowSlot_eq_of_target_eq
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hsourceRow : ∀ x,
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (F.source x)) = Finset.univ)
    {x y : Source} (htarget : F.target x = F.target y) :
    F.rowSlot x = F.rowSlot y := by
  have hstate := congrArg F.targetState htarget
  rw [F.output_state x, F.output_state y] at hstate
  have hmask := congrArg
    (lpReplicaOrbitFourColorSlotRowMask G sites q) hstate
  rw [lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    hsourceRow x, hsourceRow y] at hmask
  exact Finset.singleton_injective
    (symmDiff_right_injective (Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q)) hmask)




theorem LPReplicaStrictRouteStateFamily.eq_of_spatialSlot_eq_of_target_eq
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hsourceRow : ∀ x,
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (F.source x)) = Finset.univ)
    {x y : Source} (hspatial : F.spatialSlot x = F.spatialSlot y)
    (htarget : F.target x = F.target y) : x = y := by
  apply F.source.injective
  apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
    G sites i j q (F.source x) (F.source y)
    {F.spatialSlot x} {F.rowSlot x}
    {F.spatialSlot y} {F.rowSlot y}
    (F.targetState (F.target x)) (F.targetState (F.target y))
    (F.output_state x) (F.output_state y)
  · exact congrArg
      (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
      hspatial
  · exact congrArg
      (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
      (F.rowSlot_eq_of_target_eq hsourceRow htarget)
  · exact congrArg F.targetState htarget



theorem LPReplicaStrictRouteStateFamily.saturated_target_fiber_card_le_four
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*} [Fintype Source] [DecidableEq Target]
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hsourceRow : ∀ x,
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (F.source x)) = Finset.univ)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (t : Target) :
    Fintype.card {x : Source // F.target x = t} ≤ 4 := by
  classical
  let Fiber := {x : Source // F.target x = t}
  by_cases hne : Nonempty Fiber
  · let base : Fiber := Classical.choice hne
    let encode : Fiber ↪
        {d : LPReplicaOrbitCommonSlot G sites q //
          d ≠ F.rowSlot base.1} :=
      {
        toFun := fun x => ⟨F.spatialSlot x.1, by
          intro hspatialRow
          apply F.slots_ne x.1
          exact hspatialRow.trans
            (F.rowSlot_eq_of_target_eq hsourceRow
              (x.2.trans base.2.symm)).symm⟩
        inj' := by
          intro x y h
          apply Subtype.ext
          apply F.eq_of_spatialSlot_eq_of_target_eq hsourceRow
          · exact congrArg Subtype.val h
          · exact x.2.trans y.2.symm
      }
    calc
      Fintype.card Fiber ≤
          Fintype.card {d : LPReplicaOrbitCommonSlot G sites q //
            d ≠ F.rowSlot base.1} :=
        Fintype.card_le_of_embedding encode
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 1 :=
        Set.card_ne_eq (F.rowSlot base.1)
      _ = 4 := by omega
  · have hi : IsEmpty Fiber := not_nonempty_iff.mp hne
    rw [(Fintype.card_eq_zero_iff.mpr hi)]
    omega


theorem LPReplicaStrictRouteStateFamily.card_le_twenty_mul_target
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Fintype.card Source ≤ 20 * Fintype.card Target := by
  let encode : Source ↪
      LPReplicaStrictRouteMaskKey G sites q × Target :=
    {
      toFun := fun x => (F.routeKey x, F.target x)
      inj' := by
        intro x y h
        apply F.source.injective
        have hkey := congrArg Prod.fst h
        have htarget := congrArg Prod.snd h
        have hpair := congrArg Subtype.val hkey
        apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
          G sites i j q (F.source x) (F.source y)
          {F.spatialSlot x} {F.rowSlot x}
          {F.spatialSlot y} {F.rowSlot y}
          (F.targetState (F.target x)) (F.targetState (F.target y))
          (F.output_state x) (F.output_state y)
        · exact congrArg
            (fun s : LPReplicaOrbitCommonSlot G sites q =>
              ({s} : Finset _))
            (congrArg Prod.fst hpair)
        · exact congrArg
            (fun s : LPReplicaOrbitCommonSlot G sites q =>
              ({s} : Finset _))
            (congrArg Prod.snd hpair)
        · exact congrArg F.targetState htarget
    }
  calc
    Fintype.card Source ≤
        Fintype.card (LPReplicaStrictRouteMaskKey G sites q × Target) :=
      Fintype.card_le_of_embedding encode
    _ = Fintype.card (LPReplicaStrictRouteMaskKey G sites q) *
        Fintype.card Target := Fintype.card_prod _ _
    _ = 20 * Fintype.card Target := by
      rw [card_lpReplicaStrictRouteMaskKey_rankFive G sites q hcard]

end

end StatMech.Ising
