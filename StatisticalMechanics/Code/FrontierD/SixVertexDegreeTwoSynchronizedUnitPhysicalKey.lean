/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector










namespace StatMech.FrontierD

noncomputable section

local instance synchronizedUnitPhysicalKeyPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p




theorem finitePerm_function_invariant_of_firstReturn
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (selected : A → Prop) [DecidablePred selected]
    (f : A → B)
    (hreturn : ∀ x : {a : A // selected a},
      f (finiteFirstReturn sigma selected x) = f x.1)
    (hinactive : ∀ x : A, ¬ selected x → f (sigma x) = f x) :
    ∀ x : A, f (sigma x) = f x := by
  intro x
  by_cases hx : selected x
  · let active : {a : A // selected a} := ⟨x, hx⟩
    let n := finiteFirstReturnTime sigma selected active
    have hnpos : 0 < n := finiteFirstReturnTime_pos sigma selected active
    have htail : ∀ k : Nat, 0 < k → k ≤ n →
        f ((sigma ^ k) x) = f (sigma x) := by
      intro k hkpos hkn
      induction k using Nat.case_strong_induction_on with
      | hz => omega
      | hi k ih =>
          by_cases hk : k = 0
          · subst k
            simp
          · have hkpos' : 0 < k := Nat.pos_of_ne_zero hk
            have hklt : k < n := by omega
            have hknot : ¬ selected ((sigma ^ k) x) := by
              intro hkselected
              exact (finiteFirstReturnTime_minimal sigma selected active k
                hklt) ⟨hkpos', hkselected⟩
            calc
              f ((sigma ^ (k + 1)) x) = f (sigma ((sigma ^ k) x)) := by
                rw [pow_succ']
                rfl
              _ = f ((sigma ^ k) x) := hinactive _ hknot
              _ = f (sigma x) := ih k (by omega) hkpos' (by omega)
    have hfirst := htail n hnpos (le_refl n)
    have hreturn' : f ((sigma ^ n) x) = f x := by
      simpa [active, n, finiteFirstReturn] using hreturn active
    exact hfirst.symm.trans hreturn'
  · exact hinactive x hx



theorem finitePerm_function_invariant_of_firstReturn_of_inactive_arrival
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (selected : A → Prop) [DecidablePred selected]
    (f : A → B)
    (hreturn : ∀ x : {a : A // selected a},
      f (finiteFirstReturn sigma selected x) = f x.1)
    (hinactiveArrival : ∀ x : A,
      ¬ selected (sigma x) → f (sigma x) = f x) :
    ∀ x : A, f (sigma x) = f x := by
  intro x
  by_cases harrival : selected (sigma x)
  · let y : {a : A // selected a} := ⟨sigma x, harrival⟩
    let z := (finiteFirstReturnPerm sigma selected).symm y
    let n := finiteFirstReturnTime sigma selected z
    have hnpos : 0 < n := finiteFirstReturnTime_pos sigma selected z
    have hreturnPoint : finiteFirstReturn sigma selected z = y := by
      change finiteFirstReturnPerm sigma selected z = y
      simp [z]
    have hlast : (sigma ^ (n - 1)) z.1 = x := by
      apply sigma.injective
      calc
        sigma ((sigma ^ (n - 1)) z.1) = (sigma ^ n) z.1 := by
          rw [show n = (n - 1) + 1 by omega, pow_succ']
          rfl
        _ = y.1 := congrArg Subtype.val hreturnPoint
        _ = sigma x := rfl
    have hprefix : ∀ k : Nat, k < n →
        f ((sigma ^ k) z.1) = f z.1 := by
      intro k hk
      induction k using Nat.case_strong_induction_on with
      | hz => simp
      | hi k ih =>
          have hpos : 0 < k + 1 := by omega
          have hnot : ¬ selected ((sigma ^ (k + 1)) z.1) := by
            intro hselected
            exact (finiteFirstReturnTime_minimal sigma selected z (k + 1)
              hk) ⟨hpos, hselected⟩
          calc
            f ((sigma ^ (k + 1)) z.1) = f (sigma ((sigma ^ k) z.1)) := by
              rw [pow_succ']
              rfl
            _ = f ((sigma ^ k) z.1) := by
              apply hinactiveArrival
              simpa [pow_succ'] using hnot
            _ = f z.1 := ih k (by omega) (by omega)
    have hxcolor : f x = f z.1 := by
      rw [← hlast]
      exact hprefix (n - 1) (by omega)
    have hycolor : f y.1 = f z.1 := by
      rw [← hreturnPoint]
      exact hreturn z
    exact hycolor.trans hxcolor.symm
  · exact hinactiveArrival x harrival



noncomputable def sixVertexDegreeTwoSynchronizedComponentTransitionVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (v : T.Vertex) : Bool :=
  if hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
      component
      (orientedDisagreementDartAtActiveVertex homega heta v hactive, false)
  else false

theorem sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree
        component (doubledAlignedVertex x) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (x.1, false) := by
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x))
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x))).card = 2 := by
    simpa [doubledAlignedVertex] using
      (sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1)
  let dart := orientedDisagreementDartAtActiveVertex homega heta
    (doubledAlignedVertex x) hactive
  have hdart : dart = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree dart x.1 rfl
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionVertex
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta
      (doubledAlignedVertex x) hactive = x.1 at hdart
  rw [hdart]



theorem sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree
        component (doubledAlignedVertex x) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component x := by
  rw [sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active]
  rcases x with ⟨dart, branch⟩
  cases branch
  · rfl
  · exact sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches
      homega heta hdegree component dart



noncomputable def sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (v : T.Vertex) : Bool :=
  if hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component
        (orientedDisagreementDartAtActiveVertex homega heta v hactive) &&
      ((orientedDartAlignedRetie homega heta hdegree
        (orientedDisagreementDartAtActiveVertex homega heta v hactive)).pairingP !=
       (orientedDartAlignedRetie homega heta hdegree
        (orientedDisagreementDartAtActiveVertex homega heta v hactive)).pairingQ)
  else false

theorem sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex homega heta
        hdegree component (doubledAlignedVertex x) =
      (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
          component x &&
        ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ)) := by
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x))
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x))).card = 2 := by
    simpa [doubledAlignedVertex] using
      (sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1)
  let dart := orientedDisagreementDartAtActiveVertex homega heta
    (doubledAlignedVertex x) hactive
  have hdart : dart = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree dart x.1 rfl
  unfold sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta
      (doubledAlignedVertex x) hactive = x.1 at hdart
  rw [hdart]



noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (_layer : Bool) (v : T.Vertex) : Bool :=
  sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree
      component v !=
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex homega heta
      hdegree component v

theorem sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree
        component layer (doubledAlignedVertex x) =
      (sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
          component x !=
        (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
            hdegree component x &&
          ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask,
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch,
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active]

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree
      component layer v = false := by
  have hnot : ¬ (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 := by omega
  simp [sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask,
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex,
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex, hnot]



noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) : FKMedialLoopPairing T :=
  fkMedialTogglePairingMask
    (alignedRoutingLoopPairing homega heta hdegree layer)
    (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree
      component layer)


theorem sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    let sourcePairing := if layer then retie.pairingQ else retie.pairingP
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer (doubledAlignedVertex x) =
      if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
          hdegree component layer (doubledAlignedVertex x) then
        !sourcePairing
      else sourcePairing := by
  dsimp only
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x))
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x))).card = 2 := by
    simpa [doubledAlignedVertex] using
      (sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1)
  let dart := orientedDisagreementDartAtActiveVertex homega heta
    (doubledAlignedVertex x) hactive
  have hdart : dart = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree dart x.1 rfl
  let retie := orientedDartAlignedRetie homega heta hdegree dart
  have hsource := alignedRoutingPairing_eq_at_active homega heta hdegree layer
    (doubledAlignedVertex x) hactive
  change alignedRoutingLoopPairing homega heta hdegree layer
      (doubledAlignedVertex x) =
    (if layer then retie.pairingQ else retie.pairingP) at hsource
  dsimp only [retie] at hsource
  rw [hdart] at hsource
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing,
    fkMedialTogglePairingMask, hsource]


theorem sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer v =
      alignedRoutingLoopPairing homega heta hdegree layer v := by
  simp [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing,
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega
      heta hdegree component layer v hzero, fkMedialTogglePairingMask]


@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) :
    fkMedialTogglePairingMask
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer)
        (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
          hdegree component layer) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  exact fkMedialTogglePairingMask_self _ _



theorem sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer) =
      (fkColoredParityMaskStrandSlotSwap
          (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
            hdegree component layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
          (fkColoredParityMaskStrandSlotSwap
            (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
              heta hdegree component layer) true)) := by
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _




theorem sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
      heta hdegree component layer
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm
          (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
            heta hdegree component layer))
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  classical
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  have hreturn := finiteFirstReturn_togglePairingMask_active
    (alignedRoutingLoopPairing homega heta hdegree layer) mask
    (fun d hd => by
      have hzero := (hdegree d.1.1).resolve_right hd
      exact sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive
        homega heta hdegree component layer d.1.1 hzero) dart hactive
  simpa [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing, mask]
    using hreturn



noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalInputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
      hdegree component layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == false) then
    doubledAlignedBranchSwap x else x


noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (_component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if layer then
    sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x
  else doubledAlignedFirstReturnPerm homega heta hdegree x



theorem sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer
        (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState
          homega heta hdegree component layer x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  cases layer
  · simpa [sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState,
      sixVertexDegreeTwoAlignedActiveColor] using
      (sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
        homega heta hdegree x).symm
  · let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    let retie := orientedDartAlignedRetie homega heta hdegree y.1
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true
      homega heta hdegree x
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x =
      if retie.pairingP = retie.pairingQ then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true y
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap y) at h
    rw [sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState,
      if_pos rfl, sixVertexDegreeTwoAlignedTrueFirstReturnState]
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y) = _
    by_cases heq : retie.pairingP = retie.pairingQ
    · rw [if_pos heq] at h ⊢
      exact h.symm
    · rw [if_neg heq] at h ⊢
      exact h.symm



noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
      hdegree component layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == true) then
    doubledAlignedBranchSwap x else x


noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState homega heta hdegree
    component layer
    (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState homega
      heta hdegree component layer
      (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
        hdegree component layer x))

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
          hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalInputState
  split
  · exact sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
      homega heta hdegree component x
  · rfl

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState homega heta
          hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState
  split
  · exact sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
      homega heta hdegree component x
  · rfl

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · simp [sixVertexDegreeTwoTauAdjustedState, retie, heq]
  · simpa [sixVertexDegreeTwoTauAdjustedState, retie, heq] using
      (sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
        homega heta hdegree component x)

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState
          homega heta hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  cases layer
  · rfl
  · exact sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted
      homega heta hdegree component
      (doubledAlignedFirstReturnPerm homega heta hdegree x)

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta
          hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (doubledAlignedFirstReturnPerm homega heta hdegree
          (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
            hdegree component layer x)) := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
  rw [sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState,
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState]



theorem sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta
          hdegree component layer x) !=
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (doubledAlignedFirstReturnPerm homega heta hdegree
          (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
            hdegree component layer x)) := by
  rw [sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState]
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionBit
  rw [Equiv.symm_apply_apply,
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState]



theorem sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer)
        ((finiteFirstReturn
          (fkMedialBlackBoundaryPerm
            (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
              homega heta hdegree component layer))
          (activeBlackDart (omega := omega) (eta := eta))
          ⟨dart, hactive⟩).1) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega
            heta hdegree component layer x),
        doubledAlignedSlot homega heta hdegree layer
          (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega
            heta hdegree component layer x)) := by
  classical
  let sourcePairing := alignedRoutingLoopPairing homega heta hdegree layer
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  let targetPairing :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
      hdegree component layer
  let input := sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega
    heta hdegree component layer x
  let returned :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState homega
      heta hdegree component layer input
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hpairing : targetPairing =
      fkMedialTogglePairingMask sourcePairing mask := rfl
  have hdart : dart =
      (fkColoredBlackDartStrandSlotEquiv targetPairing).symm
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
    apply (fkColoredBlackDartStrandSlotEquiv targetPairing).injective
    simpa [targetPairing] using hslot
  have hswapped : swapped =
      doubledAlignedBlackDart homega heta hdegree layer input := by
    dsimp only [swapped]
    rw [hdart, hpairing]
    exact fkMedialBlackDartMaskSwap_canonicalTargetState homega heta hdegree
      mask layer x
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped :=
    (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  have hstart :
      (⟨swapped, hswappedActive⟩ : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) =
      doubledAlignedBlackDartEquiv homega heta hdegree layer input := by
    apply Subtype.ext
    exact hswapped
  have hsourceReturn :
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, hswappedActive⟩).1 =
      doubledAlignedBlackDart homega heta hdegree layer returned := by
    rw [hstart]
    cases layer
    · exact congrArg Subtype.val
        (doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree
          input).symm
    · exact congrArg Subtype.val
        (sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree
          input)
  have htargetReturn :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active homega
      heta hdegree component layer dart hactive
  change (finiteFirstReturn
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1 =
    (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨swapped, hswappedActive⟩).1 at htargetReturn
  change fkColoredBlackDartStrandSlotEquiv targetPairing
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1) = _
  rw [htargetReturn, hsourceReturn, hpairing,
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask]
  simp only [Equiv.trans_apply]
  have hcoordinate :
      fkColoredBlackDartStrandSlotEquiv sourcePairing
          (doubledAlignedBlackDart homega heta hdegree layer returned) =
        (doubledAlignedVertex returned,
          doubledAlignedSlot homega heta hdegree layer returned) :=
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  rw [hcoordinate,
    fkColoredParityMaskStrandSlotSwap_doubledAlignedState]
  rfl


noncomputable def sixVertexDegreeTwoSynchronizedComponentStates
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    List (DoubledAlignedState omega eta) :=
  (Finset.univ.filter fun x =>
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
      component x = true).toList

@[simp] theorem sixVertexDegreeTwoSynchronizedComponent_mem_states_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    x ∈ sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component ↔
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
        hdegree component x = true := by
  simp [sixVertexDegreeTwoSynchronizedComponentStates]

theorem sixVertexDegreeTwoSynchronizedComponent_states_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
      component).Nodup := by
  exact Finset.nodup_toList _

theorem sixVertexDegreeTwoSynchronizedComponent_branchSwap_mem_states_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap x ∈
        sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
          component ↔
      x ∈ sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component := by
  simp only [sixVertexDegreeTwoSynchronizedComponent_mem_states_iff]
  rw [sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap]



abbrev SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :=
  {dart : FKMedialBlackDart T // dart ∈
    doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)}


noncomputable def sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool)
    (i : Fin (Fintype.card
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component))) : T.Vertex × Bool :=
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer
    ((Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component)).symm i).1

theorem sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
      hdegree component)).symm.injective
  apply Subtype.ext
  unfold sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey at heq
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective heq
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective heq



noncomputable def sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  fkIndexedOccurrenceSlotEquiv
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component))
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree
      component)
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
      heta hdegree component)

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (slot : FKLayeredStrandSlot T) :
    sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component slot) = slot := by
  exact fkIndexedOccurrenceSlotEquiv_apply_self _ _ _ slot


theorem sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    (∃ i, sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
          component) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence :
        SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component :=
      (Fintype.equivFin
        (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component)).symm i
    have hdart : occurrence.1 = dart := by
      cases layer
      · exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective hi
      · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence :
        SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component := ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)



theorem sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)) :
    sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
        component
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree (!layer) dart) := by
  classical
  let occurrence :
      SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component := ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
      hdegree component) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
          hdegree component currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          currentLayer dart := by
    unfold sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv,
    fkIndexedOccurrenceSlotEquiv_apply_key, hkey]



theorem sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)) :
    sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
        component
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree layer dart) := by
  unfold sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart
    ((sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff homega
      heta hdegree component layer dart).mp hexists)



noncomputable def sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) : Bool :=
  fkColoredLayeredSlotColor
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
      component
      (layer, doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))


theorem sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
          false
          (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
            component) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)
  · rw [dif_pos hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply homega heta
        hdegree component layer dart hdart)
  · rw [dif_neg hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem
        homega heta hdegree component layer dart hdart)


theorem
    sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) dart) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) := by
  classical
  rw [sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta
    hdegree component layer dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl



theorem
    sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (alignedBoundaryPerm homega heta hdegree false dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  classical
  let states := sixVertexDegreeTwoSynchronizedComponentStates homega heta
    hdegree component
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmem : next ∈ doubledAlignedBoundarySegments homega heta hdegree false
        states ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false states :=
    mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false states dart hinactive
  rw [sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta
      hdegree component layer next,
    sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta
      hdegree component layer dart]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false states
  · have hnext : next ∈ doubledAlignedBoundarySegments homega heta hdegree
        false states := hmem.mpr hdart
    rw [dif_pos hnext, dif_pos hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree (!layer) dart hinactive
  · have hnext : next ∉ doubledAlignedBoundarySegments homega heta hdegree
        false states := fun h => hdart (hmem.mp h)
    rw [dif_neg hnext, dif_neg hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree layer dart hinactive


noncomputable def sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) : FKMedialBlackDart T :=
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  let input := sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
    mask false layer dart
  let arrival := alignedBoundaryPerm homega heta hdegree false input
  let common := if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm arrival
    else arrival
  sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask true
    layer common



theorem
    sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : ¬ activeBlackDart (omega := omega) (eta := eta) dart)
    (hnext : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta
        hdegree component layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  have hzeroD := (hdegree dart.1.1).resolve_right hdart
  have hmaskD : mask dart.1.1 = false :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega
      heta hdegree component layer dart.1.1 hzeroD
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hzeroNext := (hdegree next.1.1).resolve_right hnext
  have hmaskNext : mask next.1.1 = false :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega
      heta hdegree component layer next.1.1 hzeroNext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]



theorem
    sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer
        (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta
          hdegree component layer dart) := by
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl



theorem
    sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
                homega heta hdegree component layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component)
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component))
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component)
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
        heta hdegree component) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot homega heta hdegree
    layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  change fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
        hdegree component
        (fkColoredLayeredStrandSlotBoundaryPerm
          (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
            heta hdegree component) (layer, slot))) = _
  rw [← hslot, fkColoredLayeredStrandSlotBoundaryPerm_apply,
    sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart]
  exact hfalseDart layer dart



theorem sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) →
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
                homega heta hdegree component layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component)
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component))
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component)
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
        heta hdegree component) := by
  apply sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart
    homega heta hdegree component
  intro layer dart
  by_cases hdart : activeBlackDart (omega := omega) (eta := eta) dart
  · exact hactive layer dart (Or.inl hdart)
  · by_cases hnext : activeBlackDart (omega := omega) (eta := eta)
        (alignedBoundaryPerm homega heta hdegree false dart)
    · exact hactive layer dart (Or.inr hnext)
    · rw [sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive
        homega heta hdegree component layer dart hdart hnext]
      exact
        sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive
          homega heta hdegree component layer dart hnext



noncomputable def sixVertexDegreeTwoSynchronizedComponentSpliceOfActive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) →
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
                homega heta hdegree component layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredStrandSplice
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  fkColoredSlotColorInvariantSplice
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
      hdegree component)
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component))
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree
      component)
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
      heta hdegree component)
    (sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active homega
      heta hdegree component hactive)


theorem sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor homega heta
        hdegree component layer x =
      if sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
          hdegree component x then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) x
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  classical
  unfold sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
  rw [← sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
      homega heta hdegree layer x]
  have hmem := doubledAlignedBlackDart_mem_boundarySegments_iff
    homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component) x
  by_cases hx : sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega
      heta hdegree component x = true
  · rw [if_pos hx,
      sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply homega heta
        hdegree component layer _
        (hmem.mpr (sixVertexDegreeTwoSynchronizedComponent_mem_states_iff
          homega heta hdegree component x |>.mpr hx))]
    simp [sixVertexDegreeTwoAlignedActiveColor]
  · have hxBool :
        sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
          hdegree component x = false := Bool.eq_false_of_not_eq_true hx
    rw [if_neg hx,
      sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem
        homega heta hdegree component layer _
        (fun hdart => hx
          ((sixVertexDegreeTwoSynchronizedComponent_mem_states_iff homega heta
            hdegree component x).mp (hmem.mp hdart)))]
    simp [sixVertexDegreeTwoAlignedActiveColor]


def SixVertexDegreeTwoSynchronizedComponentActiveReturnColorInvariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Prop :=
  ∀ (layer : Bool) (x : DoubledAlignedState omega eta),
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor homega heta
        hdegree component layer
        (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega
          heta hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor homega heta
        hdegree component layer x



theorem sixVertexDegreeTwoSynchronizedComponentTransportedColor_firstReturn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hreturn :
      SixVertexDegreeTwoSynchronizedComponentActiveReturnColorInvariant homega
        heta hdegree component)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer))
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
              homega heta hdegree component layer) arrival)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
              homega heta hdegree component layer) dart)) := by
  dsimp only
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot homega
      heta hdegree component layer x dart hactive hslot,
    hslot]
  exact hreturn layer x

end

end StatMech.FrontierD
