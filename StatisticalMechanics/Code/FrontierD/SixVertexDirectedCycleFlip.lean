/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLocalDisagreementSwitch
import Code.FrontierD.FKMedialLoopTopology
import Code.FrontierD.SixVertexDegreeTwoDisagreementStrand











namespace StatMech.FrontierD

noncomputable section

local instance sixVertexDirectedCycleFlipPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


def sixVertexLocalFlipMask
    (pattern mask : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern :=
  fun side => if mask side then !pattern side else pattern side


def sixVertexLocalSelectedIncomingCount
    (pattern mask : SixVertexLocalIncomingPattern) : Nat :=
  ∑ side, if mask side then (pattern side).toNat else 0



theorem sixVertexLocalFlipMask_ice
    (pattern mask : SixVertexLocalIncomingPattern)
    (hice : pattern.Ice)
    (hmask : sixVertexLocalSwitchMaskCount mask = 0 \/
      (sixVertexLocalSwitchMaskCount mask = 2 /\
        sixVertexLocalSelectedIncomingCount pattern mask = 1)) :
    (sixVertexLocalFlipMask pattern mask).Ice := by
  decide +revert



theorem sixVertexLocalSelectedIncomingCount_flip
    (pattern mask : SixVertexLocalIncomingPattern)
    (htwo : sixVertexLocalSwitchMaskCount mask = 2)
    (hone : sixVertexLocalSelectedIncomingCount pattern mask = 1) :
    sixVertexLocalSelectedIncomingCount
        (sixVertexLocalFlipMask pattern mask) mask = 1 := by
  decide +revert




def SixVertexLocalBalancedFlipMask
    (pattern mask : SixVertexLocalIncomingPattern) : Prop :=
  2 * sixVertexLocalSelectedIncomingCount pattern mask =
    sixVertexLocalSwitchMaskCount mask


theorem sixVertexLocalFlipMask_ice_of_balanced
    (pattern mask : SixVertexLocalIncomingPattern)
    (hice : pattern.Ice)
    (hbalanced : SixVertexLocalBalancedFlipMask pattern mask) :
    (sixVertexLocalFlipMask pattern mask).Ice := by
  simp only [SixVertexLocalBalancedFlipMask,
    SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalIncomingCount,
    sixVertexLocalFlipMask] at *
  decide +revert


theorem SixVertexLocalBalancedFlipMask.after_flip
    (pattern mask : SixVertexLocalIncomingPattern)
    (hbalanced : SixVertexLocalBalancedFlipMask pattern mask) :
    SixVertexLocalBalancedFlipMask
      (sixVertexLocalFlipMask pattern mask) mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalFlipMask] at *
  decide +revert



theorem sixVertexLocalBalancedFlipMask_of_ice_flip
    (pattern mask : SixVertexLocalIncomingPattern)
    (hice : pattern.Ice)
    (hflip : (sixVertexLocalFlipMask pattern mask).Ice) :
    SixVertexLocalBalancedFlipMask pattern mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalIncomingCount,
    sixVertexLocalFlipMask] at *
  decide +revert



theorem sixVertexLocalBalancedFlipMask_of_cycle
    (pattern mask : SixVertexLocalIncomingPattern)
    (hmask : sixVertexLocalSwitchMaskCount mask = 0 \/
      (sixVertexLocalSwitchMaskCount mask = 2 /\
        sixVertexLocalSelectedIncomingCount pattern mask = 1)) :
    SixVertexLocalBalancedFlipMask pattern mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount] at *
  decide +revert


def sixVertexTorusFlip
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    SixVertexArrows T where
  horizontal edge := if mask.horizontal edge then !omega.horizontal edge
    else omega.horizontal edge
  vertical edge := if mask.vertical edge then !omega.vertical edge
    else omega.vertical edge


def sixVertexTorusMaskXor
    {T : EvenTorus} (first second : SixVertexArrows T) :
    SixVertexArrows T where
  horizontal edge := first.horizontal edge != second.horizontal edge
  vertical edge := first.vertical edge != second.vertical edge


theorem sixVertexTorusFlip_maskXor
    {T : EvenTorus} (first second omega : SixVertexArrows T) :
    sixVertexTorusFlip second (sixVertexTorusFlip first omega) =
      sixVertexTorusFlip (sixVertexTorusMaskXor first second) omega := by
  ext edge
  · cases hfirst : first.horizontal edge <;>
      cases hsecond : second.horizontal edge <;>
      cases harrow : omega.horizontal edge <;>
      simp [sixVertexTorusFlip, sixVertexTorusMaskXor,
        hfirst, hsecond, harrow]
  · cases hfirst : first.vertical edge <;>
      cases hsecond : second.vertical edge <;>
      cases harrow : omega.vertical edge <;>
      simp [sixVertexTorusFlip, sixVertexTorusMaskXor,
        hfirst, hsecond, harrow]


@[simp] theorem sixVertexTorusFlip_self
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    sixVertexTorusFlip mask (sixVertexTorusFlip mask omega) = omega := by
  ext edge
  · cases h : mask.horizontal edge <;> simp [sixVertexTorusFlip, h]
  · cases h : mask.vertical edge <;> simp [sixVertexTorusFlip, h]

@[simp] theorem sixVertexTorusFlip_horizontal_selected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hselected : mask.horizontal edge = true) :
    (sixVertexTorusFlip mask omega).horizontal edge =
      !omega.horizontal edge := by
  simp [sixVertexTorusFlip, hselected]

@[simp] theorem sixVertexTorusFlip_horizontal_unselected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hunselected : mask.horizontal edge = false) :
    (sixVertexTorusFlip mask omega).horizontal edge =
      omega.horizontal edge := by
  simp [sixVertexTorusFlip, hunselected]

@[simp] theorem sixVertexTorusFlip_vertical_selected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hselected : mask.vertical edge = true) :
    (sixVertexTorusFlip mask omega).vertical edge =
      !omega.vertical edge := by
  simp [sixVertexTorusFlip, hselected]

@[simp] theorem sixVertexTorusFlip_vertical_unselected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hunselected : mask.vertical edge = false) :
    (sixVertexTorusFlip mask omega).vertical edge =
      omega.vertical edge := by
  simp [sixVertexTorusFlip, hunselected]



theorem sixVertexLocalIncomingPattern_torusFlip
    {T : EvenTorus} (mask omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexLocalIncomingPattern (sixVertexTorusFlip mask omega) v =
      sixVertexLocalFlipMask (sixVertexLocalIncomingPattern omega v)
        (sixVertexTorusLocalSwitchMask mask v) := by
  funext side
  fin_cases side <;>
    simp [sixVertexLocalIncomingPattern, sixVertexTorusFlip,
      sixVertexTorusLocalSwitchMask, sixVertexLocalFlipMask,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming] <;>
    split <;> simp_all



def SixVertexDirectedCycleFlipMask
    {T : EvenTorus} (omega mask : SixVertexArrows T) : Prop :=
  forall v,
    sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask mask v) = 0 \/
      (sixVertexLocalSwitchMaskCount
            (sixVertexTorusLocalSwitchMask mask v) = 2 /\
        sixVertexLocalSelectedIncomingCount
            (sixVertexLocalIncomingPattern omega v)
            (sixVertexTorusLocalSwitchMask mask v) = 1)



def SixVertexBalancedFlipMask
    {T : EvenTorus} (omega mask : SixVertexArrows T) : Prop :=
  forall v, SixVertexLocalBalancedFlipMask
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)

theorem SixVertexDirectedCycleFlipMask.balanced
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (hmask : SixVertexDirectedCycleFlipMask omega mask) :
    SixVertexBalancedFlipMask omega mask := by
  intro v
  exact sixVertexLocalBalancedFlipMask_of_cycle _ _ (hmask v)


theorem sixVertexTorusFlip_ice_of_balanced
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (homega : omega.IceRule)
    (hmask : SixVertexBalancedFlipMask omega mask) :
    (sixVertexTorusFlip mask omega).IceRule := by
  intro v
  have hlocal := sixVertexLocalFlipMask_ice_of_balanced
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (hmask v)
  rw [SixVertexLocalIncomingPattern.Ice] at hlocal
  rw [← sixVertexLocalIncomingPattern_count,
    sixVertexLocalIncomingPattern_torusFlip]
  exact hlocal



theorem sixVertexBalancedFlipMask_of_ice_flip
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (homega : omega.IceRule)
    (hflip : (sixVertexTorusFlip mask omega).IceRule) :
    SixVertexBalancedFlipMask omega mask := by
  intro v
  apply sixVertexLocalBalancedFlipMask_of_ice_flip
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
  rw [← sixVertexLocalIncomingPattern_torusFlip]
  exact sixVertexLocalIncomingPattern_ice _ hflip v



theorem SixVertexBalancedFlipMask.maskXor
    {T : EvenTorus} {omega first second : SixVertexArrows T}
    (homega : omega.IceRule)
    (hfirst : SixVertexBalancedFlipMask omega first)
    (hsecond : SixVertexBalancedFlipMask
      (sixVertexTorusFlip first omega) second) :
    SixVertexBalancedFlipMask omega
      (sixVertexTorusMaskXor first second) := by
  apply sixVertexBalancedFlipMask_of_ice_flip homega
  rw [← sixVertexTorusFlip_maskXor]
  exact sixVertexTorusFlip_ice_of_balanced
    (sixVertexTorusFlip_ice_of_balanced homega hfirst) hsecond


theorem sixVertexTorusFlip_maskXor_eq
    {T : EvenTorus} (first second omega : SixVertexArrows T) :
    sixVertexTorusFlip (sixVertexTorusMaskXor first second) omega =
      sixVertexTorusFlip second (sixVertexTorusFlip first omega) :=
  (sixVertexTorusFlip_maskXor first second omega).symm


theorem SixVertexBalancedFlipMask.after_flip
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (hmask : SixVertexBalancedFlipMask omega mask) :
    SixVertexBalancedFlipMask (sixVertexTorusFlip mask omega) mask := by
  intro v
  rw [sixVertexLocalIncomingPattern_torusFlip]
  exact (hmask v).after_flip _ _


theorem sixVertexTorusFlip_ice
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (homega : omega.IceRule)
    (hmask : SixVertexDirectedCycleFlipMask omega mask) :
    (sixVertexTorusFlip mask omega).IceRule := by
  intro v
  have hlocal := sixVertexLocalFlipMask_ice
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (hmask v)
  rw [SixVertexLocalIncomingPattern.Ice] at hlocal
  rw [← sixVertexLocalIncomingPattern_count]
  rw [sixVertexLocalIncomingPattern_torusFlip]
  exact hlocal



theorem SixVertexDirectedCycleFlipMask.after_flip
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (hmask : SixVertexDirectedCycleFlipMask omega mask) :
    SixVertexDirectedCycleFlipMask (sixVertexTorusFlip mask omega) mask := by
  intro v
  rcases hmask v with hzero | ⟨htwo, hone⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨htwo, ?_⟩
    rw [sixVertexLocalIncomingPattern_torusFlip]
    exact sixVertexLocalSelectedIncomingCount_flip _ _ htwo hone


def sixVertexTorusAgreementMask
    {T : EvenTorus} (omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal edge := omega.horizontal edge == eta.horizontal edge
  vertical edge := omega.vertical edge == eta.vertical edge


def sixVertexLocalAgreementMask
    (first second : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern :=
  fun side => first side == second side

theorem sixVertexTorusLocalSwitchMask_agreement
    {T : EvenTorus} (omega eta : SixVertexArrows T) (v : T.Vertex) :
    sixVertexTorusLocalSwitchMask (sixVertexTorusAgreementMask omega eta) v =
      sixVertexLocalAgreementMask
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) := by
  funext side
  fin_cases side <;>
    simp [sixVertexTorusLocalSwitchMask, sixVertexTorusAgreementMask,
      sixVertexLocalAgreementMask, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming]



theorem sixVertexLocalAgreementMask_balanced
    (first second : SixVertexLocalIncomingPattern)
    (hfirst : first.Ice) (hsecond : second.Ice)
    (hdegree : (sixVertexLocalDisagreementSides first second).card = 0 \/
      (sixVertexLocalDisagreementSides first second).card = 2) :
    SixVertexLocalBalancedFlipMask first
      (sixVertexLocalAgreementMask first second) := by
  simp only [SixVertexLocalBalancedFlipMask,
    SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalIncomingCount,
    sixVertexLocalAgreementMask,
    sixVertexLocalDisagreementSides] at *
  decide +revert

theorem sixVertexLocalAgreementMask_comm
    (first second : SixVertexLocalIncomingPattern) :
    sixVertexLocalAgreementMask first second =
      sixVertexLocalAgreementMask second first := by
  funext side
  simp [sixVertexLocalAgreementMask, eq_comm]



theorem sixVertexTorusAgreementMask_balanced_first
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexBalancedFlipMask omega
      (sixVertexTorusAgreementMask omega eta) := by
  intro v
  rw [sixVertexTorusLocalSwitchMask_agreement]
  exact sixVertexLocalAgreementMask_balanced _ _
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (sixVertexLocalIncomingPattern_ice eta heta v)
    (hdegree v)


theorem sixVertexTorusAgreementMask_balanced_second
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexBalancedFlipMask eta
      (sixVertexTorusAgreementMask omega eta) := by
  intro v
  rw [sixVertexTorusLocalSwitchMask_agreement]
  have h := sixVertexLocalAgreementMask_balanced
    (sixVertexLocalIncomingPattern eta v)
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern_ice eta heta v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (by
      simpa [sixVertexLocalDisagreementSides, ne_comm] using hdegree v)
  rw [sixVertexLocalAgreementMask_comm]
  exact h


theorem sixVertexTorusFlip_agreement_ice_first
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (sixVertexTorusFlip (sixVertexTorusAgreementMask omega eta) omega).IceRule :=
  sixVertexTorusFlip_ice_of_balanced homega
    (sixVertexTorusAgreementMask_balanced_first homega heta hdegree)

theorem sixVertexTorusFlip_agreement_ice_second
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (sixVertexTorusFlip (sixVertexTorusAgreementMask omega eta) eta).IceRule :=
  sixVertexTorusFlip_ice_of_balanced heta
    (sixVertexTorusAgreementMask_balanced_second homega heta hdegree)


def sixVertexTorusFlipSeamDelta
    {T : EvenTorus} (mask omega : SixVertexArrows T) : Int :=
  Finset.univ.sum (fun column : Fin T.width =>
    Int.ofNat ((sixVertexTorusFlip mask omega).vertical
      (column, svFinLast T.height_pos)).toNat -
    Int.ofNat (omega.vertical
      (column, svFinLast T.height_pos)).toNat)


theorem sixVertexTorusFlip_upCount
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    (sixVertexUpCount
        (svTorusVerticalRows T (sixVertexTorusFlip mask omega)
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) +
        sixVertexTorusFlipSeamDelta mask omega := by
  let targetRow := svTorusVerticalRows T (sixVertexTorusFlip mask omega)
    (svFinLast T.height_pos)
  let sourceRow := svTorusVerticalRows T omega (svFinLast T.height_pos)
  have htarget : (∑ i, ((targetRow i).toNat : Int)) =
      (sixVertexUpCount targetRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount targetRow
  have hsource : (∑ i, ((sourceRow i).toNat : Int)) =
      (sixVertexUpCount sourceRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount sourceRow
  change (sixVertexUpCount targetRow : Int) =
    (sixVertexUpCount sourceRow : Int) +
      ∑ i, (((targetRow i).toNat : Int) - ((sourceRow i).toNat : Int))
  rw [Finset.sum_sub_distrib, htarget, hsource]
  ring


theorem sixVertexTorusFlipSeamDelta_after_flip
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    sixVertexTorusFlipSeamDelta mask (sixVertexTorusFlip mask omega) =
      -sixVertexTorusFlipSeamDelta mask omega := by
  unfold sixVertexTorusFlipSeamDelta
  simp only [sixVertexTorusFlip_self]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro column _
  ring



theorem sixVertexTorusFlipSeamDelta_maskXor
    {T : EvenTorus} (first second omega : SixVertexArrows T) :
    sixVertexTorusFlipSeamDelta
        (sixVertexTorusMaskXor first second) omega =
      sixVertexTorusFlipSeamDelta first omega +
        sixVertexTorusFlipSeamDelta second
          (sixVertexTorusFlip first omega) := by
  unfold sixVertexTorusFlipSeamDelta
  rw [sixVertexTorusFlip_maskXor_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro column _
  ring

end

end StatMech.FrontierD
