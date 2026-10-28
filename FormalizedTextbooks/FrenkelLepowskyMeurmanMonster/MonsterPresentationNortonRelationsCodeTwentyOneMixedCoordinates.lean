/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-twentyone mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOctadChoice_strictMono :
    StrictMono monsterNortonCodeTwentyOneForwardOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeTwentyOneForwardOctadChoice i.castSucc <
      monsterNortonCodeTwentyOneForwardOctadChoice i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono
  monsterNortonCodeTwentyOneForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeTwentyOneForwardColumns i.castSucc <
      monsterNortonCodeTwentyOneForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeTwentyOneForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyOneForwardSpinLabel i.castSucc <
      monsterNortonCodeTwentyOneForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeTwentyOneInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeTwentyOneInverseOctadChoice i.castSucc <
      monsterNortonCodeTwentyOneInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeTwentyOneInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyOneInverseSpinLabel i.castSucc <
      monsterNortonCodeTwentyOneInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono
  monsterNortonCodeTwentyOneInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeTwentyOneInverseColumns i.castSucc <
      monsterNortonCodeTwentyOneInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeTwentyOneInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeTwentyOneInverseSign i j.castSucc <
        monsterNortonCodeTwentyOneInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeTwentyOneForwardSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeTwentyOneForwardSign i j.castSucc <
        monsterNortonCodeTwentyOneForwardSign i j.succ := by decide +kernel
  exact hc i

private theorem forwardCodes_injective :
    Function.Injective monsterNortonEvenShortInverseUOctadCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 93, monsterNortonEvenShortInverseUOctadCodes i.castSucc <
      monsterNortonEvenShortInverseUOctadCodes i.succ := by decide +kernel
  exact hc

/-- Original forward octad coordinates from the actual source dictionary. -/
noncomputable def monsterNortonCodeTwentyOneForwardShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  let a := monsterNortonCodeTwentyOneForwardOctadChoice p.1
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctad_weight a), monsterNortonCodeTwentyOneForwardSign p.1 p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeTwentyOneInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeTwentyOneInverseOctadChoice p.1), monsterNortonCodeTwentyOneInverseSign
      p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeTwentyOneForwardTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel p.1),
    monsterNortonCodeTwentyOneForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeTwentyOneInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTwentyOneInverseSpinLabel p.1),
    monsterNortonCodeTwentyOneInverseColumns p.2)

/-- Distinct forward packet entries name distinct genuine octad-sign coordinates. -/
theorem monsterNortonCodeTwentyOneForwardShortIndex_injective :
    Function.Injective monsterNortonCodeTwentyOneForwardShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))
  have hc := congrArg golayOctadLabel hp.1
  simp only [monsterNortonOctadIndex_label] at hc
  have hi := ForwardOctadChoice_strictMono.injective (forwardCodes_injective hc)
  have hj : p.2 = q.2 := by
    rw [hi] at hp
    exact (ForwardSign_strictMono q.1).injective hp.2
  exact Prod.ext hi hj

/-- Distinct packet entries have distinct actual inverse short coordinates. -/
theorem monsterNortonCodeTwentyOneInverseShortIndex_injective :
    Function.Injective monsterNortonCodeTwentyOneInverseShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))
  have hc := congrArg golayOctadLabel hp.1
  simp only [monsterNortonRemainingOctadUOctad, monsterNortonOctadIndex_label] at hc
  have hi := InverseOctadChoice_strictMono.injective (displayCodes_injective hc)
  have hj : p.2 = q.2 := by
    rw [hi] at hp
    exact (InverseSign_strictMono q.1).injective hp.2
  exact Prod.ext hi hj

/-- The forward tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeTwentyOneForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeTwentyOneForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeTwentyOneInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeTwentyOneInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeTwentyOneForwardTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeTwentyOneForwardSpinCoefficient p.1 *
    monsterNortonCodeTwentyOneForwardLeech (monsterNortonCodeTwentyOneForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeTwentyOneInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeTwentyOneInverseSpinCoefficient p.1 *
    monsterNortonCodeTwentyOneInverseLeech (monsterNortonCodeTwentyOneInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTwentyOneForwardTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeTwentyOneForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTwentyOneInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeTwentyOneInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeTwentyOneForwardPacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTwentyOneForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTwentyOneForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTwentyOneForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTwentyOneForwardTensorIndex j).1
            (monsterNortonCodeTwentyOneForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTwentyOneForwardPacket_norm :
    griessForm monsterNortonCodeTwentyOneForwardPacket
      monsterNortonCodeTwentyOneForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTwentyOneForwardShortIndex monsterNortonCodeTwentyOneForwardTensorIndex
    monsterNortonCodeTwentyOneForwardShortIndex_injective
    monsterNortonCodeTwentyOneForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeTwentyOne_forward_short_sq
  · exact monsterNortonCodeTwentyOneForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeTwentyOneInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTwentyOneInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTwentyOneInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTwentyOneInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTwentyOneInverseTensorIndex j).1
            (monsterNortonCodeTwentyOneInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTwentyOneInversePacket_norm :
    griessForm monsterNortonCodeTwentyOneInversePacket
      monsterNortonCodeTwentyOneInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTwentyOneInverseShortIndex monsterNortonCodeTwentyOneInverseTensorIndex
    monsterNortonCodeTwentyOneInverseShortIndex_injective
    monsterNortonCodeTwentyOneInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeTwentyOne_inverse_short_sq
  · exact monsterNortonCodeTwentyOneInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
