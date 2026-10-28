/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-five mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOddCodes_strictMono : StrictMono monsterNortonCodeFiveForwardOddCodes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 31, monsterNortonCodeFiveForwardOddCodes i.castSucc <
      monsterNortonCodeFiveForwardOddCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeFiveForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeFiveForwardColumns i.castSucc <
      monsterNortonCodeFiveForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono : StrictMono monsterNortonCodeFiveForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 63, monsterNortonCodeFiveForwardSpinLabel i.castSucc <
      monsterNortonCodeFiveForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeFiveInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeFiveInverseOctadChoice i.castSucc <
      monsterNortonCodeFiveInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono : StrictMono monsterNortonCodeFiveInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeFiveInverseSpinLabel i.castSucc <
      monsterNortonCodeFiveInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono monsterNortonCodeFiveInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeFiveInverseColumns i.castSucc <
      monsterNortonCodeFiveInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeFiveInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeFiveInverseSign i j.castSucc <
        monsterNortonCodeFiveInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

/-- Each forward short label is its genuine original odd source coordinate. -/
def monsterNortonCodeFiveForwardShortIndex (p : Fin 32 × Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inr (monsterNortonCodeFiveForwardOddCodes p.1,
    monsterNortonCodeFiveForwardColumns p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeFiveInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeFiveInverseOctadChoice p.1), monsterNortonCodeFiveInverseSign p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeFiveForwardTensorIndex (p : Fin 64 × Fin 8) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeFiveForwardSpinLabel p.1),
    monsterNortonCodeFiveForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeFiveInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeFiveInverseSpinLabel p.1),
    monsterNortonCodeFiveInverseColumns p.2)

/-- Distinct packet entries have distinct actual forward short coordinates. -/
theorem monsterNortonCodeFiveForwardShortIndex_injective :
    Function.Injective monsterNortonCodeFiveForwardShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
  exact Prod.ext (ForwardOddCodes_strictMono.injective hp.1)
    (ForwardColumns_strictMono.injective hp.2)

/-- Distinct packet entries have distinct actual inverse short coordinates. -/
theorem monsterNortonCodeFiveInverseShortIndex_injective :
    Function.Injective monsterNortonCodeFiveInverseShortIndex := by
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
theorem monsterNortonCodeFiveForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeFiveForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeFiveInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeFiveInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeFiveForwardTensorCoefficient (p : Fin 64 × Fin 8) : ℤ :=
  monsterNortonCodeFiveForwardSpinCoefficient p.1 *
    monsterNortonCodeFiveForwardLeech (monsterNortonCodeFiveForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeFiveInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeFiveInverseSpinCoefficient p.1 *
    monsterNortonCodeFiveInverseLeech (monsterNortonCodeFiveInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeFiveForwardTensorCoefficient_sq :
    (∑ p : Fin 64 × Fin 8, monsterNortonCodeFiveForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeFiveInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeFiveInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeFiveForwardPacket : GriessSpace :=
  ∑ k : (Fin 32 × Fin 8) ⊕ (Fin 64 × Fin 8),
    Sum.elim (fun i => ((fun p => monsterNortonCodeFiveForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeFiveForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeFiveForwardTensorIndex j).1
            (monsterNortonCodeFiveForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeFiveForwardPacket_norm :
    griessForm monsterNortonCodeFiveForwardPacket monsterNortonCodeFiveForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeFiveForwardShortIndex monsterNortonCodeFiveForwardTensorIndex
    monsterNortonCodeFiveForwardShortIndex_injective
    monsterNortonCodeFiveForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeFive_forward_short_sq
  · exact monsterNortonCodeFiveForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeFiveInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i => ((fun p => monsterNortonCodeFiveInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeFiveInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeFiveInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeFiveInverseTensorIndex j).1
            (monsterNortonCodeFiveInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeFiveInversePacket_norm :
    griessForm monsterNortonCodeFiveInversePacket monsterNortonCodeFiveInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeFiveInverseShortIndex monsterNortonCodeFiveInverseTensorIndex
    monsterNortonCodeFiveInverseShortIndex_injective
    monsterNortonCodeFiveInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeFive_inverse_short_sq
  · exact monsterNortonCodeFiveInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
