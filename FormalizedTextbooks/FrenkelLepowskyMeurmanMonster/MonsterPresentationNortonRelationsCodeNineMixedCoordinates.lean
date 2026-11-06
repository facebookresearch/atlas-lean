/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-nine mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOddCodes_strictMono : StrictMono monsterNortonCodeNineForwardOddCodes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 31, monsterNortonCodeNineForwardOddCodes i.castSucc <
      monsterNortonCodeNineForwardOddCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeNineForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeNineForwardColumns i.castSucc <
      monsterNortonCodeNineForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeNineForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 63, monsterNortonCodeNineForwardSpinLabel i.castSucc <
      monsterNortonCodeNineForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeNineInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeNineInverseOctadChoice i.castSucc <
      monsterNortonCodeNineInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeNineInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeNineInverseSpinLabel i.castSucc <
      monsterNortonCodeNineInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono monsterNortonCodeNineInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeNineInverseColumns i.castSucc <
      monsterNortonCodeNineInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeNineInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeNineInverseSign i j.castSucc <
        monsterNortonCodeNineInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

/-- Each forward short label is its genuine original odd source coordinate. -/
def monsterNortonCodeNineForwardShortIndex (p : Fin 32 × Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inr (monsterNortonCodeNineForwardOddCodes p.1,
    monsterNortonCodeNineForwardColumns p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeNineInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeNineInverseOctadChoice p.1), monsterNortonCodeNineInverseSign p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeNineForwardTensorIndex (p : Fin 64 × Fin 8) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeNineForwardSpinLabel p.1),
    monsterNortonCodeNineForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeNineInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeNineInverseSpinLabel p.1),
    monsterNortonCodeNineInverseColumns p.2)

/-- Distinct packet entries have distinct actual forward short coordinates. -/
theorem monsterNortonCodeNineForwardShortIndex_injective :
    Function.Injective monsterNortonCodeNineForwardShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
  exact Prod.ext (ForwardOddCodes_strictMono.injective hp.1)
    (ForwardColumns_strictMono.injective hp.2)

/-- Distinct packet entries have distinct actual inverse short coordinates. -/
theorem monsterNortonCodeNineInverseShortIndex_injective :
    Function.Injective monsterNortonCodeNineInverseShortIndex := by
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
theorem monsterNortonCodeNineForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeNineForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeNineInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeNineInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeNineForwardTensorCoefficient (p : Fin 64 × Fin 8) : ℤ :=
  monsterNortonCodeNineForwardSpinCoefficient p.1 *
    monsterNortonCodeNineForwardLeech (monsterNortonCodeNineForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeNineInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeNineInverseSpinCoefficient p.1 *
    monsterNortonCodeNineInverseLeech (monsterNortonCodeNineInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeNineForwardTensorCoefficient_sq :
    (∑ p : Fin 64 × Fin 8, monsterNortonCodeNineForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeNineInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeNineInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeNineForwardPacket : GriessSpace :=
  ∑ k : (Fin 32 × Fin 8) ⊕ (Fin 64 × Fin 8),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeNineForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeNineForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeNineForwardTensorIndex j).1
            (monsterNortonCodeNineForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeNineForwardPacket_norm :
    griessForm monsterNortonCodeNineForwardPacket monsterNortonCodeNineForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeNineForwardShortIndex monsterNortonCodeNineForwardTensorIndex
    monsterNortonCodeNineForwardShortIndex_injective
    monsterNortonCodeNineForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeNine_forward_short_sq
  · exact monsterNortonCodeNineForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeNineInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeNineInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeNineInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeNineInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeNineInverseTensorIndex j).1
            (monsterNortonCodeNineInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeNineInversePacket_norm :
    griessForm monsterNortonCodeNineInversePacket monsterNortonCodeNineInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeNineInverseShortIndex monsterNortonCodeNineInverseTensorIndex
    monsterNortonCodeNineInverseShortIndex_injective
    monsterNortonCodeNineInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeNine_inverse_short_sq
  · exact monsterNortonCodeNineInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
