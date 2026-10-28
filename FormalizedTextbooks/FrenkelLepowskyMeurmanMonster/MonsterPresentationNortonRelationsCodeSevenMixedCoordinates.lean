/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-seven mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOddCodes_strictMono : StrictMono monsterNortonCodeSevenForwardOddCodes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 31, monsterNortonCodeSevenForwardOddCodes i.castSucc <
      monsterNortonCodeSevenForwardOddCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeSevenForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeSevenForwardColumns i.castSucc <
      monsterNortonCodeSevenForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeSevenForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 63, monsterNortonCodeSevenForwardSpinLabel i.castSucc <
      monsterNortonCodeSevenForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeSevenInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeSevenInverseOctadChoice i.castSucc <
      monsterNortonCodeSevenInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeSevenInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeSevenInverseSpinLabel i.castSucc <
      monsterNortonCodeSevenInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono monsterNortonCodeSevenInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeSevenInverseColumns i.castSucc <
      monsterNortonCodeSevenInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeSevenInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeSevenInverseSign i j.castSucc <
        monsterNortonCodeSevenInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

/-- Each forward short label is its genuine original odd source coordinate. -/
def monsterNortonCodeSevenForwardShortIndex (p : Fin 32 × Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inr (monsterNortonCodeSevenForwardOddCodes p.1,
    monsterNortonCodeSevenForwardColumns p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeSevenInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeSevenInverseOctadChoice p.1), monsterNortonCodeSevenInverseSign p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeSevenForwardTensorIndex (p : Fin 64 × Fin 8) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeSevenForwardSpinLabel p.1),
    monsterNortonCodeSevenForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeSevenInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeSevenInverseSpinLabel p.1),
    monsterNortonCodeSevenInverseColumns p.2)

/-- Distinct packet entries have distinct actual forward short coordinates. -/
theorem monsterNortonCodeSevenForwardShortIndex_injective :
    Function.Injective monsterNortonCodeSevenForwardShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
  exact Prod.ext (ForwardOddCodes_strictMono.injective hp.1)
    (ForwardColumns_strictMono.injective hp.2)

/-- Distinct packet entries have distinct actual inverse short coordinates. -/
theorem monsterNortonCodeSevenInverseShortIndex_injective :
    Function.Injective monsterNortonCodeSevenInverseShortIndex := by
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
theorem monsterNortonCodeSevenForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeSevenForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeSevenInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeSevenInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeSevenForwardTensorCoefficient (p : Fin 64 × Fin 8) : ℤ :=
  monsterNortonCodeSevenForwardSpinCoefficient p.1 *
    monsterNortonCodeSevenForwardLeech (monsterNortonCodeSevenForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeSevenInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeSevenInverseSpinCoefficient p.1 *
    monsterNortonCodeSevenInverseLeech (monsterNortonCodeSevenInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeSevenForwardTensorCoefficient_sq :
    (∑ p : Fin 64 × Fin 8, monsterNortonCodeSevenForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeSevenInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeSevenInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeSevenForwardPacket : GriessSpace :=
  ∑ k : (Fin 32 × Fin 8) ⊕ (Fin 64 × Fin 8),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeSevenForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeSevenForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeSevenForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeSevenForwardTensorIndex j).1
            (monsterNortonCodeSevenForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeSevenForwardPacket_norm :
    griessForm monsterNortonCodeSevenForwardPacket monsterNortonCodeSevenForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeSevenForwardShortIndex monsterNortonCodeSevenForwardTensorIndex
    monsterNortonCodeSevenForwardShortIndex_injective
    monsterNortonCodeSevenForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeSeven_forward_short_sq
  · exact monsterNortonCodeSevenForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeSevenInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeSevenInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeSevenInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeSevenInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeSevenInverseTensorIndex j).1
            (monsterNortonCodeSevenInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeSevenInversePacket_norm :
    griessForm monsterNortonCodeSevenInversePacket monsterNortonCodeSevenInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeSevenInverseShortIndex monsterNortonCodeSevenInverseTensorIndex
    monsterNortonCodeSevenInverseShortIndex_injective
    monsterNortonCodeSevenInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeSeven_inverse_short_sq
  · exact monsterNortonCodeSevenInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
