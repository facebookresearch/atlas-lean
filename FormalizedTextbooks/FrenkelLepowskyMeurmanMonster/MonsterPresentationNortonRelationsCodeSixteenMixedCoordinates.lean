/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-sixteen mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOctadChoice_strictMono :
    StrictMono monsterNortonCodeSixteenForwardOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeSixteenForwardOctadChoice i.castSucc <
      monsterNortonCodeSixteenForwardOctadChoice i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeSixteenForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeSixteenForwardColumns i.castSucc <
      monsterNortonCodeSixteenForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeSixteenForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeSixteenForwardSpinLabel i.castSucc <
      monsterNortonCodeSixteenForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeSixteenInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeSixteenInverseOctadChoice i.castSucc <
      monsterNortonCodeSixteenInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeSixteenInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeSixteenInverseSpinLabel i.castSucc <
      monsterNortonCodeSixteenInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono monsterNortonCodeSixteenInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeSixteenInverseColumns i.castSucc <
      monsterNortonCodeSixteenInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeSixteenInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeSixteenInverseSign i j.castSucc <
        monsterNortonCodeSixteenInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeSixteenForwardSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeSixteenForwardSign i j.castSucc <
        monsterNortonCodeSixteenForwardSign i j.succ := by decide +kernel
  exact hc i

private theorem forwardCodes_injective :
    Function.Injective monsterNortonEvenShortInverseUOctadCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 93, monsterNortonEvenShortInverseUOctadCodes i.castSucc <
      monsterNortonEvenShortInverseUOctadCodes i.succ := by decide +kernel
  exact hc

/-- Original forward octad coordinates from the actual source dictionary. -/
noncomputable def monsterNortonCodeSixteenForwardShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  let a := monsterNortonCodeSixteenForwardOctadChoice p.1
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctad_weight a), monsterNortonCodeSixteenForwardSign p.1 p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeSixteenInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeSixteenInverseOctadChoice p.1), monsterNortonCodeSixteenInverseSign p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeSixteenForwardTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeSixteenForwardSpinLabel p.1),
    monsterNortonCodeSixteenForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeSixteenInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel p.1),
    monsterNortonCodeSixteenInverseColumns p.2)

/-- Distinct forward packet entries name distinct genuine octad-sign coordinates. -/
theorem monsterNortonCodeSixteenForwardShortIndex_injective :
    Function.Injective monsterNortonCodeSixteenForwardShortIndex := by
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
theorem monsterNortonCodeSixteenInverseShortIndex_injective :
    Function.Injective monsterNortonCodeSixteenInverseShortIndex := by
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
theorem monsterNortonCodeSixteenForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeSixteenForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeSixteenInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeSixteenInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeSixteenForwardTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeSixteenForwardSpinCoefficient p.1 *
    monsterNortonCodeSixteenForwardLeech (monsterNortonCodeSixteenForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeSixteenInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeSixteenInverseSpinCoefficient p.1 *
    monsterNortonCodeSixteenInverseLeech (monsterNortonCodeSixteenInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeSixteenForwardTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeSixteenForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeSixteenInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeSixteenInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeSixteenForwardPacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeSixteenForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeSixteenForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeSixteenForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeSixteenForwardTensorIndex j).1
            (monsterNortonCodeSixteenForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeSixteenForwardPacket_norm :
    griessForm monsterNortonCodeSixteenForwardPacket monsterNortonCodeSixteenForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeSixteenForwardShortIndex monsterNortonCodeSixteenForwardTensorIndex
    monsterNortonCodeSixteenForwardShortIndex_injective
    monsterNortonCodeSixteenForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeSixteen_forward_short_sq
  · exact monsterNortonCodeSixteenForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeSixteenInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeSixteenInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeSixteenInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeSixteenInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeSixteenInverseTensorIndex j).1
            (monsterNortonCodeSixteenInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeSixteenInversePacket_norm :
    griessForm monsterNortonCodeSixteenInversePacket monsterNortonCodeSixteenInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeSixteenInverseShortIndex monsterNortonCodeSixteenInverseTensorIndex
    monsterNortonCodeSixteenInverseShortIndex_injective
    monsterNortonCodeSixteenInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeSixteen_inverse_short_sq
  · exact monsterNortonCodeSixteenInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
