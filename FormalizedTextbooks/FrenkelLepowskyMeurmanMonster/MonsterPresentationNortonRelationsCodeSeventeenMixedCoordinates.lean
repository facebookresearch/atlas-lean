/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-seventeen mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOctadChoice_strictMono :
    StrictMono monsterNortonCodeSeventeenForwardOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeSeventeenForwardOctadChoice i.castSucc <
      monsterNortonCodeSeventeenForwardOctadChoice i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono
  monsterNortonCodeSeventeenForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeSeventeenForwardColumns i.castSucc <
      monsterNortonCodeSeventeenForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeSeventeenForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeSeventeenForwardSpinLabel i.castSucc <
      monsterNortonCodeSeventeenForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeSeventeenInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeSeventeenInverseOctadChoice i.castSucc <
      monsterNortonCodeSeventeenInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeSeventeenInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeSeventeenInverseSpinLabel i.castSucc <
      monsterNortonCodeSeventeenInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono
  monsterNortonCodeSeventeenInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeSeventeenInverseColumns i.castSucc <
      monsterNortonCodeSeventeenInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeSeventeenInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeSeventeenInverseSign i j.castSucc <
        monsterNortonCodeSeventeenInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeSeventeenForwardSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeSeventeenForwardSign i j.castSucc <
        monsterNortonCodeSeventeenForwardSign i j.succ := by decide +kernel
  exact hc i

private theorem forwardCodes_injective :
    Function.Injective monsterNortonEvenShortInverseUOctadCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 93, monsterNortonEvenShortInverseUOctadCodes i.castSucc <
      monsterNortonEvenShortInverseUOctadCodes i.succ := by decide +kernel
  exact hc

/-- Original forward octad coordinates from the actual source dictionary. -/
noncomputable def monsterNortonCodeSeventeenForwardShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  let a := monsterNortonCodeSeventeenForwardOctadChoice p.1
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctad_weight a), monsterNortonCodeSeventeenForwardSign p.1 p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeSeventeenInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeSeventeenInverseOctadChoice p.1), monsterNortonCodeSeventeenInverseSign
      p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeSeventeenForwardTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeSeventeenForwardSpinLabel p.1),
    monsterNortonCodeSeventeenForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeSeventeenInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel p.1),
    monsterNortonCodeSeventeenInverseColumns p.2)

/-- Distinct forward packet entries name distinct genuine octad-sign coordinates. -/
theorem monsterNortonCodeSeventeenForwardShortIndex_injective :
    Function.Injective monsterNortonCodeSeventeenForwardShortIndex := by
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
theorem monsterNortonCodeSeventeenInverseShortIndex_injective :
    Function.Injective monsterNortonCodeSeventeenInverseShortIndex := by
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
theorem monsterNortonCodeSeventeenForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeSeventeenForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeSeventeenInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeSeventeenInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeSeventeenForwardTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeSeventeenForwardSpinCoefficient p.1 *
    monsterNortonCodeSeventeenForwardLeech (monsterNortonCodeSeventeenForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeSeventeenInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeSeventeenInverseSpinCoefficient p.1 *
    monsterNortonCodeSeventeenInverseLeech (monsterNortonCodeSeventeenInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeSeventeenForwardTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeSeventeenForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeSeventeenInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeSeventeenInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeSeventeenForwardPacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeSeventeenForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeSeventeenForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeSeventeenForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeSeventeenForwardTensorIndex j).1
            (monsterNortonCodeSeventeenForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeSeventeenForwardPacket_norm :
    griessForm monsterNortonCodeSeventeenForwardPacket
      monsterNortonCodeSeventeenForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeSeventeenForwardShortIndex monsterNortonCodeSeventeenForwardTensorIndex
    monsterNortonCodeSeventeenForwardShortIndex_injective
    monsterNortonCodeSeventeenForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeSeventeen_forward_short_sq
  · exact monsterNortonCodeSeventeenForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeSeventeenInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeSeventeenInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeSeventeenInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeSeventeenInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeSeventeenInverseTensorIndex j).1
            (monsterNortonCodeSeventeenInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeSeventeenInversePacket_norm :
    griessForm monsterNortonCodeSeventeenInversePacket
      monsterNortonCodeSeventeenInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeSeventeenInverseShortIndex monsterNortonCodeSeventeenInverseTensorIndex
    monsterNortonCodeSeventeenInverseShortIndex_injective
    monsterNortonCodeSeventeenInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeSeventeen_inverse_short_sq
  · exact monsterNortonCodeSeventeenInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
