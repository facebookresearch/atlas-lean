/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-nineteen mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOctadChoice_strictMono :
    StrictMono monsterNortonCodeNineteenForwardOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeNineteenForwardOctadChoice i.castSucc <
      monsterNortonCodeNineteenForwardOctadChoice i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeNineteenForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeNineteenForwardColumns i.castSucc <
      monsterNortonCodeNineteenForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeNineteenForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeNineteenForwardSpinLabel i.castSucc <
      monsterNortonCodeNineteenForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeNineteenInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeNineteenInverseOctadChoice i.castSucc <
      monsterNortonCodeNineteenInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeNineteenInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeNineteenInverseSpinLabel i.castSucc <
      monsterNortonCodeNineteenInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono monsterNortonCodeNineteenInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeNineteenInverseColumns i.castSucc <
      monsterNortonCodeNineteenInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeNineteenInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeNineteenInverseSign i j.castSucc <
        monsterNortonCodeNineteenInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeNineteenForwardSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeNineteenForwardSign i j.castSucc <
        monsterNortonCodeNineteenForwardSign i j.succ := by decide +kernel
  exact hc i

private theorem forwardCodes_injective :
    Function.Injective monsterNortonEvenShortInverseUOctadCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 93, monsterNortonEvenShortInverseUOctadCodes i.castSucc <
      monsterNortonEvenShortInverseUOctadCodes i.succ := by decide +kernel
  exact hc

/-- Original forward octad coordinates from the actual source dictionary. -/
noncomputable def monsterNortonCodeNineteenForwardShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  let a := monsterNortonCodeNineteenForwardOctadChoice p.1
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctad_weight a), monsterNortonCodeNineteenForwardSign p.1 p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeNineteenInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeNineteenInverseOctadChoice p.1), monsterNortonCodeNineteenInverseSign
      p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeNineteenForwardTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeNineteenForwardSpinLabel p.1),
    monsterNortonCodeNineteenForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeNineteenInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeNineteenInverseSpinLabel p.1),
    monsterNortonCodeNineteenInverseColumns p.2)

/-- Distinct forward packet entries name distinct genuine octad-sign coordinates. -/
theorem monsterNortonCodeNineteenForwardShortIndex_injective :
    Function.Injective monsterNortonCodeNineteenForwardShortIndex := by
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
theorem monsterNortonCodeNineteenInverseShortIndex_injective :
    Function.Injective monsterNortonCodeNineteenInverseShortIndex := by
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
theorem monsterNortonCodeNineteenForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeNineteenForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeNineteenInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeNineteenInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeNineteenForwardTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeNineteenForwardSpinCoefficient p.1 *
    monsterNortonCodeNineteenForwardLeech (monsterNortonCodeNineteenForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeNineteenInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeNineteenInverseSpinCoefficient p.1 *
    monsterNortonCodeNineteenInverseLeech (monsterNortonCodeNineteenInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeNineteenForwardTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeNineteenForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeNineteenInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeNineteenInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeNineteenForwardPacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeNineteenForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeNineteenForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeNineteenForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeNineteenForwardTensorIndex j).1
            (monsterNortonCodeNineteenForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeNineteenForwardPacket_norm :
    griessForm monsterNortonCodeNineteenForwardPacket monsterNortonCodeNineteenForwardPacket
      = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeNineteenForwardShortIndex monsterNortonCodeNineteenForwardTensorIndex
    monsterNortonCodeNineteenForwardShortIndex_injective
    monsterNortonCodeNineteenForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeNineteen_forward_short_sq
  · exact monsterNortonCodeNineteenForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeNineteenInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeNineteenInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeNineteenInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeNineteenInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeNineteenInverseTensorIndex j).1
            (monsterNortonCodeNineteenInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeNineteenInversePacket_norm :
    griessForm monsterNortonCodeNineteenInversePacket monsterNortonCodeNineteenInversePacket
      = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeNineteenInverseShortIndex monsterNortonCodeNineteenInverseTensorIndex
    monsterNortonCodeNineteenInverseShortIndex_injective
    monsterNortonCodeNineteenInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeNineteen_inverse_short_sq
  · exact monsterNortonCodeNineteenInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
