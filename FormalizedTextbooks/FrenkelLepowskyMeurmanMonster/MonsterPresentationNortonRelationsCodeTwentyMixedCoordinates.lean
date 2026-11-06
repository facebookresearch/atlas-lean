/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the code-twenty mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOctadChoice_strictMono :
    StrictMono monsterNortonCodeTwentyForwardOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeTwentyForwardOctadChoice i.castSucc <
      monsterNortonCodeTwentyForwardOctadChoice i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeTwentyForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeTwentyForwardColumns i.castSucc <
      monsterNortonCodeTwentyForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeTwentyForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyForwardSpinLabel i.castSucc <
      monsterNortonCodeTwentyForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeTwentyInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeTwentyInverseOctadChoice i.castSucc <
      monsterNortonCodeTwentyInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono :
    StrictMono monsterNortonCodeTwentyInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyInverseSpinLabel i.castSucc <
      monsterNortonCodeTwentyInverseSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseColumns_strictMono : StrictMono monsterNortonCodeTwentyInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 3, monsterNortonCodeTwentyInverseColumns i.castSucc <
      monsterNortonCodeTwentyInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeTwentyInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeTwentyInverseSign i j.castSucc <
        monsterNortonCodeTwentyInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardSign_strictMono (i : Fin 8) :
    StrictMono (monsterNortonCodeTwentyForwardSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 8, ∀ j : Fin 31,
      monsterNortonCodeTwentyForwardSign i j.castSucc <
        monsterNortonCodeTwentyForwardSign i j.succ := by decide +kernel
  exact hc i

private theorem forwardCodes_injective :
    Function.Injective monsterNortonEvenShortInverseUOctadCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 93, monsterNortonEvenShortInverseUOctadCodes i.castSucc <
      monsterNortonEvenShortInverseUOctadCodes i.succ := by decide +kernel
  exact hc

/-- Original forward octad coordinates from the actual source dictionary. -/
noncomputable def monsterNortonCodeTwentyForwardShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  let a := monsterNortonCodeTwentyForwardOctadChoice p.1
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctad_weight a), monsterNortonCodeTwentyForwardSign p.1 p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeTwentyInverseShortIndex (p : Fin 8 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeTwentyInverseOctadChoice p.1), monsterNortonCodeTwentyInverseSign p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeTwentyForwardTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTwentyForwardSpinLabel p.1),
    monsterNortonCodeTwentyForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeTwentyInverseTensorIndex (p : Fin 16 × Fin 4) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel p.1),
    monsterNortonCodeTwentyInverseColumns p.2)

/-- Distinct forward packet entries name distinct genuine octad-sign coordinates. -/
theorem monsterNortonCodeTwentyForwardShortIndex_injective :
    Function.Injective monsterNortonCodeTwentyForwardShortIndex := by
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
theorem monsterNortonCodeTwentyInverseShortIndex_injective :
    Function.Injective monsterNortonCodeTwentyInverseShortIndex := by
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
theorem monsterNortonCodeTwentyForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeTwentyForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeTwentyInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeTwentyInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_strictMono.injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeTwentyForwardTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeTwentyForwardSpinCoefficient p.1 *
    monsterNortonCodeTwentyForwardLeech (monsterNortonCodeTwentyForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeTwentyInverseTensorCoefficient (p : Fin 16 × Fin 4) : ℤ :=
  monsterNortonCodeTwentyInverseSpinCoefficient p.1 *
    monsterNortonCodeTwentyInverseLeech (monsterNortonCodeTwentyInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTwentyForwardTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeTwentyForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTwentyInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeTwentyInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeTwentyForwardPacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTwentyForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTwentyForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTwentyForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTwentyForwardTensorIndex j).1
            (monsterNortonCodeTwentyForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTwentyForwardPacket_norm :
    griessForm monsterNortonCodeTwentyForwardPacket monsterNortonCodeTwentyForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTwentyForwardShortIndex monsterNortonCodeTwentyForwardTensorIndex
    monsterNortonCodeTwentyForwardShortIndex_injective
    monsterNortonCodeTwentyForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeTwenty_forward_short_sq
  · exact monsterNortonCodeTwentyForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeTwentyInversePacket : GriessSpace :=
  ∑ k : (Fin 8 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTwentyInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTwentyInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTwentyInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTwentyInverseTensorIndex j).1
            (monsterNortonCodeTwentyInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTwentyInversePacket_norm :
    griessForm monsterNortonCodeTwentyInversePacket monsterNortonCodeTwentyInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTwentyInverseShortIndex monsterNortonCodeTwentyInverseTensorIndex
    monsterNortonCodeTwentyInverseShortIndex_injective
    monsterNortonCodeTwentyInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeTwenty_inverse_short_sq
  · exact monsterNortonCodeTwentyInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
