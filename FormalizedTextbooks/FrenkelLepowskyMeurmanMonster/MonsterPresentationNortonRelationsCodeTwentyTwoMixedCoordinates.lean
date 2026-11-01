/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the basis22 mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOddCodes_strictMono : StrictMono
  monsterNortonCodeTwentyTwoForwardOddCodes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 31, monsterNortonCodeTwentyTwoForwardOddCodes i.castSucc <
      monsterNortonCodeTwentyTwoForwardOddCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono
  monsterNortonCodeTwentyTwoForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyTwoForwardColumns i.castSucc <
      monsterNortonCodeTwentyTwoForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeTwentyTwoForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 63, monsterNortonCodeTwentyTwoForwardSpinLabel i.castSucc <
      monsterNortonCodeTwentyTwoForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InverseOctadChoice_strictMono :
    StrictMono monsterNortonCodeTwentyTwoInverseOctadChoice := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyTwoInverseOctadChoice i.castSucc <
      monsterNortonCodeTwentyTwoInverseOctadChoice i.succ := by decide +kernel
  exact hc

private theorem InverseSpinLabel_strictMono (k : Fin 16) :
    StrictMono (monsterNortonCodeTwentyTwoInverseSpinLabel k) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ k : Fin 16, ∀ i : Fin 3,
      monsterNortonCodeTwentyTwoInverseSpinLabel k i.castSucc <
        monsterNortonCodeTwentyTwoInverseSpinLabel k i.succ := by decide +kernel
  exact hc k

private theorem InverseColumns_strictMono : StrictMono
  monsterNortonCodeTwentyTwoInverseColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 15, monsterNortonCodeTwentyTwoInverseColumns i.castSucc <
      monsterNortonCodeTwentyTwoInverseColumns i.succ := by decide +kernel
  exact hc

private theorem InverseSign_strictMono (i : Fin 16) :
    StrictMono (monsterNortonCodeTwentyTwoInverseSign i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 16, ∀ j : Fin 31,
      monsterNortonCodeTwentyTwoInverseSign i j.castSucc <
        monsterNortonCodeTwentyTwoInverseSign i j.succ := by decide +kernel
  exact hc i

private theorem displayCodes_injective : Function.Injective monsterNortonRemainingOctadUCodes := by
  apply StrictMono.injective
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 75, monsterNortonRemainingOctadUCodes i.castSucc <
      monsterNortonRemainingOctadUCodes i.succ := by decide +kernel
  exact hc

/-- Each forward short label is its genuine original odd source coordinate. -/
def monsterNortonCodeTwentyTwoForwardShortIndex (p : Fin 32 × Fin 16) : GriessShortIndex :=
  Sum.inr (Sum.inr (monsterNortonCodeTwentyTwoForwardOddCodes p.1,
    monsterNortonCodeTwentyTwoForwardColumns p.2))

/-- Each inverse short label uses its certified original octad and local sign. -/
noncomputable def monsterNortonCodeTwentyTwoInverseShortIndex (p : Fin 16 × Fin 32) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonCodeTwentyTwoInverseOctadChoice p.1), monsterNortonCodeTwentyTwoInverseSign
      p.1 p.2))

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeTwentyTwoForwardTensorIndex (p : Fin 64 × Fin 16) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTwentyTwoForwardSpinLabel p.1),
    monsterNortonCodeTwentyTwoForwardColumns p.2)

/-- Each inverse tensor address retains its own column's four original spin labels. -/
def monsterNortonCodeTwentyTwoInverseTensorIndex (p : Fin 16 × Fin 4) :
    SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel p.1 p.2),
    monsterNortonCodeTwentyTwoInverseColumns p.1)

/-- Distinct packet entries have distinct actual forward short coordinates. -/
theorem monsterNortonCodeTwentyTwoForwardShortIndex_injective :
    Function.Injective monsterNortonCodeTwentyTwoForwardShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
  exact Prod.ext (ForwardOddCodes_strictMono.injective hp.1)
    (ForwardColumns_strictMono.injective hp.2)

/-- Distinct packet entries have distinct actual inverse short coordinates. -/
theorem monsterNortonCodeTwentyTwoInverseShortIndex_injective :
    Function.Injective monsterNortonCodeTwentyTwoInverseShortIndex := by
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
theorem monsterNortonCodeTwentyTwoForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeTwentyTwoForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeTwentyTwoInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeTwentyTwoInverseTensorIndex := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have hp := Prod.mk.inj h
  have hik : i = k := InverseColumns_strictMono.injective hp.2
  subst k
  have hjl : j = l := (InverseSpinLabel_strictMono i).injective
    (golayLabelCoefficients_bijective.injective hp.1)
  exact Prod.ext rfl hjl

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTwentyTwoForwardTensorCoefficient_sq :
    (∑ p : Fin 64 × Fin 16, monsterNortonCodeTwentyTwoForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTwentyTwoInverseTensorCoefficient_sq :
    (∑ p : Fin 16 × Fin 4, monsterNortonCodeTwentyTwoInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeTwentyTwoForwardPacket : GriessSpace :=
  ∑ k : (Fin 32 × Fin 16) ⊕ (Fin 64 × Fin 16),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTwentyTwoForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTwentyTwoForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTwentyTwoForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTwentyTwoForwardTensorIndex j).1
            (monsterNortonCodeTwentyTwoForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTwentyTwoForwardPacket_norm :
    griessForm monsterNortonCodeTwentyTwoForwardPacket
      monsterNortonCodeTwentyTwoForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTwentyTwoForwardShortIndex monsterNortonCodeTwentyTwoForwardTensorIndex
    monsterNortonCodeTwentyTwoForwardShortIndex_injective
    monsterNortonCodeTwentyTwoForwardTensorIndex_injective
  · decide +kernel
  · exact monsterNortonCodeTwentyTwoForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeTwentyTwoInversePacket : GriessSpace :=
  ∑ k : (Fin 16 × Fin 32) ⊕ (Fin 16 × Fin 4),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTwentyTwoInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTwentyTwoInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTwentyTwoInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTwentyTwoInverseTensorIndex j).1
            (monsterNortonCodeTwentyTwoInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTwentyTwoInversePacket_norm :
    griessForm monsterNortonCodeTwentyTwoInversePacket
      monsterNortonCodeTwentyTwoInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTwentyTwoInverseShortIndex monsterNortonCodeTwentyTwoInverseTensorIndex
    monsterNortonCodeTwentyTwoInverseShortIndex_injective
    monsterNortonCodeTwentyTwoInverseTensorIndex_injective
  · decide +kernel
  · exact monsterNortonCodeTwentyTwoInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
