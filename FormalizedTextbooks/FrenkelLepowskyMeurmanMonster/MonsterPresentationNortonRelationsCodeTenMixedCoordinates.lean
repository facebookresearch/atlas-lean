/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Distinct actual labels and complete norms of the preferred-basis-ten mixed packet candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenMixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem ForwardOddCodes_strictMono : StrictMono monsterNortonCodeTenForwardOddCodes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 31, monsterNortonCodeTenForwardOddCodes i.castSucc <
      monsterNortonCodeTenForwardOddCodes i.succ := by decide +kernel
  exact hc

private theorem ForwardColumns_strictMono : StrictMono monsterNortonCodeTenForwardColumns := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 7, monsterNortonCodeTenForwardColumns i.castSucc <
      monsterNortonCodeTenForwardColumns i.succ := by decide +kernel
  exact hc

private theorem ForwardSpinLabel_strictMono :
    StrictMono monsterNortonCodeTenForwardSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have hc : ∀ i : Fin 63, monsterNortonCodeTenForwardSpinLabel i.castSucc <
      monsterNortonCodeTenForwardSpinLabel i.succ := by decide +kernel
  exact hc

private theorem InversePair_injective : Function.Injective monsterNortonCodeTenInversePair := by
  intro i j h
  have hc := congrArg griessCoordinatePair h
  simp only [monsterNortonCodeTenInversePair, griessPairIndex_coordinates,
    monsterNortonCodeTenInversePair_lt, ite_true] at hc
  exact monsterNortonCodeTenInversePairPhysical_injective hc

private theorem InverseSpinLabel_strictMono : StrictMono monsterNortonCodeTenInverseSpinLabel := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have h : ∀ i : Fin 3, monsterNortonCodeTenInverseSpinLabel i.castSucc <
      monsterNortonCodeTenInverseSpinLabel i.succ := by decide +kernel
  exact h

private theorem InverseColumns_injective : Function.Injective monsterNortonCodeTenInverseColumns :=
  fun a b _ => Subsingleton.elim a b

/-- Each forward short label is its genuine original odd source coordinate. -/
def monsterNortonCodeTenForwardShortIndex (p : Fin 32 × Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inr (monsterNortonCodeTenForwardOddCodes p.1,
    monsterNortonCodeTenForwardColumns p.2))

/-- Each inverse short label is an actual preferred pair-family coordinate. -/
noncomputable def monsterNortonCodeTenInverseShortIndex (p : Fin 2 × Fin 128) : GriessShortIndex :=
  Sum.inl (p.1, monsterNortonCodeTenInversePair p.2)

/-- The original source-spin and physical-column coordinates of the forward tensor packet. -/
def monsterNortonCodeTenForwardTensorIndex (p : Fin 64 × Fin 8) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTenForwardSpinLabel p.1),
    monsterNortonCodeTenForwardColumns p.2)

/-- The original source-spin and physical-column coordinates of the inverse tensor packet. -/
def monsterNortonCodeTenInverseTensorIndex (p : Fin 4 × Fin 1) : SpinIndex × Fin 24 :=
  (golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel p.1),
    monsterNortonCodeTenInverseColumns p.2)

/-- Distinct packet entries have distinct actual forward short coordinates. -/
theorem monsterNortonCodeTenForwardShortIndex_injective :
    Function.Injective monsterNortonCodeTenForwardShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
  exact Prod.ext (ForwardOddCodes_strictMono.injective hp.1)
    (ForwardColumns_strictMono.injective hp.2)

/-- All inverse pair entries are distinct actual original short coordinates. -/
theorem monsterNortonCodeTenInverseShortIndex_injective :
    Function.Injective monsterNortonCodeTenInverseShortIndex := by
  intro p q h
  have hp := Prod.mk.inj (Sum.inl.inj h)
  exact Prod.ext hp.1 (InversePair_injective hp.2)

/-- The forward tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeTenForwardTensorIndex_injective :
    Function.Injective monsterNortonCodeTenForwardTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (ForwardSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (ForwardColumns_strictMono.injective hp.2)

/-- The inverse tensor entries are distinct actual physical basis vectors. -/
theorem monsterNortonCodeTenInverseTensorIndex_injective :
    Function.Injective monsterNortonCodeTenInverseTensorIndex := by
  intro p q h
  have hp := Prod.mk.inj h
  exact Prod.ext (InverseSpinLabel_strictMono.injective
    (golayLabelCoefficients_bijective.injective hp.1))
    (InverseColumns_injective hp.2)

/-- Complete unnormalized integer coefficients of the forward tensor candidate. -/
def monsterNortonCodeTenForwardTensorCoefficient (p : Fin 64 × Fin 8) : ℤ :=
  monsterNortonCodeTenForwardSpinCoefficient p.1 *
    monsterNortonCodeTenForwardLeech (monsterNortonCodeTenForwardColumns p.2)

/-- Complete unnormalized integer coefficients of the inverse tensor candidate. -/
def monsterNortonCodeTenInverseTensorCoefficient (p : Fin 4 × Fin 1) : ℤ :=
  monsterNortonCodeTenInverseSpinCoefficient p.1 *
    monsterNortonCodeTenInverseLeech (monsterNortonCodeTenInverseColumns p.2)

/-- The full forward tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTenForwardTensorCoefficient_sq :
    (∑ p : Fin 64 × Fin 8, monsterNortonCodeTenForwardTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The full inverse tensor coefficient square sum retains the original physical normalization. -/
theorem monsterNortonCodeTenInverseTensorCoefficient_sq :
    (∑ p : Fin 4 × Fin 1, monsterNortonCodeTenInverseTensorCoefficient p ^ 2) = 1024 := by
  decide +kernel

/-- The whole original-coordinate normalized forward mixed packet candidate. -/
noncomputable def monsterNortonCodeTenForwardPacket : GriessSpace :=
  ∑ k : (Fin 32 × Fin 8) ⊕ (Fin 64 × Fin 8),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTenForwardShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTenForwardTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTenForwardShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTenForwardTensorIndex j).1
            (monsterNortonCodeTenForwardTensorIndex j).2) k

/-- The full forward candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTenForwardPacket_norm :
    griessForm monsterNortonCodeTenForwardPacket monsterNortonCodeTenForwardPacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTenForwardShortIndex monsterNortonCodeTenForwardTensorIndex
    monsterNortonCodeTenForwardShortIndex_injective
    monsterNortonCodeTenForwardTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeTen_forward_short_sq
  · exact monsterNortonCodeTenForwardTensorCoefficient_sq

/-- The whole original-coordinate normalized inverse mixed packet candidate. -/
noncomputable def monsterNortonCodeTenInversePacket : GriessSpace :=
  ∑ k : (Fin 2 × Fin 128) ⊕ (Fin 4 × Fin 1),
    Sum.elim (fun i =>
      ((fun p => monsterNortonCodeTenInverseShortCoefficient p.1 p.2) i : ℝ) / 32)
      (fun j => (monsterNortonCodeTenInverseTensorCoefficient j : ℝ) / (32 * Real.sqrt 2)) k •
        Sum.elim (fun i => monsterNortonPureShort (monsterNortonCodeTenInverseShortIndex i))
          (fun j => monsterNortonTensorUnit (monsterNortonCodeTenInverseTensorIndex j).1
            (monsterNortonCodeTenInverseTensorIndex j).2) k

/-- The full inverse candidate has exact Griess norm one in every constituent. -/
theorem monsterNortonCodeTenInversePacket_norm :
    griessForm monsterNortonCodeTenInversePacket monsterNortonCodeTenInversePacket = 1 := by
  apply monsterNortonMixedDyadicPacket_norm
    monsterNortonCodeTenInverseShortIndex monsterNortonCodeTenInverseTensorIndex
    monsterNortonCodeTenInverseShortIndex_injective
    monsterNortonCodeTenInverseTensorIndex_injective
  · rw [Fintype.sum_prod_type]
    exact monsterNortonCodeTen_inverse_short_sq
  · exact monsterNortonCodeTenInverseTensorCoefficient_sq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
