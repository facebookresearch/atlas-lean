/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQPhaseCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

/-! Nonzero actual odd and tensor coordinates eliminate an Omega-only remaining Q quotient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- A genuine supported odd coordinate eliminates an Omega-only original fixing quotient. -/
theorem generatedTenth_Q_quotient_zero_of_Omega (x : GriessSpace) (q : Q)
    (hq : rhoLocal (inclQ q) x = x) (b : ZMod 2)
    (hbase : toAdd q.base = b • (Pi.single (11 : Fin 24) 1))
    (hOdd : ∃ d : Fin 2048, ∃ i : Fin 24,
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) ≠ 0) :
    toAdd q.base = 0 := by
  obtain ⟨d, i, hn⟩ := hOdd
  have hp := ((generatedFourthQ_full_fixed_iff q x).mp hq).1
    (Sum.inr (Sum.inr (d, i))) hn
  have hc : toAdd (localAxisQPhase (Sum.inr (Sum.inr (d, i))) q) = b := by
    rw [generatedTenth_Q_phase_coordinates, hbase, dotProduct_smul, dotProduct_single]
    have hr (u v : SpinIndex) : Fin.append u v (11 : Fin 24) = u 11 :=
      Fin.append_left u v (11 : Fin 12)
    rw [mul_one, hr, griessOdd_modulation_omega]
    exact smul_eq_mul b (1 : ZMod 2) |>.trans (mul_one b)
  have hb : b = 0 := by rw [← hc, hp]; rfl
  rw [hbase, hb, zero_smul]

/-- A nonzero entire actual tensor eliminates every nonidentity central Q fixer. -/
theorem generatedTenth_Q_eq_one_of_zero_quotient (x : GriessSpace) (q : Q)
    (hq : rhoLocal (inclQ q) x = x) (hbase : toAdd q.base = 0)
    (hT : (griessConwayEncode x).2.2 ≠ 0) : q = 1 := by
  let c := toAdd q.coeff
  have he : q = qCentral c := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      exact hbase
    · rfl
  have hex : ∃ t : SpinIndex, ∃ i : Fin 24, (griessConwayEncode x).2.2 t i ≠ 0 := by
    by_contra! h
    apply hT
    funext t i
    exact h t i
  obtain ⟨t, i, hn⟩ := hex
  have ht := congrFun (((generatedFourthQ_full_fixed_iff q x).mp hq).2 i) t
  rw [he, spinRepresentation_central] at ht
  change qSign c * (griessConwayEncode x).2.2 t i = (griessConwayEncode x).2.2 t i at ht
  have hs : qSign c = 1 := (mul_right_cancel₀ hn (ht.trans (one_mul _).symm))
  have hz : c = 0 := (qSign_eq_one_iff c).mp hs
  rw [he, hz]
  rfl

/-- Actual supported odd coordinates and a nonzero tensor make an Omega-only
full Q stabilizer trivial. -/
theorem generatedTenth_Q_eq_one_of_Omega_quotient (x : GriessSpace) (q : Q)
    (hq : rhoLocal (inclQ q) x = x) (b : ZMod 2)
    (hbase : toAdd q.base = b • (Pi.single (11 : Fin 24) 1))
    (hOdd : ∃ d : Fin 2048, ∃ i : Fin 24,
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) ≠ 0)
    (hT : (griessConwayEncode x).2.2 ≠ 0) : q = 1 :=
  generatedTenth_Q_eq_one_of_zero_quotient x q hq
    (generatedTenth_Q_quotient_zero_of_Omega x q hq b hbase hOdd) hT

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
