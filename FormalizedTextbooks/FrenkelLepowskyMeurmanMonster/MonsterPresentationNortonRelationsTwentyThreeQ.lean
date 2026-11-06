/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact Q phases remaining after twenty-three coordinate commutation checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTwentyThreeBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddCocode

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem polar_zero_of_commute (q r : Q) (hc : Commute q r) :
    qBeta (toAdd q.base) (toAdd r.base) + qBeta (toAdd r.base) (toAdd q.base) = 0 := by
  have h : q * r * q⁻¹ = r := by
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [q_conjugation_central_phase] at h
  have hz : qCentral (qBeta (toAdd q.base) (toAdd r.base) +
      qBeta (toAdd r.base) (toAdd q.base)) = 1 :=
    mul_right_cancel (h.trans (one_mul r).symm)
  exact congrArg (fun g : Q => toAdd g.coeff) hz

/-- The centralizer in Q of these twenty-three lifts has only the Omega binary direction. -/
theorem monsterNortonQ_twentyThree_base (q : Q)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute q (qCoordinateGenerator i)) :
    toAdd q.base = (toAdd q.base 11) • (Pi.single 11 1 : Fin 24 → ZMod 2) := by
  let v : Fin 24 → ZMod 2 := toAdd q.base
  have hmod (i : Fin 12) : v (Fin.natAdd 12 i) = 0 := by
    have hn : Fin.castAdd 12 i ≠ (23 : Fin 24) := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = 23 at hv
      omega
    have h := polar_zero_of_commute q (qCoordinateGenerator (Fin.castAdd 12 i)) (hi _ hn)
    change qBeta v (Pi.single (Fin.castAdd 12 i) 1) +
      qBeta (Pi.single (Fin.castAdd 12 i) 1) v = 0 at h
    rw [qBeta_right_single_first, qBeta_single_first, zero_add] at h
    exact h
  have htr (i : Fin 12) (hi11 : i ≠ 11) : v (Fin.castAdd 12 i) = 0 := by
    have hn : Fin.natAdd 12 i ≠ (23 : Fin 24) := by
      intro h
      apply hi11
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 12 + i.val = 23 at hv
      omega
    have h := polar_zero_of_commute q (qCoordinateGenerator (Fin.natAdd 12 i)) (hi _ hn)
    change qBeta v (Pi.single (Fin.natAdd 12 i) 1) +
      qBeta (Pi.single (Fin.natAdd 12 i) 1) v = 0 at h
    rw [qBeta_single_second, qBeta_left_single_second, add_zero] at h
    exact h
  have hother (j : Fin 24) (hj : j ≠ 11) : v j = 0 := by
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective j
    cases i with
    | inl i =>
      rw [finSumFinEquiv_apply_left]
      apply htr i
      intro hi11
      subst i
      apply hj
      rfl
    | inr i =>
      rw [finSumFinEquiv_apply_right]
      exact hmod i
  change v = v 11 • (Pi.single 11 1 : Fin 24 → ZMod 2)
  ext j
  by_cases hj : j = 11
  · subst j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
  · simp [Pi.smul_apply, smul_eq_mul, hj, hother j hj]

/-- One actual delta-zero spin coefficient removes both Omega and every central sign. -/
theorem monsterNortonQ_twentyThree_eq_one_of_spin_zero (q : Q)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute q (qCoordinateGenerator i))
    (hf : spinRepresentation q (Pi.single 0 1) 0 = 1) : q = 1 := by
  have hb := monsterNortonQ_twentyThree_base q hi
  change qSign (spinPhase q 0) *
    (Pi.single 0 1 : SpinSpace) (0 + spinTranslation q) = 1 at hf
  simp only [zero_add] at hf
  have ht : spinTranslation q = 0 := by
    by_contra hn
    simp only [Pi.single_apply, hn, ite_false, mul_zero] at hf
    norm_num at hf
  have h11 := congrFun ht 11
  change toAdd q.base 11 = 0 at h11
  have hbase : toAdd q.base = 0 := by rw [hb, h11, zero_smul]
  rw [ht, Pi.single_eq_same, mul_one] at hf
  have hphase : spinPhase q 0 = toAdd q.coeff := by simp [spinPhase, spinDot]
  rw [hphase] at hf
  have hcoeff : toAdd q.coeff = 0 := by
    by_cases hc : toAdd q.coeff = 0
    · exact hc
    · norm_num [qSign, hc] at hf
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact hbase
  · apply toAdd.injective
    exact hcoeff

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
