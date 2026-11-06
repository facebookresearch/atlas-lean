/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Twenty-three coordinate lifts determine the actual orthogonal binary spin action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem q_square_central (q : Q) :
    q ^ 2 = qCentral (qBeta (toAdd q.base) (toAdd q.base)) := by
  rw [pow_two]
  apply NormalizedCocycleExtension.Extension.ext
  · exact q_square_base q
  · apply toAdd.injective
    change (toAdd q.coeff + toAdd q.coeff) + qBeta (toAdd q.base) (toAdd q.base) = _
    rw [CharTwo.add_self_eq_zero, zero_add]
    rfl

/-- The binary action preserves the actual square form, as a consequence of Q conjugation. -/
theorem monsterNortonSpinBinary_preserves_square (s : SpinHolomorph) (v : Fin 24 → ZMod 2) :
    qBeta (spinBinaryAction s v) (spinBinaryAction s v) = qBeta v v := by
  have h := congrArg (spinConjugation s) (q_square_central (qSection v))
  rw [map_pow, spinConjugation_central, q_square_central] at h
  have hc := congrArg (fun q : Q => toAdd q.coeff) h
  change qBeta (toAdd (spinConjugation s (qSection v)).base)
    (toAdd (spinConjugation s (qSection v)).base) = qBeta v v at hc
  have hb : spinBinaryAction s v = toAdd (spinConjugation s (qSection v)).base :=
    qBinaryAction_apply (spinConjugation s) (qSection v)
  rw [← hb] at hc
  exact hc

private theorem square_polar (L : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hL : ∀ v, qBeta (L v) (L v) = qBeta v v) (v w : Fin 24 → ZMod 2) :
    qBeta (L v) (L w) + qBeta (L w) (L v) = qBeta v w + qBeta w v := by
  have h := hL (v + w)
  have hv := hL v
  have hw := hL w
  simp only [map_add, qBeta_add_left, qBeta_add_right] at h
  linear_combination h - hv - hw

/-- A square-form isometry fixing every coordinate except odd modulation fixes that one as well. -/
theorem monsterNortonBinary_eq_one_of_twentyThree
    (L : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hL : ∀ v, qBeta (L v) (L v) = qBeta v v)
    (hi : ∀ i : Fin 24, i ≠ 23 → L (Pi.single i 1) = Pi.single i 1) : L = 1 := by
  let e : Fin 24 → ZMod 2 := Pi.single 23 1
  let w : Fin 24 → ZMod 2 := L e
  have hmod (i : Fin 12) : w (Fin.natAdd 12 i) = if i = 11 then 1 else 0 := by
    have hneq : Fin.castAdd 12 i ≠ (23 : Fin 24) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd] at hv
      change _ = (23 : ℕ) at hv
      omega
    have h := square_polar L hL e (Pi.single (Fin.castAdd 12 i) 1)
    rw [hi _ hneq, qBeta_right_single_first, qBeta_single_first,
      qBeta_right_single_first, qBeta_single_first, zero_add, zero_add] at h
    change w (Fin.natAdd 12 i) = e (Fin.natAdd 12 i) at h
    rw [h]
    fin_cases i <;> simp [e]
  have htr (i : Fin 12) (hi11 : i ≠ 11) : w (Fin.castAdd 12 i) = 0 := by
    have hneq : Fin.natAdd 12 i ≠ (23 : Fin 24) := by
      intro h
      apply hi11
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      change _ = (23 : ℕ) at hv
      omega
    have h := square_polar L hL e (Pi.single (Fin.natAdd 12 i) 1)
    rw [hi _ hneq, qBeta_single_second, qBeta_left_single_second,
      qBeta_single_second, qBeta_left_single_second, add_zero, add_zero] at h
    change w (Fin.castAdd 12 i) = e (Fin.castAdd 12 i) at h
    rw [h]
    fin_cases i <;> simp [e]
  have hself : qBeta w w = w 11 := by
    unfold qBeta
    simp_rw [hmod]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  have hlast : w 11 = 0 := by
    have h := hL e
    change qBeta w w = qBeta e e at h
    rw [hself] at h
    change w 11 = qBeta (Pi.single (Fin.natAdd 12 (11 : Fin 12)) 1) e at h
    rw [qBeta_left_single_second] at h
    exact h
  have hw : w = e := by
    ext j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective j
    cases i with
    | inl i =>
      rw [finSumFinEquiv_apply_left]
      by_cases hi11 : i = 11
      · subst i
        change w 11 = e 11
        rw [hlast]
        simp [e]
      · rw [htr i hi11]
        fin_cases i <;> simp [e]
    | inr i =>
      rw [finSumFinEquiv_apply_right, hmod]
      fin_cases i <;> simp [e]
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  intro i c
  have hs : (Pi.single i c : Fin 24 → ZMod 2) = c • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [hs, map_smul, map_smul]
  congr 1
  by_cases hi23 : i = 23
  · subst i
    exact hw
  · exact hi i hi23

/-- Fixing these twenty-three full Q lifts forces the actual binary spin action to be identity. -/
theorem monsterNortonSpinBinary_eq_one_of_twentyThree (s : SpinHolomorph)
    (hi : ∀ i : Fin 24, i ≠ 23 → spinConjugation s (qCoordinateGenerator i) =
      qCoordinateGenerator i) : spinBinaryAction s = 1 := by
  apply monsterNortonBinary_eq_one_of_twentyThree
  · exact monsterNortonSpinBinary_preserves_square s
  · intro i hi23
    have h := qBinaryAction_apply (spinConjugation s) (qCoordinateGenerator i)
    change spinBinaryAction s (Pi.single i 1) =
      toAdd (spinConjugation s (qCoordinateGenerator i)).base at h
    rw [hi i hi23] at h
    exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
