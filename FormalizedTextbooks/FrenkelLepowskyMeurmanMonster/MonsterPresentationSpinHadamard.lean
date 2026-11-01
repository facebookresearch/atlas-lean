/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The explicit one-coordinate Fourier change between the source spin plus/minus bases. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinPermutation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The last binary spin coordinate, corresponding to the all-one codeword. -/
def monsterSpinOmegaVector : SpinIndex := Pi.single 11 1

/-- Change the last coordinate of an actual spin label. -/
def monsterSpinOmegaFlip (t : SpinIndex) : SpinIndex := t + monsterSpinOmegaVector

/-- This explicit coordinate change is an involution. -/
theorem monsterSpinOmegaFlip_involutive : Function.Involutive monsterSpinOmegaFlip := by
  intro t
  ext i
  change (t i + monsterSpinOmegaVector i) + monsterSpinOmegaVector i = t i
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Two actual last-coordinate flips cancel. -/
theorem monsterSpinOmegaFlip_double (t : SpinIndex) :
    monsterSpinOmegaFlip (monsterSpinOmegaFlip t) = t := monsterSpinOmegaFlip_involutive t

/-- The last-coordinate change as a finite permutation for exact sum reindexing. -/
def monsterSpinOmegaFlipEquiv : Equiv.Perm SpinIndex :=
  Function.Involutive.toPerm monsterSpinOmegaFlip monsterSpinOmegaFlip_involutive

/-- Changing the last coordinate reverses its Schrödinger sign. -/
theorem monsterSpinOmegaFlip_sign (t : SpinIndex) :
    qSign ((monsterSpinOmegaFlip t) 11) = -qSign (t 11) := by
  change qSign (t 11 + 1) = _
  rw [qSign_add, qSign_one]
  ring

/-- The source plus/minus change of basis, with the exact real normalization. -/
noncomputable def monsterSpinHadamard : SpinSpace →ₗ[ℝ] SpinSpace where
  toFun f t := (qSign (t 11) * f t + f (monsterSpinOmegaFlip t)) / Real.sqrt 2
  map_add' f g := by ext t; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Its coordinate formula avoids unfolding representation wrappers. -/
theorem monsterSpinHadamard_apply (f : SpinSpace) (t : SpinIndex) :
    monsterSpinHadamard f t =
      (qSign (t 11) * f t + f (monsterSpinOmegaFlip t)) / Real.sqrt 2 := rfl

/-- The exact normalization makes the one-coordinate Fourier operator involutive. -/
theorem monsterSpinHadamard_involutive : Function.Involutive monsterSpinHadamard := by
  intro f
  ext t
  simp only [monsterSpinHadamard_apply, monsterSpinOmegaFlip_sign,
    monsterSpinOmegaFlip_involutive t]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq := qSign_sq (t 11)
  field_simp [hs]
  rw [hsq]
  linear_combination f t * hq

/-- Reindexing by the actual flip moves it from the first factor to the second. -/
theorem monsterSpinOmegaFlip_pairing (f g : SpinSpace) :
    (∑ t, f (monsterSpinOmegaFlip t) * g t) =
      ∑ t, f t * g (monsterSpinOmegaFlip t) := by
  have h := Equiv.sum_comp monsterSpinOmegaFlipEquiv
    (fun t => f t * g (monsterSpinOmegaFlip t))
  change (∑ t, f (monsterSpinOmegaFlip t) *
    g (monsterSpinOmegaFlip (monsterSpinOmegaFlip t))) = _ at h
  simpa only [monsterSpinOmegaFlip_double] using h

/-- The source Fourier operator is self-adjoint for the actual spin pairing. -/
theorem monsterSpinHadamard_selfAdjoint (f g : SpinSpace) :
    (∑ t, monsterSpinHadamard f t * g t) = ∑ t, f t * monsterSpinHadamard g t := by
  have hL (t : SpinIndex) : monsterSpinHadamard f t * g t =
      ((qSign (t 11) * f t + f (monsterSpinOmegaFlip t)) * g t) / Real.sqrt 2 := by
    rw [monsterSpinHadamard_apply]
    ring
  have hR (t : SpinIndex) : f t * monsterSpinHadamard g t =
      (f t * (qSign (t 11) * g t + g (monsterSpinOmegaFlip t))) / Real.sqrt 2 := by
    rw [monsterSpinHadamard_apply]
    ring
  simp only [hL, hR]
  rw [← Finset.sum_div, ← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / Real.sqrt 2)
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply Finset.sum_congr rfl
    intro t _
    ring
  · rw [monsterSpinOmegaFlip_pairing]

/-- The plus/minus basis change preserves the actual spin pairing. -/
theorem monsterSpinHadamard_pairing (f g : SpinSpace) :
    (∑ t, monsterSpinHadamard f t * monsterSpinHadamard g t) = ∑ t, f t * g t := by
  rw [monsterSpinHadamard_selfAdjoint, monsterSpinHadamard_involutive g]

/-- The concrete Fourier change of basis as an actual real linear equivalence. -/
noncomputable def monsterSpinHadamardEquiv : SpinSpace ≃ₗ[ℝ] SpinSpace :=
  { monsterSpinHadamard with
    invFun := monsterSpinHadamard
    left_inv := monsterSpinHadamard_involutive
    right_inv := monsterSpinHadamard_involutive }

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
