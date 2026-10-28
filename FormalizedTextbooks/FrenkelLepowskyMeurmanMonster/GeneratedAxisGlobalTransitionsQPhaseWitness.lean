/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorColumns

/-! One nonzero actual tensor coefficient determines the central sign of a local Q image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

private theorem coordinateSign_injective : Function.Injective qSign := by
  intro a b hab
  have hs : a + b = 0 := (qSign_eq_one_iff _).mp (by rw [qSign_add, hab, qSign_sq])
  calc
    a = a + (b + b) := by rw [ZModModule.add_self, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [hs, zero_add]

/-- The genuine local tensor representation intertwines the actual full Q conjugation. -/
theorem generatedAxisGlobalTensor_Q_intertwine (f : localFiberSubgroup) (q : Q)
    (T : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation f (localTensorRepresentation (localFiberIncl q) T) =
      localTensorRepresentation (localFiberIncl (spinConjugation f.val.1 q))
        (localTensorRepresentation f T) := by
  have h : f * localFiberIncl q = localFiberIncl (spinConjugation f.val.1 q) * f := by
    rw [localFiberIncl_conjugate]
    group
  rw [← LinearEquiv.mul_apply, ← map_mul, h, map_mul, LinearEquiv.mul_apply]

/-- The actual central Q sign is its real scalar on every physical tensor coordinate. -/
theorem generatedAxisGlobalTensor_Q_central (c : ZMod 2) (T : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation (localFiberIncl (qCentral c)) T = qSign c • T := by
  funext t i
  rw [localFiberQ_tensor_columns]
  change qSign (c + spinDot 0 t) * T (t + 0) i = qSign c * T t i
  simp only [spinDot_zero_left, add_zero]

/-- Equal actual binary coordinates identify a normalized target up to its true central sign. -/
theorem generatedAxisGlobalQ_image_central (f : localFiberSubgroup) (q r : Q)
    (hr : toAdd r.coeff = 0)
    (hb : (spinConjugation f.val.1 q).base = r.base) :
    spinConjugation f.val.1 q =
      qCentral (toAdd (spinConjugation f.val.1 q).coeff) * r := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    exact hb
  · apply toAdd.injective
    rw [qCentral_mul_coeff, hr, add_zero]

/-- A single verified nonzero real coefficient determines the complete actual Q image. -/
theorem generatedAxisGlobalQ_image_of_tensor_coefficient (f : localFiberSubgroup)
    (q r : Q) (c : ZMod 2) (hr : toAdd r.coeff = 0)
    (hb : (spinConjugation f.val.1 q).base = r.base)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24)
    (hn : localTensorRepresentation (localFiberIncl r) (localTensorRepresentation f T) t i ≠ 0)
    (hc : localTensorRepresentation f (localTensorRepresentation (localFiberIncl q) T) t i =
      qSign c * localTensorRepresentation (localFiberIncl r) (localTensorRepresentation f T) t i) :
    spinConjugation f.val.1 q = qCentral c * r := by
  have hp := generatedAxisGlobalQ_image_central f q r hr hb
  have hh := generatedAxisGlobalTensor_Q_intertwine f q T
  rw [hp, map_mul, map_mul, LinearEquiv.mul_apply, generatedAxisGlobalTensor_Q_central] at hh
  have hi := congrArg (fun U => U t i) hh
  change localTensorRepresentation f (localTensorRepresentation (localFiberIncl q) T) t i =
    qSign (toAdd (spinConjugation f.val.1 q).coeff) *
      localTensorRepresentation (localFiberIncl r) (localTensorRepresentation f T) t i at hi
  have he := mul_right_cancel₀ hn (hi.symm.trans hc)
  have hphase := coordinateSign_injective he
  rw [hphase] at hp
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
