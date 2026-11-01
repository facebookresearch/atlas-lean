/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQMask

/-! Exact binary-mask encoding of the original finite coordinates, without any enumeration. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators

/-- Encode an original binary vector by XOR of its occupied coordinate powers. -/
def generatedAxisGlobalMaskEncode (v : Fin 24 → ZMod 2) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v i = 0 then 0 else 2 ^ i.val))

/-- Each coordinate power decodes to its original standard basis vector. -/
theorem generatedAxisGlobalMaskDecode_power (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ i.val) = Pi.single i 1 := by
  funext j
  have h : ∀ i j : Fin 24,
      monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ i.val) j =
        (Pi.single i 1 : Fin 24 → ZMod 2) j := by
    decide +kernel
  exact h i j

/-- Mask encoding recovers every original coordinate, for every actual binary vector. -/
theorem generatedAxisGlobalMaskEncode_actual (v : Fin 24 → ZMod 2) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalMaskEncode v) = v := by
  unfold generatedAxisGlobalMaskEncode
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  have ht : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  have hs : ∀ i : Fin 24,
      monsterCo1GeometryBinaryMaskDecode (n := 24) (if v i = 0 then 0 else 2 ^ i.val) =
        v i • (Pi.single i 1) := by
    intro i
    rcases ht (v i) with h | h
    · simp [h, monsterCo1GeometryBinaryMaskDecode_zero]
    · simp [h, generatedAxisGlobalMaskDecode_power]
  calc
    _ = ∑ i : Fin 24, v i • (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hs i
    _ = v := by
      funext j
      simp [Pi.single_apply]

/-- Every original extraspecial element is its exact encoded lift with its original central bit. -/
theorem generatedAxisGlobalQMaskEncode_normal_form (q : Q) :
    q = qCentral (toAdd q.coeff) *
      generatedAxisGlobalQMask (generatedAxisGlobalMaskEncode (toAdd q.base)) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    exact (generatedAxisGlobalMaskEncode_actual (toAdd q.base)).symm
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change toAdd q.coeff = toAdd q.coeff + 0
    rw [add_zero]

/-- A coefficient-zero original lift is precisely its encoded positive mask lift. -/
theorem generatedAxisGlobalQMaskEncode_positive (q : Q) (hq : q.coeff = 1) :
    q = generatedAxisGlobalQMask (generatedAxisGlobalMaskEncode (toAdd q.base)) := by
  have h := generatedAxisGlobalQMaskEncode_normal_form q
  rw [hq] at h
  change q = qCentral 0 * _ at h
  have hz : qCentral 0 = 1 := by rfl
  simpa only [hz, one_mul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
