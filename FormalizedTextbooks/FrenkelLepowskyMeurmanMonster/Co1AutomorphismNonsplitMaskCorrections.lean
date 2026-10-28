/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskData

/-! The 120 symbolic coordinates represent every linear generator correction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original generator and base-coordinate positions in the full correction space. -/
def co1NonsplitVariableIndex (k : Fin 5) (i : Fin 24) : Fin 120 :=
  ⟨24 * k.val + i.val, by omega⟩

/-- A single bit is the genuine coordinate unit, in every finite binary dimension. -/
theorem co1NonsplitMask_unit {n : ℕ} (i : Fin n) :
    monsterCo1GeometryBinaryMaskDecode (2 ^ i.val) =
      (Pi.single i 1 : Fin n → ZMod 2) := by
  ext j
  by_cases h : i = j
  · subst j
    simp [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_two_pow_self]
  · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
    simp [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_two_pow_of_ne hv, h]

/-- Variable-mask evaluation is exactly the linear functional on the selected input bits. -/
theorem co1NonsplitMaskVariables_dot (k : Fin 5) (v : ℕ) (p : Fin 120 → ZMod 2) :
    monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskVariables k v) ⬝ᵥ p =
      ∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode v i *
        p (co1NonsplitVariableIndex k i) := by
  unfold co1NonsplitMaskVariables
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn,
    sum_dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  cases hv : v.testBit i.val
  · simp [hv, monsterCo1GeometryBinaryMaskDecode_zero,
      monsterCo1GeometryBinaryMaskDecode]
  · have hu := co1NonsplitMask_unit (co1NonsplitVariableIndex k i)
    simpa [monsterCo1GeometryBinaryMaskDecode, hv, co1NonsplitVariableIndex,
      single_one_dotProduct] using congrArg (fun x => x ⬝ᵥ p) hu

/-- Every binary linear functional is determined by its original coordinate-unit values. -/
theorem co1NonsplitLinear_unit_sum
    (f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v : Fin 24 → ZMod 2) :
    f v = ∑ i : Fin 24, v i * f (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 24, v i • (Pi.single i 1 : Fin 24 → ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
