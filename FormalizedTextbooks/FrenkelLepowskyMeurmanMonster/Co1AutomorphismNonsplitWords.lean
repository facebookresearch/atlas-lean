/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskSemantics
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskCorrections
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitSpan

/-! The obstruction uses relations in the original faithful Conway action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original quotient word, with the same left-action order as the finite evaluator. -/
def co1NonsplitActualWord : List (Fin 5) → Co1
  | [] => 1
  | k :: w => co1NonsplitActualWord w * monsterCo1FiveGenerator k

/-- Decoding the word evaluator gives the full original binary word action. -/
theorem co1NonsplitMaskRun_base_decode (w : List (Fin 5)) (s : Co1NonsplitMaskState) :
    monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskRun w s).1 =
      w.foldl (fun v k => omegaOrbitBinaryMatrices k *ᵥ v)
        (monsterCo1GeometryBinaryMaskDecode s.1) := by
  induction w generalizing s with
  | nil => rfl
  | cons k w ih =>
    simp only [co1NonsplitMaskRun, List.foldl_cons]
    rw [← co1NonsplitMaskRun, ih]
    exact congrArg (w.foldl (fun v k => omegaOrbitBinaryMatrices k *ᵥ v))
      (co1NonsplitMaskVector_decode k s.1)

/-- The original Conway quotient word acts by the same full binary matrix evaluation. -/
theorem co1NonsplitActualWord_action (w : List (Fin 5)) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (co1NonsplitActualWord w) v =
      w.foldl (fun v k => omegaOrbitBinaryMatrices k *ᵥ v) v := by
  induction w generalizing v with
  | nil => simp [co1NonsplitActualWord]
  | cons k w ih =>
    simp only [co1NonsplitActualWord, map_mul, LinearEquiv.mul_apply, List.foldl_cons]
    rw [ih, co1NonsplitFive_action]

/-- Faithfulness proves each checked original word is literally one in Co₁. -/
theorem co1NonsplitActual_relation (r : Fin 14) :
    co1NonsplitActualWord (co1NonsplitRelationWords r) = 1 := by
  apply co1BinaryAction_injective
  apply LinearEquiv.ext
  intro v
  have hu (i : Fin 24) : co1BinaryAction
      (co1NonsplitActualWord (co1NonsplitRelationWords r)) (Pi.single i 1) =
        Pi.single i 1 := by
    rw [co1NonsplitActualWord_action, ← co1NonsplitMask_unit i]
    have he := co1NonsplitMaskRun_base_decode (co1NonsplitRelationWords r)
      (2 ^ i.val, (0, 0))
    rw [co1NonsplitRelation_mask_base r i] at he
    exact he.symm
  have hv : v = ∑ i : Fin 24, v i • (Pi.single i 1 : Fin 24 → ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  rw [hv]
  simp only [map_sum, map_smul, hu, map_one]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
