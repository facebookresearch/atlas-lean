/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthInverseActions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthForestRoots

/-! Ten actual local words whose binary roots are the ten type-four roots of the Sixth singular
forest: the identity, five original Fifth normalization words, and four products of those
words with actual Fifth-axis stabilizer lifts. Every binary root is computed from the proved
binary actions; the root masks are kernel checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual Ω class is the coordinate mask `2048`. -/
theorem generatedAxisGlobalTwelveSixth_omega_mask :
    toAdd (qQuotHom sourceOmegaQ) = monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 := by
  rw [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic]
  decide +kernel

/-- The binary root of an original Fifth normalization word is its displayed root mask. -/
theorem generatedAxisGlobalTwelveSixth_fifthWord_root (k : Fin 14) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord k)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalFifthRootMask k) := by
  change co1BinaryAction (projH (generatedAxisGlobalFifthShortLocalWord k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = generatedAxisGlobalFifthRootBinary k
  rw [map_inv, ← generatedAxisGlobalFifthShortLocalWord_binary k,
    ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Right multiplication by an actual Fifth stabilizer lift moves a binary root by the
lift's checked inverse action. -/
theorem generatedAxisGlobalTwelveSixth_root_mul (w : H) (k : Fin 19) (m m' : ℕ)
    (hm : m < 2 ^ 24)
    (hw : (generatedAxisGlobalBinaryRoot w).val = monsterCo1GeometryBinaryMaskDecode (n := 24) m)
    (hstep : generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k) m = m') :
    (generatedAxisGlobalBinaryRoot (w * (generatedAxisGlobalFifthGenerator k).val)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) m' := by
  unfold generatedAxisGlobalBinaryRoot
  rw [mul_inv_rev, generatedAxisGlobalBinaryAct_mul,
    generatedAxisGlobalFifthGenerator_inverse_binary]
  have he : (generatedAxisGlobalMaskFiniteEquiv 24).symm
      (generatedAxisGlobalBinaryAct w⁻¹ generatedAxisGlobalBinaryOmega).val =
        (⟨m, hm⟩ : Fin (2 ^ 24)) := by
    apply (generatedAxisGlobalMaskFiniteEquiv 24).injective
    rw [Equiv.apply_symm_apply]
    exact hw
  rw [he]
  change monsterCo1GeometryBinaryMaskDecode
    (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k) m) = _
  rw [hstep]

/-- The ten actual local root words of the Sixth forest, in the order of the type-four roots. -/
def generatedAxisGlobalTwelveSixthRootWord : Fin 10 → H :=
  ![1, generatedAxisGlobalFifthShortLocalWord 0, generatedAxisGlobalFifthShortLocalWord 1,
    generatedAxisGlobalFifthShortLocalWord 2, generatedAxisGlobalFifthShortLocalWord 8,
    generatedAxisGlobalFifthShortLocalWord 9,
    generatedAxisGlobalFifthShortLocalWord 0 * (generatedAxisGlobalFifthGenerator 17).val,
    generatedAxisGlobalFifthShortLocalWord 2 * (generatedAxisGlobalFifthGenerator 18).val,
    generatedAxisGlobalFifthShortLocalWord 1 * (generatedAxisGlobalFifthGenerator 7).val,
    generatedAxisGlobalFifthShortLocalWord 9 * (generatedAxisGlobalFifthGenerator 16).val *
      (generatedAxisGlobalFifthGenerator 17).val]

set_option maxHeartbeats 4000000 in
-- Check the five displayed mask products of the composite root words.
/-- The checked binary root masks of the four composite words. -/
theorem generatedAxisGlobalTwelveSixthRootWord_masks :
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows 17) 1 = 6138124 ∧
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows 18) 17 = 57361 ∧
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows 7) 4 = 2557956 ∧
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows 16) 273 = 1703412 ∧
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows 17) 1703412 =
      1782870 := by
  decide +kernel

/-- Every root word has the displayed type-four root of the Sixth forest. -/
theorem generatedAxisGlobalTwelveSixthRootWord_root (i : Fin 10) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSixthRootWord i)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveSixthLongRootMask i) := by
  obtain ⟨h17, h18, h7, h16, h17'⟩ := generatedAxisGlobalTwelveSixthRootWord_masks
  fin_cases i
  · change (generatedAxisGlobalBinaryAct 1⁻¹ generatedAxisGlobalBinaryOmega).val =
      monsterCo1GeometryBinaryMaskDecode 2048
    rw [inv_one, ← generatedAxisGlobalTwelveSixth_omega_mask]
    change co1BinaryAction (projH 1) (toAdd (qQuotHom sourceOmegaQ)) = _
    rw [map_one, map_one]
    rfl
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 0
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 1
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 2
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 8
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 9
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 17 1 _ (by decide)
      (generatedAxisGlobalTwelveSixth_fifthWord_root 0) h17
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 18 17 _ (by decide)
      (generatedAxisGlobalTwelveSixth_fifthWord_root 2) h18
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 7 4 _ (by decide)
      (generatedAxisGlobalTwelveSixth_fifthWord_root 1) h7
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 17 1703412 _ (by decide)
      (generatedAxisGlobalTwelveSixth_root_mul _ 16 273 _ (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 9) h16) h17'

/-- The ten type-four root masks lie in the genuine binary Ω orbit. -/
theorem generatedAxisGlobalTwelveSixthLongRoot_mem_orbit (i : Fin 10) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSixthLongRootMask i) ∈
      generatedAxisGlobalBinaryOrbit := by
  rw [← generatedAxisGlobalTwelveSixthRootWord_root]
  exact (generatedAxisGlobalBinaryRoot _).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
