/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthRootWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhForestRoots

/-! Twenty-three actual local words whose binary roots are the 23 type-four roots of the Seventh
singular forest: the identity, original Fifth normalization words, and products of those words
with actual Fifth-axis stabilizer lifts. Every binary root is computed from the proved binary
actions; each mask step is kernel checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The binary root of the identity word is the Ω mask `2048`. -/
theorem generatedAxisGlobalTwelveSeventh_one_root :
    (generatedAxisGlobalBinaryRoot (1 : H)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 := by
  change (generatedAxisGlobalBinaryAct 1⁻¹ generatedAxisGlobalBinaryOmega).val =
    monsterCo1GeometryBinaryMaskDecode 2048
  rw [inv_one, ← generatedAxisGlobalTwelveSixth_omega_mask]
  change co1BinaryAction (projH 1) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_one, map_one]
  rfl

/-- The 23 actual local root words of the Seventh forest, in the order of the type-four roots. -/
def generatedAxisGlobalTwelveSeventhRootWord : Fin 23 → H :=
  ![1,
    generatedAxisGlobalFifthShortLocalWord 0,
    generatedAxisGlobalFifthShortLocalWord 12,
    generatedAxisGlobalFifthShortLocalWord 1,
    generatedAxisGlobalFifthShortLocalWord 2,
    generatedAxisGlobalFifthShortLocalWord 3,
    generatedAxisGlobalFifthShortLocalWord 2 *
      (generatedAxisGlobalFifthGenerator 5).val,
    generatedAxisGlobalFifthShortLocalWord 0 *
      (generatedAxisGlobalFifthGenerator 16).val,
    generatedAxisGlobalFifthShortLocalWord 3 *
      (generatedAxisGlobalFifthGenerator 15).val,
    generatedAxisGlobalFifthShortLocalWord 2 *
      (generatedAxisGlobalFifthGenerator 15).val,
    generatedAxisGlobalFifthShortLocalWord 4,
    generatedAxisGlobalFifthShortLocalWord 5,
    generatedAxisGlobalFifthShortLocalWord 5 *
      (generatedAxisGlobalFifthGenerator 4).val,
    generatedAxisGlobalFifthShortLocalWord 8,
    generatedAxisGlobalFifthShortLocalWord 9,
    generatedAxisGlobalFifthShortLocalWord 10,
    generatedAxisGlobalFifthShortLocalWord 0 *
      (generatedAxisGlobalFifthGenerator 17).val,
    generatedAxisGlobalFifthShortLocalWord 2 *
      (generatedAxisGlobalFifthGenerator 17).val,
    1 *
      (generatedAxisGlobalFifthGenerator 18).val *
      (generatedAxisGlobalFifthGenerator 16).val,
    generatedAxisGlobalFifthShortLocalWord 9 *
      (generatedAxisGlobalFifthGenerator 4).val,
    generatedAxisGlobalFifthShortLocalWord 1 *
      (generatedAxisGlobalFifthGenerator 5).val,
    generatedAxisGlobalFifthShortLocalWord 0 *
      (generatedAxisGlobalFifthGenerator 16).val *
      (generatedAxisGlobalFifthGenerator 14).val *
      (generatedAxisGlobalFifthGenerator 17).val,
    generatedAxisGlobalFifthShortLocalWord 13 *
      (generatedAxisGlobalFifthGenerator 4).val]

/-- Every root word has the displayed type-four root of the Seventh forest. -/
theorem generatedAxisGlobalTwelveSeventhRootWord_root (i : Fin 23) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSeventhRootWord i)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveSeventhLongRootMask i) := by
  fin_cases i
  · exact generatedAxisGlobalTwelveSeventh_one_root
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 0
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 12
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 1
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 2
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 3
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 5 17 129041 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 2) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 16 1 3080450 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 0) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 15 22 1446053 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 3) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 15 17 4395183 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 2) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 4
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 5
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 4 97 2242657 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 5) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 8
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 9
  · exact generatedAxisGlobalTwelveSixth_fifthWord_root 10
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 17 1 6138124 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 0) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 17 17 6169980 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 2) (by decide +kernel)
  · have h0 := generatedAxisGlobalTwelveSixth_root_mul _ 18 2048 4196352 (by decide)
        (generatedAxisGlobalTwelveSeventh_one_root) (by decide +kernel)
    exact generatedAxisGlobalTwelveSixth_root_mul _ 16 4196352 4655104 (by decide)
        h0 (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 4 273 706833 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 9) (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 5 4 3737604 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 1) (by decide +kernel)
  · have h0 := generatedAxisGlobalTwelveSixth_root_mul _ 16 1 3080450 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 0) (by decide +kernel)
    have h1 := generatedAxisGlobalTwelveSixth_root_mul _ 14 3080450 4831798 (by decide)
        h0 (by decide +kernel)
    exact generatedAxisGlobalTwelveSixth_root_mul _ 17 4831798 2164742 (by decide)
        h1 (by decide +kernel)
  · exact generatedAxisGlobalTwelveSixth_root_mul _ 4 196612 1900548 (by decide)
        (generatedAxisGlobalTwelveSixth_fifthWord_root 13) (by decide +kernel)

/-- The 23 type-four root masks lie in the genuine binary Ω orbit. -/
theorem generatedAxisGlobalTwelveSeventhLongRoot_mem_orbit (i : Fin 23) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveSeventhLongRootMask i) ∈ generatedAxisGlobalBinaryOrbit := by
  rw [← generatedAxisGlobalTwelveSeventhRootWord_root]
  exact (generatedAxisGlobalBinaryRoot _).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
