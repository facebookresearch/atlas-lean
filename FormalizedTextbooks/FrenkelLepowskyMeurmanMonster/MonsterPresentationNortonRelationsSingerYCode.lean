/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full preferred source-code labels and their exact all-one-code correction. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerSourceAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual full permuted preferred code labels, including their all-one components. -/
def monsterNortonSingerYBasisFull : Fin 11 → Fin 4096 :=
  ![15, 2059, 2055, 2061, 512, 768, 16, 32, 192, 64, 3087]

/-- The exact all-one components of those full code labels. -/
def monsterNortonSingerYBasisHigh : Fin 11 → ℕ := ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check all preferred source code coordinates against the actual linear permutation.
/-- The full source labels are the actual Singer images of the preferred basis codes. -/
theorem monsterNortonSingerYBasisFull_certificate (a : Fin 11) :
    golayLabelCoefficients (monsterNortonSingerYBasisFull a) =
      monsterNortonSingerCode 0 (monsterNortonYCode (monsterNortonSingerYBasisSource a)) := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check each complete code lift and central phase, rather than identifying only binary classes.
/-- The actual full code lift is its low lift times the stated genuine all-one element. -/
theorem monsterNortonSingerYBasisFull_decomposition (a : Fin 11) :
    sourceQCode (monsterNortonSingerYBasisFull a) 0 =
      sourceQCode ⟨(monsterNortonSingerYBasisTarget a).val, by omega⟩ 0 *
        sourceOmegaQ ^ monsterNortonSingerYBasisHigh a := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd (sourceQCode (monsterNortonSingerYBasisFull a) 0).base j) =
      (fun j : Fin 24 => toAdd (sourceQCode
        ⟨(monsterNortonSingerYBasisTarget a).val, by omega⟩ 0 *
          sourceOmegaQ ^ monsterNortonSingerYBasisHigh a).base j)
    fin_cases a <;> decide +kernel
  · apply toAdd.injective
    fin_cases a <;> decide +kernel

/-- The full source code conjugation includes its exact high-component correction. -/
theorem monsterNortonSingerImage_basis_code (a : Fin 11) :
    monsterNortonSingerImage
      (sourceQCode ⟨(monsterNortonSingerYBasisSource a).val, by omega⟩ 0) =
        sourceQCode (monsterNortonSingerYBasisFull a) 0 := by
  apply monsterNortonSingerImage_code
  exact monsterNortonSingerYBasisFull_certificate a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
