/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsQuadratic

/-! Exact XOR-parity arithmetic evaluates complete original binary quadratic spin phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Selected source rows contribute their exact binary dot product to the quadratic parity. -/
def generatedSixthMonomialMaskQuadratic (rows : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if n.testBit i.val then monsterCo1GeometryBinaryMaskDot 12 (rows i) n else 0))

/-- The complete XOR parity is the genuine quadratic polynomial on the actual binary vector. -/
theorem generatedSixth_monomial_mask_quadratic (rows : Fin 12 → ℕ) (n : ℕ) :
    (if (generatedSixthMonomialMaskQuadratic rows n).testBit 0 then (1 : ZMod 2) else 0) =
      monsterMonomialQuadratic (monsterCo1GeometryBinaryMaskMatrix rows)
        (monsterCo1GeometryBinaryMaskDecode n) := by
  rw [representativeQuadratic_dot, monsterCo1GeometryBinaryMaskMatrix_mulVec]
  unfold generatedSixthMonomialMaskQuadratic
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  change (∑ i : Fin 12, if (if n.testBit i.val then
      monsterCo1GeometryBinaryMaskDot 12 (rows i) n else 0).testBit 0 then 1 else 0) =
    ∑ i : Fin 12, monsterCo1GeometryBinaryMaskDecode n i *
      (if (monsterCo1GeometryBinaryMaskDot 12 (rows i) n).testBit 0 then 1 else 0)
  apply Finset.sum_congr rfl
  intro i _
  cases h : n.testBit i.val <;> simp [monsterCo1GeometryBinaryMaskDecode, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
