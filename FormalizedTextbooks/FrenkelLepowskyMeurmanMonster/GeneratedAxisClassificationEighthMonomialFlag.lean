/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMonomialMatrix

/-! Recognizing the exact permutation flag inside actual matrix-fixing monomial maps. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fixing the dodecad projection is equivalent to fixing its original codeword. -/
theorem generatedEighth_monomial_dodecad_fix_iff (c : golayCode)
    (p : golayAutomorphismSubgroup) :
    conwayMatrixAction (golayMonomialPair (c, p)) generatedEighthDodecadProjection =
      generatedEighthDodecadProjection ↔
        golayPermute p.val generatedEighthDodecadWord.val = generatedEighthDodecadWord.val := by
  unfold generatedEighthDodecadProjection
  rw [generatedEighth_monomial_diagonal]
  constructor
  · intro hm
    funext i
    have he := congrArg (fun a : Matrix (Fin 24) (Fin 24) ℝ => a i i) hm
    simp only [Matrix.diagonal_apply, ite_true] at he
    change generatedEighthDodecadWord.val (p.val.symm i) = generatedEighthDodecadWord.val i
    rw [generatedEighth_dodecad_coordinate, generatedEighth_dodecad_coordinate]
    cases ha : Nat.testBit 0xc5066f (p.val.symm i).val <;>
      cases hb : Nat.testBit 0xc5066f i.val <;> simp_all [golayBooleanCast]
  · intro hw
    ext i j
    by_cases hij : i = j
    · subst j
      have he := congrFun hw i
      change generatedEighthDodecadWord.val (p.val.symm i) = generatedEighthDodecadWord.val i at he
      rw [generatedEighth_dodecad_coordinate, generatedEighth_dodecad_coordinate] at he
      cases ha : Nat.testBit 0xc5066f (p.val.symm i).val <;>
        cases hb : Nat.testBit 0xc5066f i.val <;>
          simp_all [golayBooleanCast]
    · simp [hij]

/-- Fixing the distinguished coordinate line is equivalent to fixing coordinate 20. -/
theorem generatedEighth_monomial_line_fix_iff (c : golayCode)
    (p : golayAutomorphismSubgroup) :
    conwayMatrixAction (golayMonomialPair (c, p)) generatedEighthCoordinateLineProjection =
      generatedEighthCoordinateLineProjection ↔ p.val 20 = 20 := by
  unfold generatedEighthCoordinateLineProjection
  rw [generatedEighth_monomial_diagonal]
  constructor
  · intro hm
    have he := congrArg (fun a : Matrix (Fin 24) (Fin 24) ℝ => a (p.val 20) (p.val 20)) hm
    simp only [Matrix.diagonal_apply, ite_true, p.val.symm_apply_apply] at he
    by_contra hp
    simp [hp] at he
  · intro hp
    have hi (i : Fin 24) : p.val.symm i = 20 ↔ i = 20 := by
      rw [Equiv.symm_apply_eq, hp]
    ext i j
    simp only [Matrix.diagonal_apply, hi]

/-- Fixing the actual eighth matrix is equivalent to preserving its actual coordinate flag. -/
theorem generatedEighth_monomial_matrix_fix_iff (c : golayCode)
    (p : golayAutomorphismSubgroup) :
    conwayMatrixAction (golayMonomialPair (c, p)) (griessConwayEncode generatedEighthAxis).1 =
      (griessConwayEncode generatedEighthAxis).1 ↔
        p ∈ generatedEighthPermutationFlagStabilizer := by
  rw [generatedEighth_matrix_stabilizer_iff, generatedEighth_monomial_dodecad_fix_iff,
    generatedEighth_monomial_line_fix_iff, generatedEighthPermutationFlagStabilizer_mem]
  exact and_comm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
