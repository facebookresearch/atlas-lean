/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The literal Norton candidate family with the checked inverse-transpose triality assignment.
All factors now refer to named elements of the actual generated group G.
The involution and listed Coxeter relations are proved; the remaining source relations,
wreath generation and full Y555 presentation kernel are not asserted.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationTrialitySource

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual source y lift uses the checked source t1 assignment. -/
noncomputable def y555NortonActualY (d : Fin 4096) (ε : ZMod 2) : ↥G :=
  y555NortonY monsterSourceTriality d ε

/-- Its conjugation orientation is explicit and differs from the earlier algebraic Y wrapper. -/
theorem y555NortonActualY_word (d : Fin 4096) (ε : ZMod 2) :
    y555NortonActualY d ε =
      extraIntoGenerated * sourceGeneratedCode d ε * extraIntoGenerated⁻¹ := by
  simp only [y555NortonActualY, y555NortonY, monsterSourceTriality, inv_inv]

/-- The actual literal Norton u word, with every source tag fixed. -/
noncomputable def y555NortonActualU : ↥G := y555NortonU monsterSourceTriality

/-- The sixteen actual coordinate parameters of the Norton family. -/
noncomputable def y555NortonActualParameter : Y555Vertex → ↥G :=
  y555NortonParameter monsterSourceTriality

/-- Explicit candidate images for the independent Y555 generators in the actual G wreath C2. -/
noncomputable def y555NortonActualCandidate : Y555Vertex → ↥G ≀ᵣ WreathParity :=
  y555NortonCandidate monsterSourceTriality

/-- All sixteen independent involution relators hold for the actual candidate family. -/
theorem y555NortonActualCandidate_square (v : Y555Vertex) :
    y555NortonActualCandidate v ^ 2 = 1 := y555NortonCandidate_square _ _

/-- The actual distinguished generator is exactly the swap of the two named factors. -/
theorem y555NortonActualCandidate_center :
    y555NortonActualCandidate none = wreathSwap ↥G := y555NortonCandidate_center _

/-- The fifteen distinct point pairs satisfy their actual order-two Coxeter checks. -/
theorem y555NortonActualCandidate_points_square (i j : Fin 6) :
    (y555NortonActualCandidate (y555NortonPointVertex i) *
      y555NortonActualCandidate (y555NortonPointVertex j)) ^ 2 = 1 :=
  y555NortonCandidate_points_square _ _ _

/-- All six center-point pairs satisfy their actual order-two Coxeter checks. -/
theorem y555NortonActualCandidate_center_point_square (i : Fin 6) :
    (y555NortonActualCandidate none *
      y555NortonActualCandidate (y555NortonPointVertex i)) ^ 2 = 1 :=
  y555NortonCandidate_center_point_square _ _

/-- The first line parameter is an actual conjugate of the inverse source triality. -/
theorem y555NortonActualLine_zero :
    y555NortonLine monsterSourceTriality 0 =
      y555NortonV * monsterSourceTriality⁻¹ * y555NortonV⁻¹ := by
  simp only [y555NortonLine, y555NortonConjugate, Fin.val_zero, pow_zero,
    inv_one, one_mul, mul_one, mul_inv_rev]
  rw [mul_assoc]

/-- The first line parameter has cube one in the named G. -/
theorem y555NortonActualLine_zero_cube :
    y555NortonLine monsterSourceTriality 0 ^ 3 = 1 := by
  rw [y555NortonActualLine_zero, conj_pow, inv_pow, monsterSourceTriality_cube]
  simp

/-- The first adjacent center-line Coxeter relation holds in the actual wreath product. -/
theorem y555NortonActualCandidate_center_first_line_cube :
    (y555NortonActualCandidate none *
      y555NortonActualCandidate (some (0, 0))) ^ 3 = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  change (1 * (y555NortonLine monsterSourceTriality 0)⁻¹) ^ 3 = 1
  rw [one_mul, inv_pow, y555NortonActualLine_zero_cube, inv_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
