/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal short Norton words supplying diagonal points and source triality for generation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555ActualWreathGeneration

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual factor diagonal is a homomorphism into the actual wreath base. -/
noncomputable def y555ActualWreathDiagonal : G →* G ≀ᵣ WreathParity :=
  y555WreathBase.comp ((MonoidHom.id G).prod (MonoidHom.id G))

/-- The two-letter point-center word is the actual diagonal of the point parameter. -/
theorem y555NortonActual_point_center_word (i : Fin 6) :
    y555NortonActualCandidate (y555NortonPointVertex i) * y555NortonActualCandidate none =
      y555ActualWreathDiagonal (y555NortonPoint i) := by
  change y555WreathReflection
    (y555NortonParameter monsterSourceTriality (y555NortonPointVertex i)) *
      y555WreathReflection 1 = _
  rw [y555NortonParameter_point, y555WreathReflection_mul, inv_one, mul_one, mul_one]
  have hi : (y555NortonPoint i)⁻¹ = y555NortonPoint i := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, y555NortonPoint_sq]
  rw [hi]
  rfl

/-- All six actual point diagonals already lie in the fixed Norton generated subgroup. -/
theorem y555NortonActual_point_diagonal_mem (i : Fin 6) :
    y555ActualWreathDiagonal (y555NortonPoint i) ∈ y555NortonActualGeneratedWreath := by
  rw [← y555NortonActual_point_center_word]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)
    (Subgroup.subset_closure ⟨none, rfl⟩)

/-- Conjugating an outer reflection by a factor diagonal conjugates its actual parameter. -/
theorem y555WreathReflection_diagonal_conjugate {M : Type*} [Group M] (v m : M) :
    y555WreathBase (v, v) * y555WreathReflection m * (y555WreathBase (v, v))⁻¹ =
      y555WreathReflection (v * m * v⁻¹) := by
  rw [← map_inv]
  apply RegularWreathProduct.ext
  · funext x
    rcases wreathParity_cases x with rfl | rfl <;>
      simp [RegularWreathProduct.mul_left, y555WreathBase, y555WreathReflection,
        mul_assoc, show wreathFlip ≠ 1 by decide]
  · simp [RegularWreathProduct.mul_right, y555WreathBase, y555WreathReflection]

/-- Swap conjugation takes the reflection parameter to its inverse. -/
theorem y555WreathReflection_swap_conjugate {M : Type*} [Group M] (m : M) :
    wreathSwap M * y555WreathReflection m * wreathSwap M = y555WreathReflection m⁻¹ := by
  apply RegularWreathProduct.ext
  · funext x
    rcases wreathParity_cases x with rfl | rfl <;>
      simp [RegularWreathProduct.mul_left, wreathSwap, y555WreathReflection,
        wreathFlip_inv, wreathFlip_sq, show wreathFlip ≠ 1 by decide]
  · simp [RegularWreathProduct.mul_right, wreathSwap, y555WreathReflection, wreathFlip_sq]

/-- The actual diagonal of v turns the already included first line into source triality.
This is the explicit conjugation word; no new generator is adjoined. -/
theorem y555NortonActual_triality_mem_of_v_diagonal
    (hv : y555ActualWreathDiagonal y555NortonV ∈ y555NortonActualGeneratedWreath) :
    y555WreathReflection monsterSourceTriality ∈ y555NortonActualGeneratedWreath := by
  let S := y555NortonActualGeneratedWreath
  have hL : y555WreathReflection
      (y555NortonLine monsterSourceTriality 0) ∈ S :=
    Subgroup.subset_closure ⟨some (0, 0), rfl⟩
  have hd : y555ActualWreathDiagonal y555NortonV *
      y555WreathReflection monsterSourceTriality⁻¹ *
        (y555ActualWreathDiagonal y555NortonV)⁻¹ =
      y555WreathReflection (y555NortonLine monsterSourceTriality 0) := by
    rw [y555NortonActualLine_zero]
    exact y555WreathReflection_diagonal_conjugate _ _
  have ht : y555WreathReflection monsterSourceTriality⁻¹ ∈ S := by
    have hm := S.mul_mem (S.mul_mem (S.inv_mem hv) hL) hv
    rw [← hd] at hm
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hm
  have hm := S.mul_mem (S.mul_mem y555NortonActualGeneratedWreath_swap ht)
    y555NortonActualGeneratedWreath_swap
  simpa only [y555WreathReflection_swap_conjugate, inv_inv] using hm

/-- Actual diagonal H inclusion alone suffices to generate the full fixed Norton wreath:
the explicit v/first-line/swap word above supplies its source triality prerequisite. -/
theorem y555NortonActualGeneratedWreath_eq_top_of_local_diagonal
    (hH : ∀ h : H, y555WreathBase (localIntoGenerated h, localIntoGenerated h) ∈
      y555NortonActualGeneratedWreath) : y555NortonActualGeneratedWreath = ⊤ := by
  apply y555NortonActualGeneratedWreath_eq_top hH
  apply y555NortonActual_triality_mem_of_v_diagonal
  exact hH (inclQ y555NortonVQ)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
