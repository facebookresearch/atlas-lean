/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortCoordinates

/-! The entire original middle short vector is transported from its genuine pair support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

private def pairEmbed : ((Fin 2 × Fin 276) → ℝ) →ₗ[ℝ] (GriessShortIndex → ℝ) where
  toFun x r := match r with | Sum.inl p => x p | Sum.inr _ => 0
  map_add' x y := by funext r; cases r <;> simp
  map_smul' c x := by funext r; cases r <;> simp

private theorem pairEmbed_single (p : Fin 2 × Fin 276) (c : ℝ) :
    pairEmbed (Pi.single p c) = Pi.single (Sum.inl p) c := by
  funext r
  cases r <;> simp [pairEmbed, Pi.single_apply]

/-- Any genuine vector supported on pair labels is the sum of its entire pair basis expansion. -/
theorem generatedSeventhXi_pair_support_expansion (x : GriessShortIndex → ℝ)
    (h : ∀ r, x (Sum.inr r) = 0) :
    x = ∑ s : Fin 2, ∑ p : Fin 276, x (Sum.inl (s, p)) •
      Pi.single (Sum.inl (s, p)) (1 : ℝ) := by
  have he : x = pairEmbed (fun p => x (Sum.inl p)) := by
    funext r
    cases r with
    | inl p => rfl
    | inr r => exact h r
  calc
    x = pairEmbed (fun p => x (Sum.inl p)) := he
    _ = pairEmbed (∑ p : Fin 2 × Fin 276, Pi.single p (x (Sum.inl p))) :=
      congrArg pairEmbed (LinearMap.sum_single_apply (fun _ : Fin 2 × Fin 276 => ℝ)
        (fun p => x (Sum.inl p))).symm
    _ = ∑ p : Fin 2 × Fin 276, pairEmbed (Pi.single p (x (Sum.inl p))) := map_sum _ _ _
    _ = ∑ s : Fin 2, ∑ p : Fin 276,
        x (Sum.inl (s, p)) • Pi.single (Sum.inl (s, p)) (1 : ℝ) := by
      simp only [pairEmbed_single]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro p _
      funext r
      simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp


private theorem reindexPairs (e : Equiv.Perm (Fin 276)) (x : GriessShortIndex → ℝ)
    (r : Fin 2 → Fin 276 → GriessShortIndex)
    (hr : r = fun s p => Sum.inl (s, e p)) :
    (∑ s : Fin 2, ∑ p : Fin 276,
      x (Sum.inl (s, p)) • Pi.single (Sum.inl (s, p)) (1 : ℝ)) =
      ∑ s : Fin 2, ∑ p : Fin 276, x (r s p) • Pi.single (r s p) (1 : ℝ) := by
  rw [hr]
  apply Finset.sum_congr rfl
  intro s _
  exact (Equiv.sum_comp e
    (fun p => x (Sum.inl (s, p)) •
      Pi.single (Sum.inl (s, p) : GriessShortIndex) (1 : ℝ))).symm

private theorem transportPairs
    (F : (GriessShortIndex → ℝ) →ₗ[ℝ] (GriessShortIndex → ℝ))
    (x : GriessShortIndex → ℝ) (r y : Fin 2 → Fin 276 → GriessShortIndex)
    (c : Fin 2 → Fin 276 → ℝ)
    (hx : x = ∑ s : Fin 2, ∑ p : Fin 276, x (r s p) • Pi.single (r s p) (1 : ℝ))
    (hy : ∀ s p, F (Pi.single (r s p) (1 : ℝ)) = c s p • Pi.single (y s p) 1) :
    F x = ∑ s : Fin 2, ∑ p : Fin 276, (x (r s p) * c s p) • Pi.single (y s p) 1 := by
  conv_lhs => rw [hx]
  simp_rw [map_sum, map_smul, hy, smul_smul]


/-- The complete initial odd-axis short vector has no omitted pair coordinates. -/
theorem generatedSeventhXi_initial_short_expansion :
    (griessConwayEncode generatedOddAxis).2.1 =
      ∑ s : Fin 2, ∑ p : Fin 276,
        (griessConwayEncode generatedOddAxis).2.1
          (generatedSeventhXiShortInputLabel s p) •
          Pi.single (generatedSeventhXiShortInputLabel s p) (1 : ℝ) := by
  have hx := generatedSeventhXi_pair_support_expansion
    (griessConwayEncode generatedOddAxis).2.1 (by
      intro r
      cases r with
      | inl p => exact generatedAxis_triality_odd_octad_coordinate 0 0 0 p.1 p.2
      | inr p => exact generatedAxis_triality_odd_odd_coordinate 0 p.1 0 p.2 0)
  exact hx.trans (reindexPairs generatedSeventhXiShortInputEquiv
    (griessConwayEncode generatedOddAxis).2.1 generatedSeventhXiShortInputLabel rfl)


/-- Transport of the full original short vector includes every checked preferred-Q phase. -/
theorem generatedSeventhXi_middle_short_expansion :
    localShortRepresentation generatedSeventhLocalFiber (griessConwayEncode generatedOddAxis).2.1 =
      ∑ s : Fin 2, ∑ p : Fin 276,
        ((griessConwayEncode generatedOddAxis).2.1
          (generatedSeventhXiShortInputLabel s p) *
          qSign (generatedSeventhXiShortPhaseBit s p : ZMod 2)) •
          Pi.single (generatedSeventhXiShortOutputLabel s p) (1 : ℝ) := by
  calc
    _ = localShortOperator generatedSeventhLocalFiber
        (griessConwayEncode generatedOddAxis).2.1 := rfl
    _ = _ := transportPairs (localShortOperator generatedSeventhLocalFiber)
      (griessConwayEncode generatedOddAxis).2.1 generatedSeventhXiShortInputLabel
      generatedSeventhXiShortOutputLabel (fun s p => qSign (generatedSeventhXiShortPhaseBit s p))
      generatedSeventhXi_initial_short_expansion generatedSeventhXiShortInput_basis

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
