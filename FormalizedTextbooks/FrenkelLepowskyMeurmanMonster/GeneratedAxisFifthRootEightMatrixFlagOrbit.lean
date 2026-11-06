/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightMatrixStabilizer

/-! The four actual integral flag orientations under the complete original root-eight matrix
stabilizer, with genuine Conway witnesses for all four. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The four actual oriented flags corresponding to the two independent distinguished lines. -/
def generatedFifthRootEightFlagOrientation : Fin 4 → leechIntegral × leechIntegral :=
  ![(generatedFifthRootEightNormFour, generatedFifthRootEightNormSix),
    (generatedFifthRootEightNormFour,
      generatedFifthRootEightNormFour - generatedFifthRootEightNormSix),
    (-generatedFifthRootEightNormFour, -generatedFifthRootEightNormSix),
    (-generatedFifthRootEightNormFour,
      generatedFifthRootEightNormSix - generatedFifthRootEightNormFour)]

/-- Two original integral coordinates separate every actual flag orientation. -/
theorem generatedFifthRootEightFlagOrientation_injective :
    Function.Injective generatedFifthRootEightFlagOrientation := by
  have hcodes : ∀ i : Fin 4,
      ((generatedFifthRootEightFlagOrientation i).1.val 16,
        (generatedFifthRootEightFlagOrientation i).2.val 16) =
      (![(4, 0), (4, 4), (-4, 0), (-4, -4)] : Fin 4 → ℤ × ℤ) i := by
    decide +kernel
  have hi : Function.Injective
      (![(4, 0), (4, 4), (-4, 0), (-4, -4)] : Fin 4 → ℤ × ℤ) := by decide +kernel
  intro i j h
  apply hi
  rw [← hcodes i, ← hcodes j, h]

/-- Every element of the genuine whole matrix stabilizer sends the actual flag to one of its
four original integral orientations. -/
theorem generatedFifthRootEight_matrix_flag_image (g : generatedFifthRootEightMatrixStabilizer) :
    g • (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix) ∈
      Set.range generatedFifthRootEightFlagOrientation := by
  rcases (generatedFifthRootEightMatrixStabilizer_mem g.val).mp g.property with ⟨hU, hx⟩
  rcases hU with hU | hU <;> rcases hx with hx | hx
  · have hy : leechIntegralAction g.val generatedFifthRootEightNormSix =
        generatedFifthRootEightNormSix := by
      apply Subtype.ext
      funext i
      rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul] at hU
      have h := congrArg (fun w : leechIntegral => w.val i) hU
      rw [hx] at h
      change 2 * (leechIntegralAction g.val generatedFifthRootEightNormSix).val i -
        generatedFifthRootEightNormFour.val i =
        2 * generatedFifthRootEightNormSix.val i - generatedFifthRootEightNormFour.val i at h
      omega
    exact ⟨0, (Prod.ext hx hy).symm⟩
  · have hy : leechIntegralAction g.val generatedFifthRootEightNormSix =
        generatedFifthRootEightNormSix - generatedFifthRootEightNormFour := by
      apply Subtype.ext
      funext i
      rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul] at hU
      have h := congrArg (fun w : leechIntegral => w.val i) hU
      rw [hx] at h
      change 2 * (leechIntegralAction g.val generatedFifthRootEightNormSix).val i -
        -generatedFifthRootEightNormFour.val i =
        2 * generatedFifthRootEightNormSix.val i - generatedFifthRootEightNormFour.val i at h
      change (leechIntegralAction g.val generatedFifthRootEightNormSix).val i =
        generatedFifthRootEightNormSix.val i - generatedFifthRootEightNormFour.val i
      omega
    exact ⟨3, (Prod.ext hx hy).symm⟩
  · have hy : leechIntegralAction g.val generatedFifthRootEightNormSix =
        generatedFifthRootEightNormFour - generatedFifthRootEightNormSix := by
      apply Subtype.ext
      funext i
      rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul] at hU
      have h := congrArg (fun w : leechIntegral => w.val i) hU
      rw [hx] at h
      change 2 * (leechIntegralAction g.val generatedFifthRootEightNormSix).val i -
        generatedFifthRootEightNormFour.val i =
        -(2 * generatedFifthRootEightNormSix.val i - generatedFifthRootEightNormFour.val i) at h
      change (leechIntegralAction g.val generatedFifthRootEightNormSix).val i =
        generatedFifthRootEightNormFour.val i - generatedFifthRootEightNormSix.val i
      omega
    exact ⟨1, (Prod.ext hx hy).symm⟩
  · have hy : leechIntegralAction g.val generatedFifthRootEightNormSix =
        -generatedFifthRootEightNormSix := by
      apply Subtype.ext
      funext i
      rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul] at hU
      have h := congrArg (fun w : leechIntegral => w.val i) hU
      rw [hx] at h
      change 2 * (leechIntegralAction g.val generatedFifthRootEightNormSix).val i -
        -generatedFifthRootEightNormFour.val i =
        -(2 * generatedFifthRootEightNormSix.val i - generatedFifthRootEightNormFour.val i) at h
      change (leechIntegralAction g.val generatedFifthRootEightNormSix).val i =
        -generatedFifthRootEightNormSix.val i
      omega
    exact ⟨2, (Prod.ext hx hy).symm⟩

/-- Every original orientation is attained by an actual element of the whole matrix stabilizer. -/
theorem generatedFifthRootEight_matrix_flag_reaches (i : Fin 4) :
    ∃ g : generatedFifthRootEightMatrixStabilizer,
      g • (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix) =
        generatedFifthRootEightFlagOrientation i := by
  obtain ⟨f, hx, hy⟩ := generatedFifthRootEight_matrix_mate_exists
  fin_cases i
  · exact ⟨1, one_smul _ _⟩
  · exact ⟨f, Prod.ext hx hy⟩
  · refine ⟨generatedFifthRootEightMatrixNegation, ?_⟩
    exact Prod.ext (leechRootNegationCode_action _) (leechRootNegationCode_action _)
  · refine ⟨generatedFifthRootEightMatrixNegation * f, ?_⟩
    change (leechIntegralAction
      ((golaySignIsometry leechRootNegationCode) * f.val) generatedFifthRootEightNormFour,
      leechIntegralAction ((golaySignIsometry leechRootNegationCode) * f.val)
        generatedFifthRootEightNormSix) =
      (-generatedFifthRootEightNormFour,
        generatedFifthRootEightNormSix - generatedFifthRootEightNormFour)
    simp only [map_mul, LinearEquiv.mul_apply, hx, hy,
      leechRootNegationCode_action, neg_sub]

/-- The actual whole matrix stabilizer has exactly the four distinguished oriented flags. -/
theorem generatedFifthRootEight_matrix_flag_orbit :
    MulAction.orbit generatedFifthRootEightMatrixStabilizer
      (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix) =
        Set.range generatedFifthRootEightFlagOrientation := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    exact generatedFifthRootEight_matrix_flag_image g
  · rintro ⟨i, rfl⟩
    exact generatedFifthRootEight_matrix_flag_reaches i

/-- The four actual attained flag orientations give orbit cardinality four. -/
theorem generatedFifthRootEight_matrix_flag_orbit_card :
    Nat.card (MulAction.orbit generatedFifthRootEightMatrixStabilizer
      (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix)) = 4 := by
  rw [generatedFifthRootEight_matrix_flag_orbit,
    ← Nat.card_congr (Equiv.ofInjective generatedFifthRootEightFlagOrientation
      generatedFifthRootEightFlagOrientation_injective), Nat.card_eq_fintype_card,
    Fintype.card_fin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
