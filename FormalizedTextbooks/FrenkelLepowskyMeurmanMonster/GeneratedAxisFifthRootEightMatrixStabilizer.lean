/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixActualPairTransport

/-! The full genuine Conway matrix stabilizer of the missing root-eight axis class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full actual Conway subgroup fixing the entire original root-eight matrix. -/
def generatedFifthRootEightMatrixStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedFifthRootEightAxis).1 =
    (griessConwayEncode generatedFifthRootEightAxis).1}
  one_mem' := by
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change conwayMatrixAction (g * h) _ = _
    rw [map_mul, LinearEquiv.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change conwayMatrixAction g⁻¹ _ = _
    rw [← hg, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    exact hg.symm

/-- Actual matrix membership preserves precisely the two distinguished signed lattice lines. -/
theorem generatedFifthRootEightMatrixStabilizer_mem (g : leechIsomSubgroup) :
    g ∈ generatedFifthRootEightMatrixStabilizer ↔
      (leechIntegralAction g generatedFifthRootEightNormTwenty = generatedFifthRootEightNormTwenty ∨
        leechIntegralAction g generatedFifthRootEightNormTwenty =
          -generatedFifthRootEightNormTwenty) ∧
      (leechIntegralAction g generatedFifthRootEightNormFour = generatedFifthRootEightNormFour ∨
        leechIntegralAction g generatedFifthRootEightNormFour =
          -generatedFifthRootEightNormFour) :=
  generatedFifthRootEight_matrix_fix_integral_lines_iff g

/-- The actual simultaneous point stabilizer of the original root-eight flag has order44352000. -/
theorem generatedFifthRootEight_point_stabilizer_card :
    Nat.card (leechNormSixActualPairStabilizer
      generatedFifthRootEightNormFour generatedFifthRootEightNormSix) = 44352000 := by
  exact leechNormSixActualPairStabilizer_card _ _
    generatedFifthRootEight_flag_integer_norms.1
    generatedFifthRootEight_flag_integer_norms.2.1
    generatedFifthRootEight_flag_integer_norms.2.2

/-- Every actual point stabilizer of the original flag fixes the full original matrix. -/
theorem generatedFifthRootEight_point_stabilizer_le :
    leechNormSixActualPairStabilizer generatedFifthRootEightNormFour
      generatedFifthRootEightNormSix ≤ generatedFifthRootEightMatrixStabilizer := by
  intro g hg
  have h := (leechNormSixActualPairStabilizer_mem _ _ _).mp hg
  apply (generatedFifthRootEightMatrixStabilizer_mem g).mpr
  refine ⟨Or.inl ?_, Or.inl h.1⟩
  rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul, h.1, h.2]

/-- Genuine central negation fixes the complete original matrix. -/
def generatedFifthRootEightMatrixNegation : generatedFifthRootEightMatrixStabilizer :=
  ⟨golaySignIsometry leechRootNegationCode,
    (generatedFifthRootEightMatrixStabilizer_mem _).mpr
      ⟨Or.inr (leechRootNegationCode_action _), Or.inr (leechRootNegationCode_action _)⟩⟩

/-- A genuine whole matrix stabilizer fixes the low orientation and reverses the high one. -/
theorem generatedFifthRootEight_matrix_mate_exists :
    ∃ g : generatedFifthRootEightMatrixStabilizer,
      leechIntegralAction g.val generatedFifthRootEightNormFour = generatedFifthRootEightNormFour ∧
        leechIntegralAction g.val generatedFifthRootEightNormSix =
          generatedFifthRootEightNormFour - generatedFifthRootEightNormSix := by
  obtain ⟨g, hx, hy⟩ := leechNormSixActualPair_mate_transport
    generatedFifthRootEightNormFour generatedFifthRootEightNormSix
    generatedFifthRootEight_flag_integer_norms.1
    generatedFifthRootEight_flag_integer_norms.2.1
    generatedFifthRootEight_flag_integer_norms.2.2
  have hu : leechIntegralAction g generatedFifthRootEightNormTwenty =
      -generatedFifthRootEightNormTwenty := by
    rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul, hx, hy]
    abel
  exact ⟨⟨g, (generatedFifthRootEightMatrixStabilizer_mem g).mpr ⟨Or.inr hu, Or.inl hx⟩⟩,
    hx, hy⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
