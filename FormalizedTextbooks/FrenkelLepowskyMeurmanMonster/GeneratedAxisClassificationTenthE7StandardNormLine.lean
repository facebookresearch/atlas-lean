/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7BinaryIntegerSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitGroup

/-! The entire actual standard norm-twelve line and its original signed source coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The actual norm-twelve lattice vector carried into the original standard coordinates. -/
def generatedTenthE7StandardNormTwelveLine : leechIntegral :=
  leechIntegralAction (golayPermutationIsometry generatedTenthE8StandardPermutation)⁻¹
    generatedTenthE7NormTwelveLine

private theorem integer_permute_inverse (p : Equiv.Perm (Fin 24))
    (x y : Fin 24 → ℤ) (h : golayIntegerPermute p x = y) :
    golayIntegerPermute p⁻¹ y = x := by
  rw [← h]
  funext i
  change x (p.symm (p i)) = x i
  rw [p.symm_apply_apply]

/-- All twenty-four coordinates are exactly the original standard line source. -/
theorem generatedTenth_e7_standard_norm_line_source :
    generatedTenthE7StandardNormTwelveLine.val = generatedTenthE7XiLine := by
  unfold generatedTenthE7StandardNormTwelveLine
  have hp : (golayPermutationIsometry generatedTenthE8StandardPermutation)⁻¹ =
      golayPermutationIsometry generatedTenthE8StandardPermutation⁻¹ :=
    (golayPermutationHom.map_inv _).symm
  rw [hp, leechIntegralAction_golayPermutation]
  exact integer_permute_inverse generatedTenthE8StandardPermutation.val
    generatedTenthE7XiLine generatedTenthE7DistinguishedVector
    generatedTenth_e7_xi_vectors_transport.1

/-- The full standard line has exactly the actual six-coordinate outside support. -/
theorem generatedTenth_e7_standard_norm_line_nonzero : ∀ i : Fin 24,
    generatedTenthE7XiLine i ≠ 0 ↔ generatedTenthE7StandardOutside i := by
  decide +kernel

/-- Every original outside coefficient has its exact full binary sign. -/
theorem generatedTenth_e7_standard_norm_line_sign : ∀ i : Fin 6,
    generatedTenthE7XiLine (generatedTenthE7StandardOutsideCoordinates i) =
      4 * generatedTenthE7IntegerSign (generatedTenthE7StandardOutsideSigns i) := by
  decide +kernel

/-- The complete original standard vector transports back to the actual physical line. -/
theorem generatedTenth_e7_standard_norm_line_transport :
    leechIntegralAction (golayPermutationIsometry generatedTenthE8StandardPermutation)
      generatedTenthE7StandardNormTwelveLine = generatedTenthE7NormTwelveLine := by
  unfold generatedTenthE7StandardNormTwelveLine
  rw [map_inv]
  exact LinearEquiv.apply_symm_apply _ _

/-- Every whole actual matrix fixer preserves the entire standard norm-twelve line up to sign. -/
theorem generatedTenth_e7_standard_matrix_norm_line (g : generatedTenthE7StandardMatrixGroup) :
    leechIntegralAction g.val generatedTenthE7StandardNormTwelveLine =
        generatedTenthE7StandardNormTwelveLine ∨
      leechIntegralAction g.val generatedTenthE7StandardNormTwelveLine =
        -generatedTenthE7StandardNormTwelveLine := by
  have hg : conwayMatrixAction (generatedTenthE7OrbitConjugation g.val)
      (griessConwayEncode generatedTenthAxis).1 =
        (griessConwayEncode generatedTenthAxis).1 := g.property
  have h := generatedTenth_e7_matrix_fixer_norm_twelve_line _ hg
  have hc : generatedTenthE7TransportedSpatial (generatedTenthE7OrbitConjugation g.val) =
      golayPermutationIsometry generatedTenthE8StandardPermutation * g.val *
        (golayPermutationIsometry generatedTenthE8StandardPermutation)⁻¹ := by
    simp [generatedTenthE7TransportedSpatial, generatedTenthE7OrbitConjugation,
      generatedTenthE7OrbitTransport, mul_assoc]
  rw [hc] at h
  have ha : leechIntegralAction
      (golayPermutationIsometry generatedTenthE8StandardPermutation * g.val *
        (golayPermutationIsometry generatedTenthE8StandardPermutation)⁻¹)
        generatedTenthE7NormTwelveLine =
      leechIntegralAction (golayPermutationIsometry generatedTenthE8StandardPermutation)
        (leechIntegralAction g.val generatedTenthE7StandardNormTwelveLine) := by
    rw [map_mul, map_mul]
    rfl
  rw [ha, ← generatedTenth_e7_standard_norm_line_transport] at h
  rcases h with h | h
  · exact Or.inl ((leechIntegralAction
      (golayPermutationIsometry generatedTenthE8StandardPermutation)).injective h)
  · right
    apply (leechIntegralAction
      (golayPermutationIsometry generatedTenthE8StandardPermutation)).injective
    rw [map_neg]
    exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
