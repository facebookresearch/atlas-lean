/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiCorrectionTransportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StabilizerRecognition

/-! The correcting Xi word genuinely preserves the entire original Tenth matrix flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The corrected word in the actual transported Tenth coordinate system. -/
def generatedTenthE7XiActual : leechIsomSubgroup :=
  golayPermutationIsometry generatedTenthE8StandardPermutation *
    generatedTenthE7XiCorrection *
      (golayPermutationIsometry generatedTenthE8StandardPermutation)⁻¹

/-- The corrected word in the original axis coordinates. -/
def generatedTenthE7XiOriginal : leechIsomSubgroup :=
  generatedTenthE7Isometry⁻¹ * generatedTenthE7XiActual * generatedTenthE7Isometry

private theorem standard_commute (x : Fin 24 → ℝ) :
    generatedTenthE7XiCorrection.val
        (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
      generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
        generatedTenthE7XiCorrection.val x := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix
    generatedTenth_e7_xi_projection_commute_integer
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at h
  rw [generatedTenth_e7_xi_correction_apply, generatedTenth_e7_xi_correction_apply,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

private theorem permute_matrix (p : Equiv.Perm (Fin 24))
    (A B : Matrix (Fin 24) (Fin 24) ℝ) (h : ∀ i j, A i j = B (p i) (p j))
    (x : Fin 24 → ℝ) : A *ᵥ (x ∘ p) = (B *ᵥ x) ∘ p := by
  ext i
  change (∑ j, A i j * x (p j)) = ∑ j, B (p i) j * x j
  rw [← Equiv.sum_comp p (fun j => B (p i) j * x j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [h]

private theorem conjugate_commute (p : golayAutomorphismSubgroup) (e : leechIsomSubgroup)
    (A B : Matrix (Fin 24) (Fin 24) ℝ) (h : ∀ i j, A i j = B (p.val i) (p.val j))
    (he : ∀ x, e.val (A *ᵥ x) = A *ᵥ e.val x) (x : Fin 24 → ℝ) :
    (golayPermutationIsometry p * e * (golayPermutationIsometry p)⁻¹).val (B *ᵥ x) =
      B *ᵥ (golayPermutationIsometry p * e * (golayPermutationIsometry p)⁻¹).val x := by
  let y := (golayPermutationIsometry p * e * (golayPermutationIsometry p)⁻¹).val x
  have hy : y ∘ p.val = e.val (x ∘ p.val) := by
    ext j
    change e.val (x ∘ p.val) (p.val.symm (p.val j)) = _
    rw [p.val.symm_apply_apply]
  have h1 := permute_matrix p.val A B h x
  have h2 := permute_matrix p.val A B h y
  rw [hy] at h2
  ext i
  obtain ⟨j, rfl⟩ := p.val.surjective i
  change e.val ((B *ᵥ x) ∘ p.val) (p.val.symm (p.val j)) = (B *ᵥ y) (p.val j)
  rw [p.val.symm_apply_apply, ← h1, he]
  exact congrFun h2 j

/-- The genuine transported move commutes with the entire actual E7 projector. -/
theorem generatedTenth_e7_xi_actual_commute (x : Fin 24 → ℝ) :
    generatedTenthE7XiActual.val
        (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x) =
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ
        generatedTenthE7XiActual.val x := by
  apply conjugate_commute generatedTenthE8StandardPermutation generatedTenthE7XiCorrection
    (generatedTenthE7XiProjection.map (Int.castRingHom ℝ))
    (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ))
  · intro i j
    exact congrArg (Int.castRingHom ℝ) (generatedTenth_e7_xi_projection_transport i j)
  · exact standard_commute

private theorem transported_embedding :
    (golayPermutationIsometry generatedTenthE8StandardPermutation).val
        (leechCoordinateEmbedding generatedTenthE7XiLine) =
      leechCoordinateEmbedding generatedTenthE7DistinguishedVector := by
  change golayRealPermute generatedTenthE8StandardPermutation.val
    (leechCoordinateEmbedding generatedTenthE7XiLine) = _
  rw [golayRealPermute_embedding, generatedTenth_e7_xi_vectors_transport.1]

private theorem conjugate_fixes (p e : leechIsomSubgroup) (x y : Fin 24 → ℝ)
    (hp : p.val x = y) (he : e.val x = x) : (p * e * p⁻¹).val y = y := by
  rw [← hp]
  change p.val (e.val (p.val.symm (p.val x))) = p.val x
  rw [LinearEquiv.symm_apply_apply, he]

/-- The entire actual transported norm-twelve vector is fixed with its positive orientation. -/
theorem generatedTenth_e7_xi_actual_line :
    leechIntegralAction generatedTenthE7XiActual generatedTenthE7NormTwelveLine =
      generatedTenthE7NormTwelveLine := by
  have he : generatedTenthE7XiActual.val
      (leechCoordinateEmbedding generatedTenthE7DistinguishedVector) =
        leechCoordinateEmbedding generatedTenthE7DistinguishedVector := by
    unfold generatedTenthE7XiActual
    exact conjugate_fixes _ _ _ _ transported_embedding generatedTenth_e7_xi_correction_line
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  exact he

/-- This genuine original Co0 word fixes the complete original axis matrix flag. -/
theorem generatedTenth_e7_xi_original_matrix_fix :
    conwayMatrixAction generatedTenthE7XiOriginal (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1 := by
  have ht : generatedTenthE7TransportedSpatial generatedTenthE7XiOriginal =
      generatedTenthE7XiActual := by
    simp [generatedTenthE7TransportedSpatial, generatedTenthE7XiOriginal, mul_assoc]
  apply (generatedTenth_e7_matrix_stabilizer_recognition _).mpr
  rw [ht]
  refine ⟨?_, Or.inl generatedTenth_e7_xi_actual_line⟩
  intro x
  have hc := generatedTenth_e7_xi_actual_commute x
  constructor
  · intro hx
    rw [← hc, hx, map_smul]
  · intro hx
    apply generatedTenthE7XiActual.val.injective
    rw [hc, hx, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
