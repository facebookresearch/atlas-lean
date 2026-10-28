/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagLineFixing

/-! Every complete actual signed flag candidate fixes the entire original Tenth matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

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

/-- All92160 genuine complete signed candidates belong to the entire actual matrix group. -/
theorem generatedTenth_e7_signed_flag_matrix_mem (v : generatedTenthE7SignedFlagCandidates) :
    generatedTenthE7SignedFlagSpatial v ∈ generatedTenthE7StandardMatrixGroup := by
  let p := golayPermutationIsometry generatedTenthE8StandardPermutation
  let g := generatedTenthE7SignedFlagSpatial v
  let e := p * g * p⁻¹
  have ht : generatedTenthE7TransportedSpatial (generatedTenthE7OrbitConjugation g) = e := by
    simp [e, p, generatedTenthE7TransportedSpatial, generatedTenthE7OrbitConjugation,
      generatedTenthE7OrbitTransport, mul_assoc]
  have he : ∀ x, e.val
      (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x) =
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ e.val x := by
    apply conjugate_commute generatedTenthE8StandardPermutation g
      (generatedTenthE7XiProjection.map (Int.castRingHom ℝ))
      (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ))
    · intro i j
      exact congrArg (Int.castRingHom ℝ) (generatedTenth_e7_xi_projection_transport i j)
    · exact generatedTenth_e7_signed_flag_projection_commute v
  have ha : leechIntegralAction e generatedTenthE7NormTwelveLine =
      leechIntegralAction p (leechIntegralAction g generatedTenthE7StandardNormTwelveLine) := by
    rw [show e = p * g * p⁻¹ from rfl, map_mul, map_mul]
    rfl
  have hl : leechIntegralAction e generatedTenthE7NormTwelveLine =
        generatedTenthE7NormTwelveLine ∨
      leechIntegralAction e generatedTenthE7NormTwelveLine =
        -generatedTenthE7NormTwelveLine := by
    rw [ha]
    rcases generatedTenth_e7_signed_flag_line_fix v with h | h
    · left
      rw [h]
      exact generatedTenth_e7_standard_norm_line_transport
    · right
      rw [h, map_neg, generatedTenth_e7_standard_norm_line_transport]
  change conwayMatrixAction (generatedTenthE7OrbitConjugation g)
    (griessConwayEncode generatedTenthAxis).1 = _
  apply (generatedTenth_e7_matrix_stabilizer_recognition _).mpr
  rw [ht]
  refine ⟨?_, hl⟩
  intro x
  constructor
  · intro hx
    rw [← he, hx, map_smul]
  · intro hx
    apply e.val.injective
    rw [he, hx, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
