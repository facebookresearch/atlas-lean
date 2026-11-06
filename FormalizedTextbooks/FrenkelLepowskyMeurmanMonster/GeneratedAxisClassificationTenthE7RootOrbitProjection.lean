/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitGroup

/-! Every genuine original matrix fixer preserves the entire standard E7 root space. -/

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

/-- The full actual matrix group commutes with the entire standard root-space projector. -/
theorem generatedTenth_e7_root_orbit_standard_commute
    (g : generatedTenthE7StandardMatrixGroup) (x : Fin 24 → ℝ) :
    g.val.val (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
      generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ g.val.val x := by
  let p := golayPermutationIsometry generatedTenthE8StandardPermutation
  let e := generatedTenthE7TransportedSpatial (generatedTenthE7OrbitConjugation g.val)
  have ht : e = p * g.val * p⁻¹ := by
    simp [e, p, generatedTenthE7TransportedSpatial, generatedTenthE7OrbitConjugation,
      generatedTenthE7OrbitTransport, mul_assoc]
  have he : ∀ y, e.val
      (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ y) =
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ e.val y :=
    generatedTenth_e7_projection_commute_of_eigenspace e
      (generatedTenth_e7_matrix_fixer_eigenspace _ g.property)
  have hh := conjugate_commute generatedTenthE8StandardPermutation⁻¹ e
    (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ))
    (generatedTenthE7XiProjection.map (Int.castRingHom ℝ))
    (fun i j => by
      have h := generatedTenth_e7_xi_projection_transport
        (generatedTenthE8StandardPermutation.val.symm i)
        (generatedTenthE8StandardPermutation.val.symm j)
      rw [generatedTenthE8StandardPermutation.val.apply_symm_apply,
        generatedTenthE8StandardPermutation.val.apply_symm_apply] at h
      exact congrArg (Int.castRingHom ℝ) h.symm) he x
  have hp : golayPermutationIsometry generatedTenthE8StandardPermutation⁻¹ = p⁻¹ :=
    golayPermutationHom.map_inv _
  rw [hp, ht] at hh
  have hc : p⁻¹ * (p * g.val * p⁻¹) * (p⁻¹)⁻¹ = g.val := by group
  rw [hc] at hh
  exact hh

/-- Complete coordinate action of the standard twice-projector, including all zero rows. -/
theorem generatedTenth_e7_root_orbit_projector_coordinate (x : Fin 24 → ℝ) (i : Fin 24) :
    (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) i =
      (if i.val < 8 then 2 * x i else 0) -
        (if i = 4 ∨ i = 5 then x 4 + x 5 else 0) := by
  fin_cases i <;>
    simp [generatedTenthE7XiProjection, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring

/-- The complete genuine E7 eigenspace is exactly the octad-supported perpendicular space. -/
theorem generatedTenth_e7_root_orbit_eigenspace (x : Fin 24 → ℝ) :
    generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x = (2 : ℝ) • x ↔
      (∀ i : Fin 24, 8 ≤ i.val → x i = 0) ∧ x 4 + x 5 = 0 := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hv := congrFun h i
      rw [generatedTenth_e7_root_orbit_projector_coordinate] at hv
      have h4 : i ≠ 4 := by intro he; subst i; norm_num at hi
      have h5 : i ≠ 5 := by intro he; subst i; norm_num at hi
      simp only [Nat.not_lt.mpr hi, h4, h5, false_or, ite_false, sub_zero,
        Pi.smul_apply, smul_eq_mul] at hv
      linarith
    · have hv := congrFun h 4
      rw [generatedTenth_e7_root_orbit_projector_coordinate] at hv
      norm_num at hv
      linarith
  · rintro ⟨hs, hn⟩
    ext i
    rw [generatedTenth_e7_root_orbit_projector_coordinate]
    simp only [hn, ite_self, sub_zero, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i.val < 8
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi, hs i (Nat.le_of_not_gt hi), mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
