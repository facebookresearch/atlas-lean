/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonal normalization of a real spin intertwiner, without a lift assumption. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinIrreducible

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

noncomputable def spinTranspose (t : SpinSpace →ₗ[ℝ] SpinSpace) :
    SpinSpace →ₗ[ℝ] SpinSpace := Matrix.toLin' (LinearMap.toMatrix' t).transpose

theorem spinTranspose_pairing (t : SpinSpace →ₗ[ℝ] SpinSpace) (x y : SpinSpace) :
    spinPairing (spinTranspose t x) y = spinPairing x (t y) := by
  change ((LinearMap.toMatrix' t).transpose.mulVec x) ⬝ᵥ y = x ⬝ᵥ (t y)
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, LinearMap.toMatrix'_mulVec]

theorem spinPairing_ext {x y : SpinSpace}
    (h : ∀ z, spinPairing x z = spinPairing y z) : x = y := by
  funext i
  simpa [spinPairing, Pi.single_apply, mul_ite] using h (Pi.single i 1)

theorem spinPairing_swap (x y : SpinSpace) : spinPairing x y = spinPairing y x := by
  exact dotProduct_comm x y

theorem spinPairing_smul_left (c : ℝ) (x y : SpinSpace) :
    spinPairing (c • x) y = c * spinPairing x y := by
  simp only [spinPairing, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem spinPairing_smul_right (c : ℝ) (x y : SpinSpace) :
    spinPairing x (c • y) = c * spinPairing x y := by
  rw [spinPairing_swap, spinPairing_smul_left, spinPairing_swap y x]

theorem spinPairing_self_pos (x : SpinSpace) (hx : x ≠ 0) : 0 < spinPairing x x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hp : 0 < x i * x i := mul_self_pos.mpr hi
  have hl : x i * x i ≤ spinPairing x x :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hp hl

theorem spinRepresentation_pairing_move (q : Q) (x y : SpinSpace) :
    spinPairing (spinRepresentation q x) y =
      spinPairing x (spinRepresentation q⁻¹ y) := by
  have h := spinRepresentation_pairing q x (spinRepresentation q⁻¹ y)
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

theorem spinIntertwiner_gram_commutes (a : MulAut Q) (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (he : ∀ q x, e (spinRepresentation q x) = spinRepresentation (a q) (e x)) :
    ∀ q x, ((spinTranspose e.toLinearMap).comp e.toLinearMap) (spinRepresentation q x) =
      spinRepresentation q (((spinTranspose e.toLinearMap).comp e.toLinearMap) x) := by
  intro q x
  apply spinPairing_ext
  intro y
  change spinPairing (spinTranspose e.toLinearMap (e (spinRepresentation q x))) y =
    spinPairing (spinRepresentation q (spinTranspose e.toLinearMap (e x))) y
  calc
    spinPairing (spinTranspose e.toLinearMap (e (spinRepresentation q x))) y =
        spinPairing (e (spinRepresentation q x)) (e y) := spinTranspose_pairing _ _ _
    _ = spinPairing (spinRepresentation (a q) (e x)) (e y) := by rw [he]
    _ = spinPairing (e x) (spinRepresentation (a q)⁻¹ (e y)) :=
      spinRepresentation_pairing_move _ _ _
    _ = spinPairing (e x) (e (spinRepresentation q⁻¹ y)) := by rw [← map_inv, ← he]
    _ = spinPairing (spinTranspose e.toLinearMap (e x)) (spinRepresentation q⁻¹ y) :=
      (spinTranspose_pairing _ _ _).symm
    _ = spinPairing (spinRepresentation q (spinTranspose e.toLinearMap (e x))) y :=
      (spinRepresentation_pairing_move _ _ _).symm

/-- Any invertible real intertwiner can be normalized to an orthogonal one.
Its Gram operator commutes with Q and therefore is a positive scalar. -/
theorem exists_orthogonal_spin_intertwiner (a : MulAut Q)
    (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (he : ∀ q x, e (spinRepresentation q x) = spinRepresentation (a q) (e x)) :
    ∃ s : SpinSpace ≃ₗ[ℝ] SpinSpace,
      (∀ x y, spinPairing (s x) (s y) = spinPairing x y) ∧
      (∀ q x, s (spinRepresentation q x) = spinRepresentation (a q) (s x)) := by
  obtain ⟨c, hc⟩ := spinRepresentation_commutant_linear_scalar
    ((spinTranspose e.toLinearMap).comp e.toLinearMap) (spinIntertwiner_gram_commutes a e he)
  have hp (x y : SpinSpace) : spinPairing (e x) (e y) = c * spinPairing x y := by
    calc
      spinPairing (e x) (e y) = spinPairing
          (((spinTranspose e.toLinearMap).comp e.toLinearMap) x) y :=
        (spinTranspose_pairing _ _ _).symm
      _ = spinPairing (c • x) y := congrArg (fun z => spinPairing z y) (hc x)
      _ = c * spinPairing x y := spinPairing_smul_left _ _ _
  let v : SpinSpace := Pi.single (0 : SpinIndex) 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : SpinIndex)
    simp [v] at h0
  have hev : e v ≠ 0 := by
    intro h
    exact hv (e.injective (h.trans e.map_zero.symm))
  have hvp : spinPairing v v = 1 := by simp [v, spinPairing, Pi.single_apply]
  have hcpos : 0 < c := by
    have h := spinPairing_self_pos (e v) hev
    rwa [hp, hvp, mul_one] at h
  have hroot : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcpos)
  let r : ℝ := 1 / Real.sqrt c
  have hr : r ≠ 0 := div_ne_zero one_ne_zero hroot
  have hscale : r * r * c = 1 := by
    dsimp [r]
    have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hcpos.le
    field_simp
    simpa only [pow_two] using hs.symm
  let s := e.trans (LinearEquiv.smulOfNeZero ℝ SpinSpace r hr)
  refine ⟨s, ?_, ?_⟩
  · intro x y
    change spinPairing (r • e x) (r • e y) = _
    rw [spinPairing_smul_left, spinPairing_smul_right, hp]
    calc r * (r * (c * spinPairing x y)) = (r * r * c) * spinPairing x y := by ring
      _ = spinPairing x y := by rw [hscale, one_mul]
  · intro q x
    change r • e (spinRepresentation q x) = spinRepresentation (a q) (r • e x)
    rw [he, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
