/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8Preservation

/-! Preservation of the actual E7 eigenspace forces preservation of its orthogonal projector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

private def e7Projector : Module.End ℝ (Fin 24 → ℝ) :=
  (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ)).mulVecLin

private theorem projector_integer_square :
    generatedTenthE7ProjectionInteger * generatedTenthE7ProjectionInteger =
      (2 : ℤ) • generatedTenthE7ProjectionInteger := by decide +kernel

private theorem projector_square (x : Fin 24 → ℝ) :
    e7Projector (e7Projector x) = (2 : ℝ) • e7Projector x := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix projector_integer_square
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at h
  have hm : ((2 : ℤ) • generatedTenthE7ProjectionInteger).map (Int.castRingHom ℝ) =
      (2 : ℝ) • generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
  rw [hm] at h
  change generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ
      (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x) =
    (2 : ℝ) • (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x)
  rw [Matrix.mulVec_mulVec, h, Matrix.smul_mulVec]

private theorem projector_symmetric (x y : Fin 24 → ℝ) :
    stdPairingFun (e7Projector x) y = stdPairingFun x (e7Projector y) := by
  have ht : generatedTenthE7ProjectionInteger.transpose =
      generatedTenthE7ProjectionInteger := by
    ext i j
    simp only [Matrix.transpose_apply, generatedTenthE7ProjectionInteger]
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [hij, Ne.symm hij, false_and, ite_false]
      ring
  have htr : (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ)).transpose =
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) := by
    rw [← Matrix.transpose_map, ht]
  change (_ *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (_ *ᵥ y)
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, htr]

private theorem pairing_smul_right (a : ℝ) (x y : Fin 24 → ℝ) :
    stdPairingFun x (a • y) = a * stdPairingFun x y := by
  simp only [stdPairingFun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem pairing_zero_self (x : Fin 24 → ℝ)
    (hx : stdPairingFun x x = 0) : x = 0 := by
  ext i
  have h := Finset.single_le_sum (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)
  change x i * x i ≤ stdPairingFun x x at h
  rw [hx] at h
  change x i = 0
  nlinarith

/-- Every actual Leech isometry preserving the E7 eigenspace commutes with its full projector. -/
theorem generatedTenth_e7_projection_commute_of_eigenspace (e : leechIsomSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x = (2 : ℝ) • x ↔
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ e.val x =
          (2 : ℝ) • e.val x)
    (x : Fin 24 → ℝ) :
    e.val (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x) =
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ e.val x := by
  have he' : ∀ y, e7Projector y = (2 : ℝ) • y ↔
      e7Projector (e.val y) = (2 : ℝ) • e.val y := he
  let f := e.val (e7Projector x) - e7Projector (e.val x)
  have hpf : e7Projector f = (2 : ℝ) • f := by
    simp only [f, map_sub, (he' (e7Projector x)).mp (projector_square x),
      projector_square, smul_sub]
  have hpre : e7Projector (e.val.symm f) = (2 : ℝ) • e.val.symm f := by
    apply (he' (e.val.symm f)).mpr
    rw [e.val.apply_symm_apply]
    exact hpf
  have h1 : stdPairingFun (e.val (e7Projector x)) f =
      2 * stdPairingFun (e.val x) f := by
    have h := projector_symmetric x (e.val.symm f)
    rw [hpre, pairing_smul_right] at h
    have hleft := e.property.1 (e7Projector x) (e.val.symm f)
    have hright := e.property.1 x (e.val.symm f)
    rw [e.val.apply_symm_apply] at hleft hright
    rw [hleft, hright]
    exact h
  have h2 : stdPairingFun (e7Projector (e.val x)) f =
      2 * stdPairingFun (e.val x) f := by
    rw [projector_symmetric, hpf, pairing_smul_right]
  have hzero : stdPairingFun f f = 0 := by
    change (e.val (e7Projector x) - e7Projector (e.val x)) ⬝ᵥ f = 0
    rw [sub_dotProduct]
    exact sub_eq_zero.mpr (h1.trans h2.symm)
  exact sub_eq_zero.mp (pairing_zero_self f hzero)

/-- Every actual E7-preserving Leech isometry preserves the enclosing actual
E8 coordinate section. -/
theorem generatedTenth_e8_preserved_of_e7_eigenspace (e : leechIsomSubgroup)
    (he : ∀ x : Fin 24 → ℝ,
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x = (2 : ℝ) • x ↔
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ e.val x =
          (2 : ℝ) • e.val x)
    (x : Fin 24 → ℝ) :
    x ∈ generatedTenthE8CoordinateSection ↔ e.val x ∈ generatedTenthE8CoordinateSection :=
  generatedTenth_e8_preserved_of_e7_projection e
    (generatedTenth_e7_projection_commute_of_eigenspace e he) x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
