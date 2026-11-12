/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# 3D-Var quadratic minimization

For positive-definite `B, R` and a deterministic real matrix `H`, the
3D-Var cost
`J(x) = 0.5 * (x - xb)ᵀ B⁻¹ (x - xb) + 0.5 * (H x - y)ᵀ R⁻¹ (H x - y)`
has the unique minimizer
`xa = xb + B Hᵀ (H B Hᵀ + R)⁻¹ (y - H xb)`.

The proof is pure finite-dimensional linear algebra: the Woodbury
identity, the normal equations for `xa`, and a completing-the-square
identity. No probability assumptions are made for the minimization
theorem; identifying this minimizer with a Gaussian posterior belongs
to a consumer that imports both this file and the Kalman development.
No nonlinear 4D-Var or algorithm-convergence claim is made.

## Key results

- `g07_woodbury`: `(B⁻¹ + Hᵀ R⁻¹ H)⁻¹ = B - B Hᵀ (H B Hᵀ + R)⁻¹ H B`.
- `g07_normal_equation`: `xa` satisfies the normal equations.
- `g07_minimizer_isMin_unique`: `xa` is the unique global minimizer of `J`.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.G07ThreeDVar

/-- 3D-Var cost `J(x) = 0.5 * (x - xb)ᵀ B⁻¹ (x - xb) + 0.5 * (H x - y)ᵀ R⁻¹ (H x - y)`. -/
noncomputable def g07Cost {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (xb : Fin n → ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  0.5 * ((x - xb) ⬝ᵥ B⁻¹ *ᵥ (x - xb) + (H *ᵥ x - y) ⬝ᵥ R⁻¹ *ᵥ (H *ᵥ x - y))

/-- Kalman-form 3D-Var minimizer `xa = xb + B Hᵀ (H B Hᵀ + R)⁻¹ (y - H xb)`. -/
noncomputable def g07Minimizer {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (xb : Fin n → ℝ) (y : Fin m → ℝ) : Fin n → ℝ :=
  xb + B *ᵥ (Hᵀ *ᵥ ((H * B * Hᵀ + R)⁻¹ *ᵥ (y - H *ᵥ xb)))

theorem g07_S_posDef {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (hB : B.PosDef) (hR : R.PosDef) : (H * B * Hᵀ + R).PosDef := by
  have hHH : Hᵀ = Hᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial H).symm
  rw [hHH]
  exact Matrix.PosDef.posSemidef_add (hB.posSemidef.mul_mul_conjTranspose_same H) hR

theorem g07_P_posDef {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (hB : B.PosDef) (hR : R.PosDef) : (B⁻¹ + Hᵀ * R⁻¹ * H).PosDef := by
  have hHH : Hᵀ = Hᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial H).symm
  rw [hHH]
  exact Matrix.PosDef.add_posSemidef hB.inv (hR.inv.posSemidef.conjTranspose_mul_mul_same H)

/-- Woodbury identity: `(B⁻¹ + Hᵀ R⁻¹ H)⁻¹ = B - B Hᵀ (H B Hᵀ + R)⁻¹ H B`
for positive-definite `B, R`. -/
theorem g07_woodbury {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (hB : B.PosDef) (hR : R.PosDef) :
    (B⁻¹ + Hᵀ * R⁻¹ * H)⁻¹ = B - B * Hᵀ * (H * B * Hᵀ + R)⁻¹ * H * B := by
  set S : Matrix (Fin m) (Fin m) ℝ := H * B * Hᵀ + R with hSdef
  have hSpos : S.PosDef := g07_S_posDef B R H hB hR
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSpos.isUnit
  have hB1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBdet
  have hR1 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hHBH : H * B * Hᵀ = S - R := by
    rw [hSdef]
    abel
  have key : R⁻¹ * (H * B * Hᵀ) * S⁻¹ = R⁻¹ - S⁻¹ := by
    rw [hHBH, mul_sub, hR1, sub_mul, mul_assoc, hSS, mul_one, one_mul]
  have e1 : B⁻¹ * (B * Hᵀ * S⁻¹ * H * B) = Hᵀ * S⁻¹ * H * B := by
    simp only [← Matrix.mul_assoc, hB1, Matrix.one_mul]
  have e3 : (Hᵀ * R⁻¹ * H) * (B * Hᵀ * S⁻¹ * H * B)
      = Hᵀ * R⁻¹ * H * B - Hᵀ * S⁻¹ * H * B := by
    have rassoc : (Hᵀ * R⁻¹ * H) * (B * Hᵀ * S⁻¹ * H * B)
        = Hᵀ * (R⁻¹ * (H * B * Hᵀ) * S⁻¹) * H * B := by
      simp only [Matrix.mul_assoc]
    rw [rassoc, key, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, hB1, e1, e3]
  abel

/-- The Kalman-form minimizer satisfies the normal equations. -/
theorem g07_normal_equation {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (xb : Fin n → ℝ) (y : Fin m → ℝ) (hB : B.PosDef) (hR : R.PosDef) :
    (B⁻¹ + Hᵀ * R⁻¹ * H) *ᵥ (g07Minimizer B R H xb y - xb) =
      Hᵀ *ᵥ (R⁻¹ *ᵥ (y - H *ᵥ xb)) := by
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hSpos : (H * B * Hᵀ + R).PosDef := g07_S_posDef B R H hB hR
  have hSdet : IsUnit (H * B * Hᵀ + R).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSpos.isUnit
  have hB1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBdet
  have hR1 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hSS : (H * B * Hᵀ + R) * (H * B * Hᵀ + R)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hSdet
  unfold g07Minimizer
  set S : Matrix (Fin m) (Fin m) ℝ := H * B * Hᵀ + R with hSdef
  set w : Fin m → ℝ := y - H *ᵥ xb with hwdef
  have hmin : (xb + B *ᵥ (Hᵀ *ᵥ (S⁻¹ *ᵥ w))) - xb
      = B *ᵥ (Hᵀ *ᵥ (S⁻¹ *ᵥ w)) := by abel
  rw [hmin]
  have eB : ∀ v : Fin n → ℝ, B⁻¹ *ᵥ (B *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hB1, Matrix.one_mulVec]
  have eS : ∀ u : Fin m → ℝ, S *ᵥ (S⁻¹ *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
  have eR : ∀ u : Fin m → ℝ, R⁻¹ *ᵥ (R *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, hR1, Matrix.one_mulVec]
  have key : ∀ v : Fin n → ℝ, (B⁻¹ + Hᵀ * R⁻¹ * H) *ᵥ (B *ᵥ v)
      = v + Hᵀ *ᵥ (R⁻¹ *ᵥ (H *ᵥ (B *ᵥ v))) := by
    intro v
    have rassoc : (Hᵀ * R⁻¹ * H) *ᵥ (B *ᵥ v)
        = Hᵀ *ᵥ (R⁻¹ *ᵥ (H *ᵥ (B *ᵥ v))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [Matrix.add_mulVec, eB v, rassoc]
  have hHBH : H * B * Hᵀ = S - R := by
    rw [hSdef]
    abel
  have eH : H *ᵥ (B *ᵥ (Hᵀ *ᵥ (S⁻¹ *ᵥ w))) = w - R *ᵥ (S⁻¹ *ᵥ w) := by
    have rassoc : H *ᵥ (B *ᵥ (Hᵀ *ᵥ (S⁻¹ *ᵥ w)))
        = (H * B * Hᵀ) *ᵥ (S⁻¹ *ᵥ w) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [rassoc, hHBH, Matrix.sub_mulVec, eS]
  have eRw : R⁻¹ *ᵥ (w - R *ᵥ (S⁻¹ *ᵥ w)) = R⁻¹ *ᵥ w - S⁻¹ *ᵥ w := by
    rw [Matrix.mulVec_sub, eR]
  have hkey := key (Hᵀ *ᵥ (S⁻¹ *ᵥ w))
  have hdist := Matrix.mulVec_sub Hᵀ (R⁻¹ *ᵥ w) (S⁻¹ *ᵥ w)
  rw [hkey, eH, eRw, hdist]
  abel

/-- The Kalman-form point is the unique global minimizer of `J`. -/
theorem g07_minimizer_isMin_unique {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (xb : Fin n → ℝ) (y : Fin m → ℝ) (hB : B.PosDef) (hR : R.PosDef)
    (x : Fin n → ℝ) :
    g07Cost B R H xb y (g07Minimizer B R H xb y) ≤ g07Cost B R H xb y x ∧
      (g07Cost B R H xb y x = g07Cost B R H xb y (g07Minimizer B R H xb y) →
        x = g07Minimizer B R H xb y) := by
  have hnorm := g07_normal_equation B R H xb y hB hR
  have hPpos : (B⁻¹ + Hᵀ * R⁻¹ * H).PosDef := g07_P_posDef B R H hB hR
  have hBsymm : B⁻¹ᵀ = B⁻¹ := by
    have h : (B⁻¹)ᴴ = B⁻¹ := hB.inv.isHermitian
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hRsymm : R⁻¹ᵀ = R⁻¹ := by
    have h : (R⁻¹)ᴴ = R⁻¹ := hR.inv.isHermitian
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set xa : Fin n → ℝ := g07Minimizer B R H xb y with hxadef
  set d : Fin n → ℝ := x - xa with hddef
  set e : Fin n → ℝ := xa - xb with hedef
  set f : Fin m → ℝ := H *ᵥ xa - y with hfdef
  have symm_dot : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (h : Mᵀ = M)
      (u v : Fin k → ℝ), u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
    intro k M h u v
    rw [Matrix.dotProduct_mulVec]
    have h2 : u ᵥ* M = Mᵀ *ᵥ u := by
      have h3 := Matrix.vecMul_transpose (Mᵀ) u
      rwa [Matrix.transpose_transpose] at h3
    rw [h2, h, dotProduct_comm]
  have expand : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (h : Mᵀ = M)
      (a b : Fin k → ℝ),
      (a + b) ⬝ᵥ M *ᵥ (a + b)
        = a ⬝ᵥ M *ᵥ a + 2 * (a ⬝ᵥ M *ᵥ b) + b ⬝ᵥ M *ᵥ b := by
    intro k M h a b
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      symm_dot M h b a]
    ring
  have cross_move : ∀ (d' : Fin n → ℝ) (q : Fin m → ℝ),
      (H *ᵥ d') ⬝ᵥ q = d' ⬝ᵥ (Hᵀ *ᵥ q) := by
    intro d' q
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    have h2 : q ᵥ* H = Hᵀ *ᵥ q := by
      have h3 := Matrix.vecMul_transpose (Hᵀ) q
      rwa [Matrix.transpose_transpose] at h3
    rw [h2, dotProduct_comm]
  have hde : x - xb = d + e := by rw [hddef, hedef]; abel
  have hHd : H *ᵥ d = H *ᵥ x - H *ᵥ xa := by rw [hddef, Matrix.mulVec_sub]
  have hHf : H *ᵥ x - y = H *ᵥ d + f := by rw [hHd, hfdef]; abel
  have hfe : f = H *ᵥ e - (y - H *ᵥ xb) := by
    rw [hfdef, hedef, Matrix.mulVec_sub]; abel
  have hnorm2 : B⁻¹ *ᵥ e + (Hᵀ * R⁻¹ * H) *ᵥ e
      = Hᵀ *ᵥ (R⁻¹ *ᵥ (y - H *ᵥ xb)) := by
    rw [Matrix.add_mulVec] at hnorm
    exact hnorm
  have hrassoc : ∀ v : Fin n → ℝ, (Hᵀ * R⁻¹ * H) *ᵥ v
      = Hᵀ *ᵥ (R⁻¹ *ᵥ (H *ᵥ v)) := by
    intro v
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h0 : B⁻¹ *ᵥ e + Hᵀ *ᵥ (R⁻¹ *ᵥ f) = 0 := by
    have d1 := Matrix.mulVec_sub R⁻¹ (H *ᵥ e) (y - H *ᵥ xb)
    have d2 := Matrix.mulVec_sub Hᵀ (R⁻¹ *ᵥ (H *ᵥ e)) (R⁻¹ *ᵥ (y - H *ᵥ xb))
    rw [hfe, d1, d2, ← hrassoc e]
    have habel : B⁻¹ *ᵥ e + ((Hᵀ * R⁻¹ * H) *ᵥ e - Hᵀ *ᵥ (R⁻¹ *ᵥ (y - H *ᵥ xb)))
        = (B⁻¹ *ᵥ e + (Hᵀ * R⁻¹ * H) *ᵥ e) - Hᵀ *ᵥ (R⁻¹ *ᵥ (y - H *ᵥ xb)) := by
      abel
    rw [habel, hnorm2]
    exact sub_self _
  have hcross : d ⬝ᵥ B⁻¹ *ᵥ e + (H *ᵥ d) ⬝ᵥ R⁻¹ *ᵥ f = 0 := by
    rw [cross_move d (R⁻¹ *ᵥ f), ← dotProduct_add, h0, dotProduct_zero]
  have hmain : d ⬝ᵥ B⁻¹ *ᵥ d + (H *ᵥ d) ⬝ᵥ R⁻¹ *ᵥ (H *ᵥ d)
      = d ⬝ᵥ (B⁻¹ + Hᵀ * R⁻¹ * H) *ᵥ d := by
    rw [cross_move d (R⁻¹ *ᵥ (H *ᵥ d)), Matrix.add_mulVec, ← dotProduct_add,
      hrassoc d]
  have hexpandB : (x - xb) ⬝ᵥ B⁻¹ *ᵥ (x - xb)
      = d ⬝ᵥ B⁻¹ *ᵥ d + 2 * (d ⬝ᵥ B⁻¹ *ᵥ e) + e ⬝ᵥ B⁻¹ *ᵥ e := by
    rw [hde]; exact expand B⁻¹ hBsymm d e
  have hexpandR : (H *ᵥ x - y) ⬝ᵥ R⁻¹ *ᵥ (H *ᵥ x - y)
      = (H *ᵥ d) ⬝ᵥ R⁻¹ *ᵥ (H *ᵥ d) + 2 * ((H *ᵥ d) ⬝ᵥ R⁻¹ *ᵥ f)
        + f ⬝ᵥ R⁻¹ *ᵥ f := by
    rw [hHf]; exact expand R⁻¹ hRsymm (H *ᵥ d) f
  have csq : g07Cost B R H xb y x - g07Cost B R H xb y xa
      = 0.5 * (d ⬝ᵥ (B⁻¹ + Hᵀ * R⁻¹ * H) *ᵥ d) := by
    unfold g07Cost
    rw [← hedef, ← hfdef]
    linarith [hexpandB, hexpandR, hcross, hmain]
  have hstar : star d = d := star_trivial d
  have hnn : 0 ≤ d ⬝ᵥ (B⁻¹ + Hᵀ * R⁻¹ * H) *ᵥ d := by
    have h := hPpos.posSemidef.dotProduct_mulVec_nonneg d
    rwa [hstar] at h
  constructor
  · linarith [csq, hnn]
  · intro heq
    have hQ0 : d ⬝ᵥ (B⁻¹ + Hᵀ * R⁻¹ * H) *ᵥ d = 0 := by
      linarith [csq, hnn, heq]
    have hdx0 : d = 0 := by
      by_contra hne
      have hpos := hPpos.dotProduct_mulVec_pos hne
      rw [hstar] at hpos
      linarith [hpos, hQ0]
    have hxa : x - xa = 0 := by rw [← hddef]; exact hdx0
    exact sub_eq_zero.mp hxa

end MathlibExt.LinearAlgebra.G07ThreeDVar
