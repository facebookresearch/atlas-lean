/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.ReciprocalLattice
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Tests for `PhyslibExt.CondensedMatter.Crystallography.ReciprocalLattice`

* Simple cubic, `a = 1`: the cell volume is `1`, each reciprocal vector is `2π • eᵢ`,
  duality holds via `recip_duality`, and the reciprocal cell volume is `(2π)³` via
  `recip_volume`.
* FCC/BCC numeric instance, `a = 2`: the three `fcc_bcc` equalities reduce to the
  explicit vectors stated, the FCC primitive cell volume is `a³/4 = 2`, and the
  reciprocal volume is `(2π)³/2`.
* G_hkl instance: cubic `a = 1`, `(h, k, l) = (1, 1, 1)`: `G = 2π • ![1, 1, 1]`,
  `‖G‖ = 2π√3`, spacing `1/√3` via `spacing_mul_norm`, and `G ⬝ᵥ R = 2π(n₁+n₂+n₃)`.
* Fourier: the plane-wave coefficient is `1` for `G = G₀ = b₁` and `0` for
  `G₀ = b₁`, `G = b₂` on the `2 × 2 × 2` grid.
* Boundary: coplanar `a₁ a₂ (a₁ + a₂)` have `V = 0`; no reciprocal claim is made there.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Crystallography.ReciprocalLattice

open _root_.Crystallography
open scoped Matrix

/-! ### Simple cubic, `a = 1` -/

/-- The simple cubic cell volume is `1`. -/
lemma cubic_volume : cellVolume ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] = 1 := by
  simp [cellVolume, cross_apply]

/-- The simple cubic cell volume is nonzero. -/
lemma cubic_volume_ne : cellVolume ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] ≠ 0 := by
  rw [cubic_volume]
  norm_num

/-- Cubic reciprocal vector `b₁ = 2π • e₀`. -/
lemma cubic_b1 : b₁ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
    = 2 * Real.pi • ![1, 0, 0] := by
  simp only [b₁]
  rw [cubic_volume]
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

/-- Cubic reciprocal vector `b₂ = 2π • e₁`. -/
lemma cubic_b2 : b₂ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
    = 2 * Real.pi • ![0, 1, 0] := by
  simp only [b₂]
  rw [cubic_volume]
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

/-- Cubic reciprocal vector `b₃ = 2π • e₂`. -/
lemma cubic_b3 : b₃ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
    = 2 * Real.pi • ![0, 0, 1] := by
  simp only [b₃]
  rw [cubic_volume]
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

/-- Duality check via lemma 1, indexed form. -/
example (i j : Fin 3) :
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] i ⬝ᵥ
      ![b₁ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1],
        b₂ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1],
        b₃ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]] j
      = 2 * Real.pi * (if i = j then (1 : ℝ) else 0) :=
  recip_duality _ _ _ cubic_volume_ne i j

/-- Duality check via lemma 1, diagonal case. -/
example : ![1, 0, 0] ⬝ᵥ b₁ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] = 2 * Real.pi := by
  have h := recip_duality _ _ _ cubic_volume_ne 0 0
  simpa using h

/-- Duality check via lemma 1, off-diagonal case. -/
example : ![1, 0, 0] ⬝ᵥ b₂ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] = 0 := by
  have h := recip_duality _ _ _ cubic_volume_ne 0 1
  simpa using h

/-- Cubic reciprocal cell volume `(2π)³` via lemma 2. -/
example : cellVolume (b₁ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1])
    (b₂ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1])
    (b₃ ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]) = (2 * Real.pi)^3 := by
  rw [recip_volume _ _ _ cubic_volume_ne, cubic_volume, div_one]

/-! ### FCC/BCC numeric instance, `a = 2` -/

/-- First `fcc_bcc` equality at `a = 2` reduces to `π • ![-1, 1, 1]`. -/
example : b₁ (((2 : ℝ) / 2) • ![0, 1, 1]) (((2 : ℝ) / 2) • ![1, 0, 1])
    (((2 : ℝ) / 2) • ![1, 1, 0]) = Real.pi • ![-1, 1, 1] := by
  have h := (fcc_bcc (2 : ℝ) (by norm_num)).1
  rw [h]
  congr 1
  ring

/-- Second `fcc_bcc` equality at `a = 2` reduces to `π • ![1, -1, 1]`. -/
example : b₂ (((2 : ℝ) / 2) • ![0, 1, 1]) (((2 : ℝ) / 2) • ![1, 0, 1])
    (((2 : ℝ) / 2) • ![1, 1, 0]) = Real.pi • ![1, -1, 1] := by
  have h := (fcc_bcc (2 : ℝ) (by norm_num)).2.1
  rw [h]
  congr 1
  ring

/-- Third `fcc_bcc` equality at `a = 2` reduces to `π • ![1, 1, -1]`. -/
example : b₃ (((2 : ℝ) / 2) • ![0, 1, 1]) (((2 : ℝ) / 2) • ![1, 0, 1])
    (((2 : ℝ) / 2) • ![1, 1, 0]) = Real.pi • ![1, 1, -1] := by
  have h := (fcc_bcc (2 : ℝ) (by norm_num)).2.2
  rw [h]
  congr 1
  ring

/-- The FCC primitive cell volume at `a = 2` is `a³/4 = 2`. -/
lemma fcc_volume : cellVolume (((2 : ℝ) / 2) • ![0, 1, 1])
    (((2 : ℝ) / 2) • ![1, 0, 1]) (((2 : ℝ) / 2) • ![1, 1, 0]) = 2 := by
  simp [cellVolume, cross_apply]
  norm_num

/-- The FCC primitive cell volume at `a = 2` is nonzero. -/
lemma fcc_volume_ne : cellVolume (((2 : ℝ) / 2) • ![0, 1, 1])
    (((2 : ℝ) / 2) • ![1, 0, 1]) (((2 : ℝ) / 2) • ![1, 1, 0]) ≠ 0 := by
  rw [fcc_volume]
  norm_num

/-- The reciprocal volume at `a = 2` is `(2π)³/2` via lemma 2. -/
example : cellVolume
    (b₁ (((2 : ℝ) / 2) • ![0, 1, 1]) (((2 : ℝ) / 2) • ![1, 0, 1])
      (((2 : ℝ) / 2) • ![1, 1, 0]))
    (b₂ (((2 : ℝ) / 2) • ![0, 1, 1]) (((2 : ℝ) / 2) • ![1, 0, 1])
      (((2 : ℝ) / 2) • ![1, 1, 0]))
    (b₃ (((2 : ℝ) / 2) • ![0, 1, 1]) (((2 : ℝ) / 2) • ![1, 0, 1])
      (((2 : ℝ) / 2) • ![1, 1, 0])) = (2 * Real.pi)^3 / 2 := by
  rw [recip_volume _ _ _ fcc_volume_ne, fcc_volume]

/-! ### G_hkl instance: cubic `a = 1`, `(h, k, l) = (1, 1, 1)` -/

/-- `G_111 = 2π • ![1, 1, 1]` in the cubic cell. -/
lemma cubic_G111 : recipVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 1 1 1
    = (2 * Real.pi) • ![1, 1, 1] := by
  simp only [recipVec, cubic_b1, cubic_b2, cubic_b3]
  ext i
  fin_cases i <;> simp <;> ring

/-- `‖G_111‖ = 2π√3`. -/
lemma cubic_G111_norm : euclidNorm ((2 * Real.pi) • ![1, 1, 1])
    = 2 * Real.pi * Real.sqrt 3 := by
  have hv : ![1, 1, 1] ⬝ᵥ ![1, 1, 1] = (3 : ℝ) := by
    simp [Matrix.vec3_dotProduct]
    norm_num
  have hdot : ((2 * Real.pi) • ![1, 1, 1]) ⬝ᵥ ((2 * Real.pi) • ![1, 1, 1])
      = (2 * Real.pi * Real.sqrt 3)^2 := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hv, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  simp only [euclidNorm, hdot, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sqrt_nonneg 3))

/-- Interplanar spacing `d_111 = 1/√3` via lemma 5. -/
example : interplanarSpacing ((2 * Real.pi) • ![1, 1, 1])
    = 1 / Real.sqrt 3 := by
  have hpi2 : (2 : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  have hsq3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hprod : (2 : ℝ) * Real.pi * Real.sqrt 3 ≠ 0 := mul_ne_zero hpi2 hsq3
  simp only [interplanarSpacing, cubic_G111_norm]
  field_simp

/-- `G_111 ⬝ᵥ R = 2π(n₁ + n₂ + n₃)` via lemma 4. -/
example (n₁ n₂ n₃ : ℤ) :
    recipVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 1 1 1 ⬝ᵥ
        latticeVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] n₁ n₂ n₃
      = 2 * Real.pi * (((n₁ + n₂ + n₃ : ℤ)) : ℝ) := by
  have h := recipVec_dot_lattice ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
    cubic_volume_ne 1 1 1 n₁ n₂ n₃
  simp only [one_mul] at h
  exact h

/-! ### Fourier plane-wave checks on the `2 × 2 × 2` grid -/

/-- Plane-wave coefficient: `G = G₀ = b₁` gives `1`. -/
example : fourierCoeffDiscrete ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 2
    (planeWave (recipVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 1 0 0))
    (recipVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 1 0 0) = 1 := by
  have hprod := fourierCoeffDiscrete_planeWave ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
    cubic_volume_ne 2 (by decide) 1 0 0 1 0 0
  rw [hprod]
  have a1 : (2 * ↑Real.pi * Complex.I * (↑((1 : ℤ) - (1 : ℤ)) : ℂ) / ↑(2 : ℕ))
      = (0 : ℂ) := by
    simp only [Int.cast_sub, Int.cast_one]
    ring
  have c1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑((1 : ℤ) - (1 : ℤ)) / ↑(2 : ℕ))
      = 1 := by
    rw [a1]
    exact Complex.exp_zero
  have a2 : (2 * ↑Real.pi * Complex.I * (↑((0 : ℤ) - (0 : ℤ)) : ℂ) / ↑(2 : ℕ))
      = (0 : ℂ) := by
    simp only [Int.cast_sub, Int.cast_zero]
    ring
  have c2 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑((0 : ℤ) - (0 : ℤ)) / ↑(2 : ℕ))
      = 1 := by
    rw [a2]
    exact Complex.exp_zero
  exact if_pos ⟨c1, c2, c2⟩

/-- Plane-wave coefficient: `G₀ = b₁`, `G = b₂` gives `0`. -/
example : fourierCoeffDiscrete ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 2
    (planeWave (recipVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 1 0 0))
    (recipVec ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] 0 1 0) = 0 := by
  have hprod := fourierCoeffDiscrete_planeWave ![1, 0, 0] ![0, 1, 0] ![0, 0, 1]
    cubic_volume_ne 2 (by decide) 0 1 0 1 0 0
  rw [hprod]
  have earg : (2 * ↑Real.pi * Complex.I * (↑((1 : ℤ) - (0 : ℤ)) : ℂ) / ↑(2 : ℕ))
      = 2 * ↑Real.pi * Complex.I * (↑(1 : ℕ) : ℂ) / ↑(2 : ℕ) := by
    simp only [Int.cast_sub, Int.cast_one, Int.cast_zero, Nat.cast_one]
    ring
  have hne1 : Complex.exp
      (2 * ↑Real.pi * Complex.I * ↑((1 : ℤ) - (0 : ℤ)) / ↑(2 : ℕ)) ≠ 1 := by
    rw [earg]
    intro hcon1
    rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (show (2 : ℕ) ≠ 0 by decide)]
      at hcon1
    exact absurd hcon1 (by decide)
  have hneg : ¬ (Complex.exp (2 * ↑Real.pi * Complex.I * ↑((1 : ℤ) - (0 : ℤ))
      / ↑(2 : ℕ)) = 1
    ∧ Complex.exp (2 * ↑Real.pi * Complex.I * ↑((0 : ℤ) - (1 : ℤ)) / ↑(2 : ℕ)) = 1
    ∧ Complex.exp (2 * ↑Real.pi * Complex.I * ↑((0 : ℤ) - (0 : ℤ)) / ↑(2 : ℕ))
      = 1) :=
    fun hcon => hne1 hcon.1
  exact if_neg hneg

/-! ### Boundary: coplanar vectors have `V = 0` -/

/-- Coplanar `a₁ a₂ (a₁ + a₂)` have `V = 0`; the reciprocal construction needs
`V ≠ 0`, so no reciprocal claim is made here. -/
example (a₁ a₂ : Fin 3 → ℝ) : cellVolume a₁ a₂ (a₁ + a₂) = 0 := by
  show a₁ ⬝ᵥ (a₂ ⨯₃ (a₁ + a₂)) = 0
  rw [cross_apply, Matrix.vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  simp only [Pi.add_apply]
  ring

end PhyslibExtTest.CondensedMatter.Crystallography.ReciprocalLattice
