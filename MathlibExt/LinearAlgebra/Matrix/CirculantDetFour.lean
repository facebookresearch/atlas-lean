/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# The four-by-four circulant determinant

Expanding along the first row gives a polynomial identity over any commutative ring.
-/

namespace MetaMathlibExt

@[expose] public section

open Matrix

/-- **The group determinant of $C_4$.** For a commutative ring $R$ and
$x = (x_0, x_1, x_2, x_3) \in R^4$, $D_4(x_0, x_1, x_2, x_3)$ is the determinant of the
$4 \times 4$ circulant matrix whose $(i, j)$ entry is $x_{i - j}$, indices taken mod $4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public def circulantDetFour {R : Type*} [CommRing R] (x : Fin 4 → R) : R :=
  (circulant x).det

/-- **The 4 × 4 circulant determinant of (1, 0, 0, 0).** Over every commutative ring $R$, the
$4 \times 4$ circulant determinant satisfies $D_4(1, 0, 0, 0) = 1$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public theorem circulantDetFour_single_one {R : Type*} [CommRing R] :
    circulantDetFour (Pi.single 0 1 : Fin 4 → R) = 1 := by
  simp [circulantDetFour]

/-- **Factorization of the 4 × 4 circulant determinant.** For every commutative ring $R$ and all
$x_0, x_1, x_2, x_3 \in R$, the $4 \times 4$ circulant determinant $D_4$ satisfies

$$D_4(x_0, x_1, x_2, x_3) =
\bigl((x_0 + x_2)^2 - (x_1 + x_3)^2\bigr)\bigl((x_0 - x_2)^2 + (x_1 - x_3)^2\bigr).$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 1 (`integers-2024-A30-cor-1`). -/
public theorem circulantDetFour_eq {R : Type*} [CommRing R] (x₀ x₁ x₂ x₃ : R) :
    circulantDetFour ![x₀, x₁, x₂, x₃] =
      ((x₀ + x₂) ^ 2 - (x₁ + x₃) ^ 2) * ((x₀ - x₂) ^ 2 + (x₁ - x₃) ^ 2) := by
  rw [circulantDetFour, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, submatrix_apply, Fin.succAbove]
  ring

end

open Matrix

private theorem powI_mod_four (n : ℕ) : Complex.I ^ n = Complex.I ^ (n % 4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

-- Evaluate the character at the indicated residue class.
local notation "c4Root" => (fun a : Fin 4 => Complex.I ^ Fin.val a)

private theorem c4Root_add (a b : Fin 4) : c4Root (a + b) = c4Root a * c4Root b := by
  change Complex.I ^ ((a.val + b.val) % 4) = Complex.I ^ a.val * Complex.I ^ b.val
  rw [← pow_add]
  exact (powI_mod_four _).symm

private theorem c4Root_mul (a b : Fin 4) : c4Root (a * b) = Complex.I ^ (a.val * b.val) := by
  exact (powI_mod_four (a.val * b.val)).symm

-- Orthogonality of the four characters, in the unnormalized Fourier convention.
private theorem sum_c4Root_mul (a : Fin 4) :
    ∑ s : Fin 4, c4Root (a * s) = if a = 0 then 4 else 0 := by
  fin_cases a <;>
    norm_num [Fin.sum_univ_four, Fin.val_mul, Complex.I_sq, pow_succ]

/-- **Factorization of the complex group determinant of $C_4^2$.** For every
$y \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{C}$,

$$
\det\bigl(y(h - g)\bigr)_{g, h \in \mathbb{Z}/4 \times \mathbb{Z}/4} =
\prod_{k=0}^{3} D_4\bigl(z_k(0), z_k(1), z_k(2), z_k(3)\bigr), \qquad
z_k(r) = \sum_{s=0}^{3} i^{ks} y(r, s),
$$

where $i = \sqrt{-1}$ and $D_4(x_0, x_1, x_2, x_3)$ is the determinant of the $4 \times 4$
circulant matrix with first row $(x_0, x_1, x_2, x_3)$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 2 (`integers-2024-A30-cor-2`). -/
public theorem c4Sq_groupDet_eq_prod_circulantDetFour (y : Fin 4 × Fin 4 → ℂ) :
    (circulant y).det =
      ∏ k : Fin 4, circulantDetFour fun r : Fin 4 =>
        ∑ s : Fin 4, Complex.I ^ (k.val * s.val) * y (r, s) := by
  classical
  let z (k r : Fin 4) : ℂ := ∑ s : Fin 4, c4Root (k * s) * y (r, s)
  -- The columns of `P` are indexed by (first coordinate, frequency).
  let P : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
    fun (r, s) (t, k) => if r = t then c4Root (-(k * s)) else 0
  let Q : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
    fun (r, k) (t, s) => if r = t then c4Root (k * s) else 0
  let B := blockDiagonal fun k : Fin 4 => circulant (z k)
  have hQP : Q * P = diagonal (fun _ => (4 : ℂ)) := by
    ext ⟨r, k⟩ ⟨t, l⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    by_cases h : r = t
    · subst t
      trans ∑ s : Fin 4, c4Root ((k - l) * s)
      · calc
          _ = ∑ u : Fin 4, if u = r then ∑ s : Fin 4, c4Root ((k - l) * s) else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : u = r
            · subst u
              simp [P, Q, ← c4Root_add, sub_eq_add_neg, add_mul, neg_mul]
            · simp [P, Q, hu, Ne.symm hu]
          _ = _ := by simp
      · simp [sum_c4Root_mul, diagonal_apply, Prod.mk.injEq, sub_eq_zero]
    · trans (0 : ℂ)
      · apply Finset.sum_eq_zero
        intro u _
        by_cases hu : r = u
        · subst u
          simp [P, Q, h]
        · simp [P, Q, hu]
      · simp [Prod.mk.injEq, h]
  have hz (k r s : Fin 4) :
      ∑ u : Fin 4, y (r, s - u) * c4Root (-(k * u)) = z k r * c4Root (-(k * s)) := by
    rw [show z k r = ∑ a : Fin 4, c4Root (k * a) * y (r, a) from rfl, Finset.sum_mul]
    let e : Fin 4 ≃ Fin 4 := ⟨fun u => s - u, fun a => s - a, sub_sub_cancel s,
      sub_sub_cancel s⟩
    refine Fintype.sum_equiv e _ _ (fun u => ?_)
    change _ = c4Root (k * (s - u)) * y (r, s - u) * c4Root (-(k * s))
    rw [mul_right_comm, ← c4Root_add, ← sub_eq_add_neg, ← mul_sub, sub_sub, add_comm u s,
      ← sub_sub, sub_self, zero_sub, mul_neg]
    ac_rfl
  -- Translation by the original second coordinate produces the positive powers in `z`.
  have hAP : circulant y * P = P * B := by
    ext ⟨r, s⟩ ⟨t, k⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type]
    calc
      _ = ∑ u : Fin 4, if u = t then z k (r - u) * c4Root (-(k * s)) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : u = t
        · simpa [P, hu, circulant_apply] using hz k (r - u) s
        · simp [P, hu]
      _ = z k (r - t) * c4Root (-(k * s)) := by simp
      _ = _ := by
        symm
        calc
          _ = ∑ u : Fin 4, if u = r then c4Root (-(k * s)) * z k (u - t) else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases hu : u = r
            · subst u
              trans ∑ l : Fin 4, if l = k then c4Root (-(k * s)) * z k (r - t) else 0
              · apply Finset.sum_congr rfl
                intro l _
                by_cases hl : l = k
                · subst l
                  simp [B, P, blockDiagonal_apply, circulant_apply]
                · simp [B, blockDiagonal_apply, hl]
              · simp
            · simp [P, hu, Ne.symm hu]
          _ = _ := by simp [mul_comm]
  have hP : P.det ≠ 0 := by
    intro h
    have hdet := congrArg det hQP
    rw [det_mul, h, mul_zero, det_diagonal] at hdet
    exact (Finset.prod_ne_zero_iff.mpr fun _ _ => by norm_num) hdet.symm
  have hdet := congrArg det hAP
  rw [det_mul, det_mul, mul_comm P.det] at hdet
  change (circulant y).det = _
  simpa only [B, det_blockDiagonal, circulantDetFour, z, c4Root_mul] using mul_right_cancel₀ hP hdet

end MetaMathlibExt
