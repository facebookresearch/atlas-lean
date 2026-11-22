/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace MetaMathlibExt

@[expose] public section

private theorem deGua_dist01 (a b : ℝ) :
    dist (EuclideanSpace.single (0 : Fin 3) a)
        (EuclideanSpace.single (1 : Fin 3) b) ^ 2 = a ^ 2 + b ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  have h01ne : (0 : Fin 3) ≠ 1 := by decide
  have e1 : ⟪EuclideanSpace.single (0 : Fin 3) a,
      EuclideanSpace.single (1 : Fin 3) b⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, PiLp.single_apply,
      ite_eq_right h01ne, mul_zero]
  have n0 : ‖EuclideanSpace.single (0 : Fin 3) a‖ ^ 2 = a ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have n1 : ‖EuclideanSpace.single (1 : Fin 3) b‖ ^ 2 = b ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [e1, n0, n1]
  ring

private theorem deGua_dist12 (b c : ℝ) :
    dist (EuclideanSpace.single (1 : Fin 3) b)
        (EuclideanSpace.single (2 : Fin 3) c) ^ 2 = b ^ 2 + c ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  have h12ne : (1 : Fin 3) ≠ 2 := by decide
  have e1 : ⟪EuclideanSpace.single (1 : Fin 3) b,
      EuclideanSpace.single (2 : Fin 3) c⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, PiLp.single_apply,
      ite_eq_right h12ne, mul_zero]
  have n0 : ‖EuclideanSpace.single (1 : Fin 3) b‖ ^ 2 = b ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have n1 : ‖EuclideanSpace.single (2 : Fin 3) c‖ ^ 2 = c ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [e1, n0, n1]
  ring

private theorem deGua_dist20 (c a : ℝ) :
    dist (EuclideanSpace.single (2 : Fin 3) c)
        (EuclideanSpace.single (0 : Fin 3) a) ^ 2 = c ^ 2 + a ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real]
  have h20ne : (2 : Fin 3) ≠ 0 := by decide
  have e1 : ⟪EuclideanSpace.single (2 : Fin 3) c,
      EuclideanSpace.single (0 : Fin 3) a⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, PiLp.single_apply,
      ite_eq_right h20ne, mul_zero]
  have n0 : ‖EuclideanSpace.single (2 : Fin 3) c‖ ^ 2 = c ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have n1 : ‖EuclideanSpace.single (0 : Fin 3) a‖ ^ 2 = a ^ 2 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [e1, n0, n1]
  ring

/-- **De Gua's theorem with Heron's formula.** Let $a, b, c > 0$ and let $p_0 = (a, 0, 0)$,
$p_1 = (0, b, 0)$, $p_2 = (0, 0, c)$ in $\mathbb{R}^3$, so that the tetrahedron with vertices
$0, p_0, p_1, p_2$ has a right angle between any two of the edges at $0$, with legs of lengths
$a$, $b$, $c$. Let $d_{01} = d(p_0, p_1)$, $d_{12} = d(p_1, p_2)$ and $d_{20} = d(p_2, p_0)$ be the
Euclidean distances, let $s = (d_{01} + d_{12} + d_{20})/2$, and let
$A = \sqrt{s(s - d_{01})(s - d_{12})(s - d_{20})}$, the area of the face $p_0 p_1 p_2$ by Heron's
formula. Then $A^2 = (ab/2)^2 + (bc/2)^2 + (ca/2)^2$.

Proves `Wanted` entry `deGua_theorem`.

Source: https://en.wikipedia.org/wiki/De_Gua%27s_theorem
-/
theorem deGua_theorem : ∀ (a b c A : ℝ),
  let p₀ := EuclideanSpace.single (0 : Fin 3) a
  let p₁ := EuclideanSpace.single (1 : Fin 3) b
  let p₂ := EuclideanSpace.single (2 : Fin 3) c
  let s := (dist p₀ p₁ + dist p₁ p₂ + dist p₂ p₀) / 2
  0 < a → 0 < b → 0 < c →
  A = Real.sqrt (s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀)))) →
  A ^ 2 = (a * b / 2) ^ 2 + (b * c / 2) ^ 2 + (c * a / 2) ^ 2 := by
  intro a b c A p₀ p₁ p₂ s _ _ _ hA
  have e0 : p₀ = EuclideanSpace.single (0 : Fin 3) a := rfl
  have e1 : p₁ = EuclideanSpace.single (1 : Fin 3) b := rfl
  have e2 : p₂ = EuclideanSpace.single (2 : Fin 3) c := rfl
  have es : s = (dist p₀ p₁ + dist p₁ p₂ + dist p₂ p₀) / 2 := rfl
  have h01 : dist p₀ p₁ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [e0, e1]; exact deGua_dist01 a b
  have h12 : dist p₁ p₂ ^ 2 = b ^ 2 + c ^ 2 := by
    rw [e1, e2]; exact deGua_dist12 b c
  have h20 : dist p₂ p₀ ^ 2 = c ^ 2 + a ^ 2 := by
    rw [e2, e0]; exact deGua_dist20 c a
  have d01nn : 0 ≤ dist p₀ p₁ := dist_nonneg
  have d12nn : 0 ≤ dist p₁ p₂ := dist_nonneg
  have d20nn : 0 ≤ dist p₂ p₀ := dist_nonneg
  have t1 : dist p₀ p₁ ≤ dist p₀ p₂ + dist p₂ p₁ := dist_triangle _ _ _
  have t2 : dist p₁ p₂ ≤ dist p₁ p₀ + dist p₀ p₂ := dist_triangle _ _ _
  have t3 : dist p₂ p₀ ≤ dist p₂ p₁ + dist p₁ p₀ := dist_triangle _ _ _
  have c01 : dist p₁ p₀ = dist p₀ p₁ := dist_comm _ _
  have c12 : dist p₂ p₁ = dist p₁ p₂ := dist_comm _ _
  have c20 : dist p₀ p₂ = dist p₂ p₀ := dist_comm _ _
  have hsnn : 0 ≤ s := by rw [es]; linarith
  have hs01 : 0 ≤ s - dist p₀ p₁ := by rw [es]; linarith
  have hs12 : 0 ≤ s - dist p₁ p₂ := by rw [es]; linarith
  have hs20 : 0 ≤ s - dist p₂ p₀ := by rw [es]; linarith
  have hH : 0 ≤ s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀))) :=
    mul_nonneg hsnn (mul_nonneg hs01 (mul_nonneg hs12 hs20))
  have hAsq : A ^ 2
      = s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀))) := by
    rw [hA, Real.sq_sqrt hH]
  have key : 16 * (s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀))))
      = 2 * ((dist p₀ p₁ ^ 2) * (dist p₁ p₂ ^ 2) + (dist p₁ p₂ ^ 2) * (dist p₂ p₀ ^ 2)
        + (dist p₂ p₀ ^ 2) * (dist p₀ p₁ ^ 2))
        - ((dist p₀ p₁ ^ 2) ^ 2 + (dist p₁ p₂ ^ 2) ^ 2
          + (dist p₂ p₀ ^ 2) ^ 2) := by
    rw [es]; ring
  rw [h01, h12, h20] at key
  have hHval : s * ((s - dist p₀ p₁) * ((s - dist p₁ p₂) * (s - dist p₂ p₀)))
      = (a * b / 2) ^ 2 + (b * c / 2) ^ 2 + (c * a / 2) ^ 2 := by
    linear_combination key / 16
  rw [hAsq]
  exact hHval

end

end MetaMathlibExt
