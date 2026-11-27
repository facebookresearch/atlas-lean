/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.LinearCombination

/-!
# Integer matrices with a Pisa eigenvector

For positive integers `j` and `m`, the number `τ = (j + √(j ^ 2 + 4 * m)) / 2` is the larger root
of `X ^ 2 - j * X - m`. We determine the integer `2 × 2` matrices `M` for which `(τ, 1)` is a
right eigenvector over `ℝ`. The eigenvalue is then the second coordinate `M 1 0 * τ + M 1 1` of
`M (τ, 1)`, so the eigenvector equation is `M 0 0 * τ + M 0 1 = (M 1 0 * τ + M 1 1) * τ`.

* If `j ^ 2 + 4 * m` is not a perfect square, then `τ` is irrational. Using `τ ^ 2 = j * τ + m`,
  the eigenvector equation becomes `A * τ + B = 0` with integers `A` and `B`, so it holds exactly
  when `A = B = 0`.
* If `j ^ 2 + 4 * m = r ^ 2` with `r` a natural number, then `τ = (j + r) / 2` and clearing
  denominators turns the eigenvector equation into one equation between integers.

This is Theorem 4.26 of arXiv:2410.12173v1, the preprint of the article by Coons, Ramsey and
Strungaru cited in the docstring of `pisa_eigenvector_iff`; that docstring explains why `r` is
taken nonnegative in the second case.
-/

namespace MetaMathlibExt

namespace pisa_eigenvector_iff

/-- `(τ, 1)` is a right eigenvector of the real image of an integer `2 × 2` matrix `M` exactly
when the first coordinate of `M (τ, 1)` is `τ` times the second one. -/
private theorem exists_mulVec_eq_smul_iff (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℝ) :
    (∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1]) ↔
      (M 0 0 : ℝ) * τ + M 0 1 = ((M 1 0 : ℝ) * τ + M 1 1) * τ := by
  have hmul : (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] =
      ![(M 0 0 : ℝ) * τ + M 0 1, (M 1 0 : ℝ) * τ + M 1 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [hmul, funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.smul_apply, smul_eq_mul, mul_one]
  exact ⟨fun ⟨c, h0, h1⟩ => h1 ▸ h0, fun h => ⟨_, h, rfl⟩⟩

end pisa_eigenvector_iff

/-- **Integer matrices with a Pisa eigenvector.** Let $j, m \ge 1$ be integers, let
$\tau_{j,m} = (j + \sqrt{j^2 + 4m})/2$, and let $M$ be a $2 \times 2$ integer matrix.
(a) If $j^2 + 4m$ is not a perfect square, then $(\tau_{j,m}, 1)^T$ is a right eigenvector of $M$
over $\mathbb{R}$ if and only if $M$ has rows $(t + sj, ms)$ and $(s, t)$ for some integers $s, t$.
(b) If $j^2 + 4m = r^2$ with $r$ a natural number, then $(\tau_{j,m}, 1)^T$ is a right
eigenvector of $M$ over $\mathbb{R}$ if and only if $M$ has rows $(s, t)$ and $(u, v)$ with
$u(j+r)^2 + 2(v-s)(j+r) - 4t = 0$.

In (b) $r$ is the nonnegative root, as the paper's proof uses $\tau_{j,m} = (j + r)/2$. For the
negative root the printed statement fails: for $j = 1$, $m = 2$, $r = -3$, the matrix $M$ with
rows $(0, 0)$ and $(1, 1)$ satisfies $u(j+r)^2 + 2(v-s)(j+r) - 4t = 4 - 4 - 0 = 0$, but
$\tau_{1,2} = 2$ and $M (2, 1)^T = (0, 3)^T$ is not a multiple of $(2, 1)^T$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 63
(`jis-2025-25.1.5-thm-63`). -/
public theorem pisa_eigenvector_iff (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    let τ : ℝ := (j + Real.sqrt (j ^ 2 + 4 * m)) / 2
    let IsEig := ∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1]
    ((¬ IsSquare (j ^ 2 + 4 * m)) → (IsEig ↔ ∃ s t : ℤ, M = !![t + s * j, m * s; s, t])) ∧
      ∀ r : ℕ, j ^ 2 + 4 * m = r ^ 2 →
        (IsEig ↔ ∃ s t u v : ℤ,
          u * (j + r) ^ 2 + 2 * (v - s) * (j + r) - 4 * t = 0 ∧ M = !![s, t; u, v]) := by
  intro τ IsEig
  have hEig : IsEig ↔ (M 0 0 : ℝ) * τ + M 0 1 = ((M 1 0 : ℝ) * τ + M 1 1) * τ :=
    pisa_eigenvector_iff.exists_mulVec_eq_smul_iff M τ
  have hτ : τ = (j + Real.sqrt (j ^ 2 + 4 * m)) / 2 := rfl
  clear_value τ IsEig
  rw [hEig]
  clear hEig IsEig
  refine ⟨fun hsq => ?_, fun r hr => ?_⟩
  · -- `τ` is irrational and `τ ^ 2 = j * τ + m`: compare the coefficients of `1` and `τ`.
    have hsqrt : Real.sqrt ((j : ℝ) ^ 2 + 4 * m) ^ 2 = (j : ℝ) ^ 2 + 4 * m :=
      Real.sq_sqrt (by positivity)
    have hτ2 : τ ^ 2 = j * τ + m := by
      rw [hτ]
      linear_combination hsqrt / 4
    have hirr : Irrational τ := by
      have h := irrational_sqrt_natCast_iff.2 hsq
      push_cast at h
      rw [hτ]
      exact (h.natCast_add j).div_natCast two_ne_zero
    have key : (M 0 0 : ℝ) * τ + M 0 1 = ((M 1 0 : ℝ) * τ + M 1 1) * τ ↔
        ((M 0 0 - M 1 0 * j - M 1 1 : ℤ) : ℝ) * τ + ((M 0 1 - M 1 0 * m : ℤ) : ℝ) = 0 := by
      push_cast
      constructor <;> intro h
      · linear_combination h + (M 1 0 : ℝ) * hτ2
      · linear_combination h - (M 1 0 : ℝ) * hτ2
    rw [key]
    constructor
    · intro h
      have hA : M 0 0 - M 1 0 * j - M 1 1 = 0 := by
        by_contra hA
        have h' := (hirr.intCast_mul hA).add_intCast (M 0 1 - M 1 0 * m)
        rw [h] at h'
        exact h'.ne_zero rfl
      have hB : M 0 1 - M 1 0 * m = 0 := by
        rw [hA, Int.cast_zero, zero_mul, zero_add] at h
        exact_mod_cast h
      refine ⟨M 1 0, M 1 1, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp <;> linarith
    · rintro ⟨s, t, rfl⟩
      simp [mul_comm]
  · -- `τ = (j + r) / 2` is rational: clear the denominators.
    have hsqrt : Real.sqrt ((j : ℝ) ^ 2 + 4 * m) = r := by
      have h : ((j : ℝ) ^ 2 + 4 * m) = (r : ℝ) ^ 2 := by exact_mod_cast hr
      rw [h, Real.sqrt_sq (Nat.cast_nonneg r)]
    rw [hτ, hsqrt]
    constructor
    · intro h
      refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, ?_, Matrix.eta_fin_two M⟩
      have h' : ((M 1 0 * (j + r) ^ 2 + 2 * (M 1 1 - M 0 0) * (j + r) - 4 * M 0 1 : ℤ) : ℝ) =
          0 := by
        push_cast
        linear_combination (-4 : ℝ) * h
      exact_mod_cast h'
    · rintro ⟨s, t, u, v, h, rfl⟩
      have h' : ((u * (j + r) ^ 2 + 2 * (v - s) * (j + r) - 4 * t : ℤ) : ℝ) = 0 := by
        exact_mod_cast h
      push_cast at h'
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      linear_combination (-1 / 4 : ℝ) * h'

end MetaMathlibExt
