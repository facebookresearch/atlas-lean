/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement of `bounded_partialDerivs_cube_div_sq_add_sq` below is used under the following
license.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_56.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_56 … := by sorry` into the Batteries `theorem_wanted`
`bounded_partialDerivs_cube_div_sq_add_sq`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system. Further changes in this file: the
`theorem_wanted` is now a `theorem` with a proof, `public import Mathlib` is replaced by narrower
imports, and the docstring also names the textbook source and what the statement leaves out; the
statement itself is unchanged.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The partial derivatives of `x³ / (x² + y²)` are bounded

Let `f : ℝ × ℝ → ℝ` vanish at the origin and equal `x³ / (x² + y²)` elsewhere (W. Rudin,
*Principles of Mathematical Analysis*, 3rd ed., Chapter 9, Exercise 14). Both partial derivatives
of `f` exist at every point of the plane:

* `D₁ f (x, y) = (x⁴ + 3 x² y²) / (x² + y²)²` away from the origin (`hasDerivAt_fst`), and
  `D₁ f (0, 0) = 1` since `f (t, 0) = t` (`hasDerivAt_fst_zero`);
* `D₂ f (x, y) = -2 x³ y / (x² + y²)²` at every point (`hasDerivAt_snd`).

They are bounded, `0 ≤ D₁ f ≤ 9 / 8` and `|D₂ f| ≤ 1` (`exists_hasDerivAt_partials_bounded`); the
upper bound `9 / 8` is attained at the points `(x, y) ≠ (0, 0)` with `x² = 3 y²`.

Part (a) of Rudin's exercise, that `D₁ f` and `D₂ f` are bounded, is the MA-ProofBench problem
`ma_proofbench_l1_56`. Its formal statement, the former `WantedExt` entry
`bounded_partialDerivs_cube_div_sq_add_sq`, kept with its name in namespace
`MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted`, bounds Mathlib's
`deriv`, which is `0` wherever a function is not differentiable, so on its own it does not say
that the partial derivatives exist. It is proved here as a corollary of
`exists_hasDerivAt_partials_bounded`, which does.
-/

@[expose] public section

namespace MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBounded

variable {f : ℝ × ℝ → ℝ}

/-- With Lean's convention `0 / 0 = 0`, `f` is `(x, y) ↦ x³ / (x² + y²)` at every point. -/
private lemma apply_eq (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) → f p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2)) (p : ℝ × ℝ) :
    f p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2) := by
  by_cases hp : p = (0, 0)
  · simp [hp, h0]
  · exact hxy p hp

private lemma sq_add_sq_ne_zero {x y : ℝ} (hp : (x, y) ≠ (0, 0)) : x ^ 2 + y ^ 2 ≠ 0 := by
  intro h
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact hp (by simp_all)

/-- Away from the origin, the partial derivative of `f` in the first variable is
`(x⁴ + 3 x² y²) / (x² + y²)²`. -/
theorem hasDerivAt_fst (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) → f p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2)) {x y : ℝ}
    (hp : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun t => f (t, y)) ((x ^ 4 + 3 * x ^ 2 * y ^ 2) / (x ^ 2 + y ^ 2) ^ 2) x := by
  simp only [apply_eq h0 hxy]
  refine ((hasDerivAt_pow 3 x).fun_div ((hasDerivAt_pow 2 x).add_const (y ^ 2))
    (sq_add_sq_ne_zero hp)).congr_deriv ?_
  push_cast
  ring

/-- At the origin, the partial derivative of `f` in the first variable is `1`: `f (t, 0) = t`. -/
theorem hasDerivAt_fst_zero (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) → f p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2)) :
    HasDerivAt (fun t => f (t, 0)) 1 0 := by
  have h : (fun t => f (t, 0)) = fun t => t := by
    funext t
    rw [apply_eq h0 hxy]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
      ring
  rw [h]
  exact hasDerivAt_id' 0

/-- The partial derivative of `f` in the second variable is `-2 x³ y / (x² + y²)²` at every
point, the origin included, where both sides are `0`. -/
theorem hasDerivAt_snd (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) → f p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2)) (x y : ℝ) :
    HasDerivAt (fun t => f (x, t)) (-2 * x ^ 3 * y / (x ^ 2 + y ^ 2) ^ 2) y := by
  simp only [apply_eq h0 hxy]
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using hasDerivAt_const y (0 : ℝ)
  · refine ((hasDerivAt_const y (x ^ 3)).fun_div ((hasDerivAt_pow 2 y).const_add (x ^ 2))
      (by positivity)).congr_deriv ?_
    push_cast
    ring

/-- **Rudin, Exercise 9.14(a)**, with existence: both partial derivatives of `f` exist at every
point of the plane, the first with values in `[0, 9 / 8]` and the second with values in
`[-1, 1]`.

Source: W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, Chapter 9,
Exercise 14(a). -/
theorem exists_hasDerivAt_partials_bounded (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) → f p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2)) (x y : ℝ) :
    (∃ d, HasDerivAt (fun t => f (t, y)) d x ∧ 0 ≤ d ∧ d ≤ 9 / 8) ∧
      ∃ d, HasDerivAt (fun t => f (x, t)) d y ∧ |d| ≤ 1 := by
  refine ⟨?_, _, hasDerivAt_snd h0 hxy x y, ?_⟩
  · by_cases hp : (x, y) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      exact ⟨1, hasDerivAt_fst_zero h0 hxy, zero_le_one, by norm_num⟩
    · have hd : 0 < (x ^ 2 + y ^ 2) ^ 2 := by
        have := sq_add_sq_ne_zero hp
        positivity
      refine ⟨_, hasDerivAt_fst h0 hxy hp, by positivity, ?_⟩
      rw [div_le_iff₀ hd]
      nlinarith [sq_nonneg (x ^ 2 - 3 * y ^ 2)]
  · rcases eq_or_ne (x ^ 2 + y ^ 2) 0 with hd | hd
    · simp [hd]
    · have hd' : 0 < (x ^ 2 + y ^ 2) ^ 2 := by positivity
      rw [abs_div, abs_of_pos hd', div_le_one hd', abs_le]
      constructor <;>
        nlinarith [sq_nonneg (x * (x + y)), sq_nonneg (x * (x - y)), sq_nonneg (x * y),
          sq_nonneg (y ^ 2)]

end MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBounded

namespace MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted

open MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBounded

/-- Define $f(0,0)=0$ and

\[
f(x,y)=\frac{x^3}{x^2+y^2}\qquad \text{if }(x,y)\ne(0,0).
\]
Prove that $D_1f$ and $D_2f$ are bounded functions in $R^2$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_56.lean` at
openbmb/ma-proofbench@31bab4c; the problem is W. Rudin, *Principles of Mathematical Analysis*,
3rd ed., Chapter 9, Exercise 14(a).

Proves `Wanted` entry `bounded_partialDerivs_cube_div_sq_add_sq`. Mathlib's `deriv` is `0` where a
function is not differentiable, so this statement does not say that the partial derivatives
exist; `exists_hasDerivAt_partials_bounded` does.
-/
theorem bounded_partialDerivs_cube_div_sq_add_sq (f : ℝ × ℝ → ℝ) (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) → f p = (p.1 ^ 3) / (p.1 ^ 2 + p.2 ^ 2)) :
    (∃ M : ℝ, ∀ x y : ℝ, ‖deriv (fun t => f (t, y)) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x y : ℝ, ‖deriv (fun t => f (x, t)) y‖ ≤ M) := by
  refine ⟨⟨9 / 8, fun x y => ?_⟩, ⟨1, fun x y => ?_⟩⟩
  · obtain ⟨d, hd, hd0, hd1⟩ := (exists_hasDerivAt_partials_bounded h0 hxy x y).1
    rwa [hd.deriv, Real.norm_eq_abs, abs_of_nonneg hd0]
  · obtain ⟨d, hd, hd1⟩ := (exists_hasDerivAt_partials_bounded h0 hxy x y).2
    rwa [hd.deriv, Real.norm_eq_abs]

end MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted
