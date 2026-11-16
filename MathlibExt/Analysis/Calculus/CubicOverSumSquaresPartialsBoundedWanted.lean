/-
# Partials of x³/(x²+y²) are bounded

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

Attribution and modification notice: the statement below is taken from
openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level1/ma_proofbench_l1_56.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of
LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782;
byte-identical to the Hugging Face dataset openbmb/MA-ProofBench),
distributed under the MIT License above.

Changes made: completed the original benchmark problem with a proof of the
theorem named `bounded_partialDerivs_cube_div_sq_add_sq`; moved the informal
problem statement docstring onto it; placed the declaration in namespace
`MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted`;
and replaced `import Mathlib` with `public import Mathlib` under the
module system.
-/

module

public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted

/-- Define $f(0,0)=0$ and

\[
f(x,y)=\frac{x^3}{x^2+y^2}\qquad \text{if }(x,y)\ne(0,0).
\]
Prove that $D_1f$ and $D_2f$ are bounded functions in $R^2$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_56.lean` at
openbmb/ma-proofbench@31bab4c.
-/

theorem bounded_partialDerivs_cube_div_sq_add_sq (f : ℝ × ℝ → ℝ) (h0 : f (0, 0) = 0)
    (hxy : ∀ p : ℝ × ℝ, p ≠ (0, 0) →
      f p = (p.1 ^ 3) / (p.1 ^ 2 + p.2 ^ 2)) :
    (∃ M : ℝ, ∀ x y : ℝ, ‖deriv (fun t => f (t, y)) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x y : ℝ, ‖deriv (fun t => f (x, t)) y‖ ≤ M) := by
  constructor
  · use 4 -- Bound for the first partial derivative
    intro x y
    by_cases h : (x, y) = (0, 0)
    · rcases h with ⟨rfl, rfl⟩
      have h_piece : (fun t : ℝ => f (t, 0)) = fun t => t := by
        funext t
        by_cases ht : t = 0
        · subst t
          exact h0
        · have h_ne : (t, (0 : ℝ)) ≠ (0, 0) := by
            intro heq
            injection heq with ht_eq _
            exact ht ht_eq
          rw [hxy (t, 0) h_ne]
          simp
          field_simp
      rw [h_piece]
      simp
    · by_cases hy0 : y = 0
      -- Split according to whether the y-coordinate is zero
      -- If y = 0, the slice simplifies to the identity function
      · subst y
        have h_piece : (fun t : ℝ => f (t, 0)) = fun t => t := by
          funext t
          by_cases ht : t = 0
          · subst t
            exact h0
          · have h_ne : (t, (0 : ℝ)) ≠ (0, 0) := by
              intro heq
              injection heq with ht_eq _
              exact ht ht_eq
            rw [hxy (t, 0) h_ne]
            simp
            field_simp
        rw [h_piece]
        simp
      · have hy : y ≠ 0 := hy0
        -- Since y ≠ 0, the entire slice avoids the origin
        have h_piece :
            (fun t : ℝ => f (t, y)) =
              (fun t => t ^ 3 / (t ^ 2 + y ^ 2)) := by
          funext t
          apply hxy
          intro hp
          exact hy (congrArg Prod.snd hp)
        rw [h_piece]
        -- Prove the denominator is never zero
        have hden : x ^ 2 + y ^ 2 ≠ 0 := by
          positivity
        -- Differentiate the numerator
        have hnum :
            HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
          convert (hasDerivAt_id x).pow 3 using 1
          · funext t
            rfl
          · norm_num
        -- Differentiate the denominator
        have hden' :
            HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
          convert
            ((hasDerivAt_id x).pow 2).add
              (hasDerivAt_const x (y ^ 2)) using 1
          · funext t
            simp
          · norm_num
        -- Apply the quotient rule
        have hquot := hnum.div hden' hden
        have hderiv :
            deriv (fun t : ℝ => t ^ 3 / (t ^ 2 + y ^ 2)) x =
              (x ^ 4 + 3 * x ^ 2 * y ^ 2) /
                (x ^ 2 + y ^ 2) ^ 2 := by
          convert hquot.deriv using 1
          field_simp
          ring
        rw [hderiv]
        have hbound :
            |(x ^ 4 + 3 * x ^ 2 * y ^ 2) /
              (x ^ 2 + y ^ 2) ^ 2| ≤ 4 := by
          have hpos : 0 < (x ^ 2 + y ^ 2) ^ 2 := by
            positivity
          rw [abs_of_nonneg
            (div_nonneg (by positivity) (le_of_lt hpos))]
          apply (div_le_iff₀ hpos).2
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
        -- Convert the absolute-value bound to the norm bound
        simpa only [Real.norm_eq_abs] using hbound
  · use 2 -- Bound for the second partial derivative
    intro x y
    by_cases h : (x, y) = (0, 0)
    · rcases h with ⟨rfl, rfl⟩
      have h_piece : (fun t : ℝ => f (0, t)) = fun t => 0 := by
        funext t
        by_cases ht : t = 0
        · subst t
          exact h0
        · have h_ne : ((0 : ℝ), t) ≠ (0, 0) := by
            intro heq
            injection heq with _ ht_eq
            exact ht ht_eq
          rw [hxy (0, t) h_ne]
          simp
      rw [h_piece]
      simp
    · by_cases hx0 : x = 0
      -- Split according to whether the x-coordinate is zero
      -- If x = 0, the slice is identically zero
      · subst x
        have h_piece : (fun t : ℝ => f (0, t)) = fun t => 0 := by
          funext t
          by_cases ht : t = 0
          · subst t
            exact h0
          · have h_ne : ((0 : ℝ), t) ≠ (0, 0) := by
              intro heq
              injection heq with _ ht_eq
              exact ht ht_eq
            rw [hxy (0, t) h_ne]
            simp
        rw [h_piece]
        simp
      · have hx : x ≠ 0 := hx0
        -- Establish the Y-slice rational formula
        have h_piece :
            (fun t : ℝ => f (x, t)) =
              (fun t => x ^ 3 / (x ^ 2 + t ^ 2)) := by
          funext t
          apply hxy
          intro hp
          exact hx (congrArg Prod.fst hp)
        rw [h_piece]
        have hden : x ^ 2 + y ^ 2 ≠ 0 := by
          positivity
        -- Derivative of the constant numerator (x^3) with respect to t is zero
        have hnum :
            HasDerivAt (fun t : ℝ => x ^ 3) 0 y := by
          simpa using (hasDerivAt_const y (x ^ 3))
        -- Derivative of the denominator (x^2 + t^2) with respect to t
        have hden' :
            HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
          convert
            (hasDerivAt_const y (x ^ 2)).add
              ((hasDerivAt_id y).pow 2) using 1
          · funext t
            simp
          · norm_num
        -- Apply the quotient rule
        have hquot := hnum.div hden' hden
        have hderiv :
            deriv (fun t : ℝ => x ^ 3 / (x ^ 2 + t ^ 2)) y =
              (-2 * x ^ 3 * y) / (x ^ 2 + y ^ 2) ^ 2 := by
          convert hquot.deriv using 1
          field_simp
          ring
        rw [hderiv]
        have hpos : 0 < (x ^ 2 + y ^ 2) ^ 2 := by
          positivity
        -- Rewrite the numerator absolute value to isolate cross-terms
        have habs :
            |x ^ 3 * y| = x ^ 2 * (|x| * |y|) := by
          calc
            |x ^ 3 * y| = |x| ^ 3 * |y| := by
              rw [abs_mul, abs_pow]
            _ = x ^ 2 * (|x| * |y|) := by
              rw [← sq_abs x]
              ring
        have hxabs : |x| ^ 2 = x ^ 2 := by
          exact sq_abs x
        have hyabs : |y| ^ 2 = y ^ 2 := by
          exact sq_abs y
        have hxy_bound :
            2 * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
          nlinarith [sq_nonneg (|x| - |y|), hxabs, hyabs]
        -- Use the cross-term bound to establish the main numerator inequality
        have hnum_bound :
            2 * |x ^ 3 * y| ≤ (x ^ 2 + y ^ 2) ^ 2 := by
          rw [habs]
          have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
          have hsum : x ^ 2 ≤ x ^ 2 + y ^ 2 := by
            have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
            linarith
          have hstep1 :=
            mul_le_mul_of_nonneg_left hxy_bound hx2
          have hstep2 :=
            mul_le_mul_of_nonneg_right hsum
              (by positivity : 0 ≤ x ^ 2 + y ^ 2)
          nlinarith [hstep1, hstep2]
        have habs_num :
            |(-2 : ℝ) * x ^ 3 * y| = 2 * |x ^ 3 * y| := by
          have hfactor :
              (-2 : ℝ) * x ^ 3 * y = -(2 * (x ^ 3 * y)) := by
            ring
          rw [hfactor, abs_neg, abs_mul,
            abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        -- Combine everything to prove the fractional absolute value is bounded by 2
        have hbound :
            |(-2 * x ^ 3 * y) /
              (x ^ 2 + y ^ 2) ^ 2| ≤ 2 := by
          rw [abs_div, habs_num,
            abs_of_nonneg (le_of_lt hpos)]
          apply (div_le_iff₀ hpos).2
          nlinarith [hnum_bound]
        change |(-2 * x ^ 3 * y) / (x ^ 2 + y ^ 2) ^ 2| ≤ 2
        exact hbound
end MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted
