/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/forseti-lean, commit
0a81edc7fe82748af7c9b1139229c4d898f50c28,
`Gimle/Forseti/RationalCongruence.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

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
-/

module
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Weak diagonal dominance and positive semidefiniteness

An elementary quadratic-form proof for real symmetric matrices. The diagonal
is bounded below by the absolute off-diagonal row sum, rather than its absolute
value being bounded below; in particular the diagonal entries are nonnegative.

Mathematical reference: A. E. Brouwer and W. H. Haemers, Spectra of Graphs,
Lemma 2.10.1(ii), https://aeb.win.tue.nl/2WF02/spectra.pdf.
The proof below uses the quadratic form directly rather than a spectral argument.
-/
@[expose] public section
namespace Matrix
private theorem pair_nonnegative (c a b : ℝ) :
    0 ≤ 2 * (a * (c * b)) + |c| * a ^ 2 + |c| * b ^ 2 := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    nlinarith [mul_nonneg hc (sq_nonneg (a + b))]
  · rw [abs_of_neg (lt_of_not_ge hc)]
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hc)) (sq_nonneg (a - b))]

/-- A real symmetric matrix whose diagonal dominates the absolute off-diagonal
row sums is positive semidefinite. Zero diagonal slack is allowed. -/
theorem posSemidef_of_diagonallyDominant {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hs : M.IsHermitian)
    (hd : ∀ i, (∑ j, if i = j then 0 else |M i j|) ≤ M i i) :
    M.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hs, ?_⟩
  intro x
  have hs' (i j : ι) : M i j = M j i := by
    simpa using (congrFun (congrFun hs j) i)
  let O : Matrix ι ι ℝ := fun i j => if i = j then 0 else M i j
  have hsym (i j : ι) : O i j = O j i := by
    dsimp [O]
    by_cases h : i = j
    · subst j; rfl
    · simp [h, Ne.symm h, hs' i j]
  have hrow (i : ι) : (∑ j, |O i j|) ≤ M i i := by
    simpa only [O, apply_ite abs, abs_zero] using hd i
  have hdiag (i : ι) :
      (∑ j, x i * (M i j * x j)) =
        M i i * x i ^ 2 + ∑ j, x i * (O i j * x j) := by
    have he (j : ι) : x i * (M i j * x j) =
        (if j = i then M i i * x i ^ 2 else 0) + x i * (O i j * x j) := by
      by_cases h : j = i
      · subst j; simp [O]; ring
      · simp [O, h, Ne.symm h]
    simp_rw [he, Finset.sum_add_distrib]
    simp
  have hquadratic : dotProduct x (M.mulVec x) = (∑ i, M i i * x i ^ 2) +
      ∑ i, ∑ j, x i * (O i j * x j) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum,
      hdiag, Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, |O i j| * x j ^ 2) =
      ∑ i, ∑ j, |O i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hp : 0 ≤ ∑ i, ∑ j,
      (2 * (x i * (O i j * x j)) + |O i j| * x i ^ 2 + |O i j| * x j ^ 2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      pair_nonnegative (O i j) (x i) (x j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  rw [hswap] at hp
  have hfactor : (∑ i, x i * ∑ j, O i j * x j) =
      ∑ i, ∑ j, x i * (O i j * x j) := by simp only [Finset.mul_sum]
  rw [hfactor] at hp
  have hl : (∑ i, ∑ j, |O i j| * x i ^ 2) ≤
      ∑ i, M i i * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  simpa only [star_trivial] using (show 0 ≤ dotProduct x (M.mulVec x) from by
    rw [hquadratic]
    linarith)

end Matrix
