/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkFiniteGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Chebyshev

/-!
# The return probability bound for a symmetric group walk

For a walk on a finite group, all the diagonal entries of a power of its transition matrix
are the same. For a symmetric step distribution, the trace at time `2 * k` consequently
controls the total variation distance at time `k`. This is the regular representation form
of the upper bound lemma of Diaconis and Shahshahani, *Generating a random permutation with
random transpositions* (1981), Lemmas 2 and 14.
-/

@[expose] public section

namespace MathlibExt.Probability.RandomWalkFiniteGroup

open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (conv convPow sum_conv)
open MathlibExt.Probability.MarkovMixing (tvDist)
open Matrix

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G]

/-- The transition matrix acting on column vectors for a walk by left multiplication.
Its column at `y` is the law after one step starting at `y`. -/
def walkMatrix (P : G → ℝ) : Matrix G G ℝ := fun x y => P (x * y⁻¹)

/-- Each column of the `k`-step transition matrix is a translate of the `k`-step law. -/
theorem walkMatrix_pow_apply (P : G → ℝ) (k : ℕ) (x y : G) :
    (walkMatrix P ^ k) x y = convPow P k (x * y⁻¹) := by
  induction k generalizing x y with
  | zero => simp [convPow, Matrix.one_apply, mul_inv_eq_one]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, convPow, conv]
    simp only [walkMatrix, ih]
    rw [← Equiv.sum_comp (Equiv.mulRight y⁻¹)
      (fun t => P (x * y⁻¹ * t⁻¹) * convPow P k t)]
    simp [mul_assoc]

/-- For a symmetric step distribution of total mass one, the trace of the transition matrix
at time `2 * k`, minus the stationary contribution `1`, bounds four times the squared total
variation distance. This version uses no classification of the irreducible representations. -/
theorem four_mul_tvDist_sq_le_trace_walkMatrix_pow (P : G → ℝ) (hP : ∑ x, P x = 1)
    (hsym : ∀ x, P x⁻¹ = P x) (k : ℕ) :
    4 * tvDist (convPow P k) (uniform G) ^ 2 ≤ (walkMatrix P ^ (2 * k)).trace - 1 := by
  let N : ℝ := Fintype.card G
  let p := convPow P k
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum (t : ℕ) : ∑ x, convPow P t x = 1 := by
    induction t with
    | zero => simp [convPow]
    | succ t ih => rw [convPow, sum_conv, hP, ih, one_mul]
  have htr : (walkMatrix P ^ (2 * k)).trace = N * ∑ x, p x ^ 2 := by
    have hs : (walkMatrix P).IsSymm := by
      ext x y
      simpa [walkMatrix] using hsym (x * y⁻¹)
    have hdiag (x : G) : (walkMatrix P ^ (2 * k)) x x = ∑ y, p y ^ 2 := by
      rw [walkMatrix_pow_apply, mul_inv_cancel]
      rw [← show (walkMatrix P ^ (2 * k)) 1 1 = convPow P (2 * k) 1 by
        simp [walkMatrix_pow_apply]]
      rw [two_mul, pow_add, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [(hs.pow k).apply, walkMatrix_pow_apply]
      simp [p, sq]
    simp [Matrix.trace, Matrix.diag, hdiag, N]
  have hc := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset G))
    (f := fun x => |p x - N⁻¹|)
  simp only [Finset.card_univ, sq_abs] at hc
  have hterm (x : G) : (p x - N⁻¹) ^ 2 = p x ^ 2 - p x * (2 * N⁻¹) + (N⁻¹) ^ 2 := by ring
  have hm : ∑ x, p x = 1 := hsum k
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hm,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← show N = (Fintype.card G : ℝ) from rfl] at hc
  rw [htr]
  change 4 * (1 / 2 * ∑ x, |p x - N⁻¹|) ^ 2 ≤ _
  calc
    _ = (∑ x, |p x - N⁻¹|) ^ 2 := by ring
    _ ≤ _ := hc.trans_eq (by field_simp; ring)

end MathlibExt.Probability.RandomWalkFiniteGroup
