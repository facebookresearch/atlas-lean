/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Convex.Function

/-!
# Operator convexity of the square, and failure of its operator monotonicity

Following E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*
(lecture-notes draft of May 3, 2009; published in *Entropy and the Quantum*, Contemp. Math. 529,
Amer. Math. Soc., 2010, pp. 73–140), Definition 2.1 and Section 2.1, a real function `f` is
*operator convex* when `f(t A + (1 - t) B) ≤ t f(A) + (1 - t) f(B)` in the Loewner order for all
self-adjoint `A, B` and `0 ≤ t ≤ 1`, and *operator monotone* when `A ≤ B` implies `f(A) ≤ f(B)`.

This file proves the elementary endpoint `f(t) = t²` of the Loewner–Heinz family
(Carlen, Theorem 2.6, the case `p = 2`), in every star-ordered real algebra, from the identity
`t a² + (1 - t) b² - (t a + (1 - t) b)² = t (1 - t) (a - b)²`. It also records the classical
counterexample showing that `t ↦ t²` is *not* operator monotone, although it is monotone on
`[0, ∞)`: operator monotonicity is a much stronger property than scalar monotonicity.

Mathlib already proves the rest of the basic theory in C⋆-algebras: `CFC.monotone_rpow` and
`CFC.concaveOn_rpow` (`t ↦ t ^ p` is operator monotone and operator concave for `p ∈ [0, 1]`),
`CFC.log_le_log` and `CFC.concaveOn_log`, `CStarAlgebra.inv_le_inv` (`t ↦ -t⁻¹` is operator
monotone) and `CStarAlgebra.convexOn_ringInverse` (`t ↦ t⁻¹` is operator convex). Physlib proves
the convex half, `t ↦ t ^ p` operator convex on positive elements of a nontrivial C⋆-algebra for
`p ∈ [1, 2]`, as `LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici`; the result here is
not subsumed by it, since it holds on all self-adjoint elements of any star-ordered real algebra.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder Matrix

namespace MathlibExt.Analysis.CStarAlgebra.OperatorConvexSq

section General

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **Convex-combination identity for squares.** In any real algebra,
`t a² + (1 - t) b² - (t a + (1 - t) b)² = t (1 - t) (a - b)²`. It is the algebraic heart of
the operator convexity of `t ↦ t²` (Carlen, *Trace inequalities and quantum entropy*, 2009
draft, Section 2.1). -/
theorem smul_sq_add_smul_sq_sub_sq (a b : A) (t : ℝ) :
    t • (a * a) + (1 - t) • (b * b) - (t • a + (1 - t) • b) * (t • a + (1 - t) • b) =
      (t * (1 - t)) • ((a - b) * (a - b)) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_smul_comm]
  module

variable [StarRing A] [PartialOrder A] [StarOrderedRing A] [StarModule ℝ A]

/-- **The square is operator convex.** For self-adjoint elements `a, b` of a star-ordered real
algebra and `0 ≤ t ≤ 1`, `(t a + (1 - t) b)² ≤ t a² + (1 - t) b²`. This is the case `p = 2` of the
operator convexity part of the Loewner–Heinz theorem (E. A. Carlen, *Trace inequalities and
quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.6), stated
for every star-ordered real algebra rather than only for matrices. -/
theorem sq_convex_comb_le {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (t • a + (1 - t) • b) * (t • a + (1 - t) • b) ≤ t • (a * a) + (1 - t) • (b * b) := by
  rw [← sub_nonneg, smul_sq_add_smul_sq_sub_sq]
  set s : ℝ := Real.sqrt (t * (1 - t))
  have hs : s * s = t * (1 - t) := Real.mul_self_sqrt (mul_nonneg ht₀ (by linarith))
  have hc : star (s • (a - b)) = s • (a - b) := by
    rw [star_smul, star_trivial, star_sub, ha.star_eq, hb.star_eq]
  have key := star_mul_self_nonneg (s • (a - b))
  rw [hc, smul_mul_smul_comm, hs] at key
  exact key

/-- **The square is operator convex, as a convex function.** The map `a ↦ a²` is convex, for the
star order, on the convex set of self-adjoint elements of a star-ordered real algebra
(E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes
draft of May 3, 2009, Definition 2.1 and Theorem 2.6 with `p = 2`). -/
theorem convexOn_mul_self :
    ConvexOn ℝ {a : A | IsSelfAdjoint a} (fun a => a * a) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy s t _ _ _
    exact ((IsSelfAdjoint.all s).smul hx).add ((IsSelfAdjoint.all t).smul hy)
  · intro x hx y hy s t hs ht hst
    obtain rfl : t = 1 - s := by linarith
    exact sq_convex_comb_le hx hy hs (by linarith)

end General

section Counterexample

/-- The first matrix of the counterexample: `!![1, 1; 1, 1]`. -/
private def cxA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 1]

/-- The second matrix of the counterexample: `!![2, 1; 1, 1]`. -/
private def cxB : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 1]

/-- **The square is not operator monotone.** There are positive-semidefinite `2 × 2` complex
matrices `A ≤ B` (Loewner order) with `A² ≰ B²`: take `A = !![1, 1; 1, 1]` and
`B = !![2, 1; 1, 1]`, so that `B - A = !![1, 0; 0, 0] ≥ 0` while
`B² - A² = !![3, 1; 1, 0]` has negative determinant. So `t ↦ t²`, monotone on `[0, ∞)`, is not
operator monotone; compare the Loewner–Heinz theorem (E. A. Carlen, *Trace inequalities and
quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.6), which
asserts operator monotonicity of `t ↦ t ^ p` for `0 ≤ p ≤ 1`. -/
theorem not_monotone_sq :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.PosSemidef ∧ A ≤ B ∧ ¬ A * A ≤ B * B := by
  refine ⟨cxA, cxB, ?_, ?_, ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [cxA, Matrix.conjTranspose_apply]
    · have : star x ⬝ᵥ (cxA *ᵥ x) = star (x 0 + x 1) * (x 0 + x 1) := by
        simp [cxA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      rw [this]; exact star_mul_self_nonneg _
  · rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [cxA, cxB, Matrix.conjTranspose_apply]
    · have : star x ⬝ᵥ ((cxB - cxA) *ᵥ x) = star (x 0) * x 0 := by
        simp [cxA, cxB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]; norm_num
      rw [this]; exact star_mul_self_nonneg _
  · rw [Matrix.le_iff]
    intro h
    have := h.dotProduct_mulVec_nonneg ![1, -4]
    have hval : star ![(1 : ℂ), -4] ⬝ᵥ ((cxB * cxB - cxA * cxA) *ᵥ ![1, -4]) = -5 := by
      simp [cxA, cxB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, map_ofNat]
      norm_num
    rw [hval] at this
    exact absurd this (by norm_num [Complex.nonneg_iff])

end Counterexample

end MathlibExt.Analysis.CStarAlgebra.OperatorConvexSq
