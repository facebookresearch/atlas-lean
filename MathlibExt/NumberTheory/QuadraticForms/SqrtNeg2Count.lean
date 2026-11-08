/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.X2Y2Count

@[expose] public section

namespace SumSquares

local notation "ℤ√-2" => Zsqrtd (-2 : ℤ)

private theorem sqrtNegTwoNorm (z : ℤ√-2) :
    Zsqrtd.norm z = z.re ^ 2 + 2 * z.im ^ 2 := by
  rw [Zsqrtd.norm_def]
  ring

/-- Integer pairs representing `j` by `x² + 2y²` correspond to elements of
`ℤ[√-2]` of norm `j`. -/
public def pairEquivSqrtNegTwoNormFiber (j : ℕ) :
    {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = (j : ℤ)} ≃
      {z : ℤ√-2 // (Zsqrtd.norm z).natAbs = j} where
  toFun p := ⟨⟨p.1.1, p.1.2⟩, by
    rw [sqrtNegTwoNorm, p.2, Int.natAbs_natCast]⟩
  invFun z := ⟨(z.1.re, z.1.im), by
    have hnonneg : 0 ≤ Zsqrtd.norm z.1 := Zsqrtd.norm_nonneg (by norm_num) z.1
    have hnorm : Zsqrtd.norm z.1 = (j : ℤ) := by
      rw [← Int.natAbs_of_nonneg hnonneg, z.2]
    rwa [sqrtNegTwoNorm] at hnorm⟩
  left_inv p := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

noncomputable instance pairX2Y2Fintype (j : ℕ) :
    Fintype {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = (j : ℤ)} :=
  Fintype.ofEquiv _ (pairEquivSqrtNegTwoNormFiber j).symm

/-- The number of representations of `j ≥ 1` by `x² + 2y²` equals twice
the divisor sum of the canonical character `ZMod.χ₈'`. -/
public theorem x2_add_two_sq_count (j : ℕ) (hj : 1 ≤ j) :
    (Fintype.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = (j : ℤ)} : ℤ) =
      2 * ∑ d ∈ j.divisors, ZMod.χ₈' d := by
  rw [Fintype.card_congr (pairEquivSqrtNegTwoNormFiber j)]
  simpa [SumSquares.repX2Y2Count, SumSquares.divChiNeg2Sum] using
    SumSquares.x2y2_count (t := j) (by omega)

end SumSquares
