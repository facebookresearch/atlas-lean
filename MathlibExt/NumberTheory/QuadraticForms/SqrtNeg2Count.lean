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

/-- **Representations by $x^2 + 2y^2$ as elements of $\mathbb{Z}[\sqrt{-2}]$.** For every natural
number $j$, the map $(x, y) \mapsto x + y\sqrt{-2}$ is a bijection from the set of integer pairs
$(x, y)$ with $x^2 + 2y^2 = j$ to the set of elements $z \in \mathbb{Z}[\sqrt{-2}]$ whose norm
$N(z)$ has absolute value $j$. -/
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

/-- **Number of representations by $x^2 + 2y^2$.** For every integer $j \ge 1$, the number of
pairs of integers $(x, y)$ with $x^2 + 2y^2 = j$ equals $2 \sum_{d \mid j} \chi(d)$, where $d$
runs over the positive divisors of $j$ and $\chi$ is the Dirichlet character modulo $8$ attached
to $\mathbb{Q}(\sqrt{-2})$: $\chi(d) = 1$ if $d \equiv 1, 3 \pmod 8$, $\chi(d) = -1$ if
$d \equiv 5, 7 \pmod 8$, and $\chi(d) = 0$ if $d$ is even. -/
public theorem x2_add_two_sq_count (j : ℕ) (hj : 1 ≤ j) :
    (Fintype.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = (j : ℤ)} : ℤ) =
      2 * ∑ d ∈ j.divisors, ZMod.χ₈' d := by
  rw [Fintype.card_congr (pairEquivSqrtNegTwoNormFiber j)]
  simpa [SumSquares.repX2Y2Count, SumSquares.divChiNeg2Sum] using
    SumSquares.x2y2_count (t := j) (by omega)

end SumSquares
