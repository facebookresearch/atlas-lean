/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK
import MathlibExt.Combinatorics.Enumerative.TrudiFussCatalan

/-!
# Toeplitz–Hessenberg determinants of Fuss–Catalan numbers

Trudi's formula reduces the determinant with superdiagonal entries $1$ to a signed partition
sum of generalized Fuss–Catalan numbers.
-/

namespace MetaMathlibExt

/-- **Toeplitz–Hessenberg determinants of Fuss–Catalan numbers.** Write
$\det(a_0; a_1, \dots, a_n)$ for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix
whose entry in row $i$ and column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the
superdiagonal. For natural numbers $p, r, n$ let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$
be the generalized Fuss–Catalan number, taken to be $0$ when $pn + r = 0$. Then for all natural
numbers $p, r$ and every $n \ge 1$,
$$\det(1; A_1(p, r), \dots, A_n(p, r)) = (-1)^{n-1} \frac{r}{n} \binom{pn - r - 1}{n - 1}$$
in $\mathbb{Q}$, where the binomial coefficient has an integer, possibly negative, upper index:
$\binom{x}{k} = x (x - 1) \cdots (x - k + 1)/k!$.

This includes $p = r = 0$, which the paper's standing assumption excludes; there every entry
$A_i(0, 0)$ is $0$ and both sides vanish.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 3
(`jis-2026-26.1.2-thm-3`). -/
public theorem toeplitzHessenbergDet_fussCatalan (p r n : ℕ) (hn : 1 ≤ n) :
    toeplitzHessenbergDet
        (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) n =
      (-1) ^ (n - 1) * (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ) := by
  rw [toeplitzHessenbergDet_eq_neg_one_pow_mul_trudiPartitionSum _ (by simp)]
  -- Every block of a composition has positive size, so the value at zero is immaterial.
  have hsum : trudiPartitionSum (-1 : ℚ)
      (fun i => if i = 0 then 1 else (generalizedFussCatalanNumber p i r : ℚ)) n =
      trudiPartitionSum (-1 : ℚ) (fun i => (generalizedFussCatalanNumber p i r : ℚ)) n := by
    simp only [trudiPartitionSum_eq_sum_compositions]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ite_eq_right (c.blocks_pos (c.blocksFun_mem_blocks j)).ne']
  have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  have hsign : (-1 : ℚ) ^ n = (-1) ^ (n - 1) * (-1) := by
    rw [← pow_succ, ← hn']
  rw [hsum, hsign, mul_assoc, neg_one_mul, trudiPartitionSum_fussCatalan.1 p r n hn,
    ← mul_assoc, ← mul_div_assoc]

end MetaMathlibExt
