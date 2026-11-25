/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Weighted sums of Dirichlet convolutions

Möbius inversion expresses a weighted sum of a Dirichlet convolution as a sum over multiples.
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- **Möbius expansion of weighted sums of a Dirichlet convolution.** Let $w$, $u$ and $v$ be
arithmetic functions with complex values, let $*$ denote Dirichlet convolution, let $\mu$ be the
Möbius function and put $g = w * \mu$. Then for every real $x$,
$$
\sum_{1 \le j \le x} w(j)\, (u * v)(j) =
\sum_{1 \le r \le x} g(r) \sum_{1 \le j \le x/r} (u * v)(rj),
$$
where $j$ and $r$ run over positive integers.

Both sides vanish for $x < 1$; the source assumes $x \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 4 (`integers-2024-A75-lem-4`). -/
public theorem sum_mul_dirichletConvolution_eq_sum_moebius (w u v : ArithmeticFunction ℂ)
    (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, w j * (u * v) j =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
        ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j) := by
  let g := w * (μ : ArithmeticFunction ℂ)
  let N := ⌊x⌋₊
  have hw (n : ℕ) : w n = ∑ r ∈ n.divisors, g r := by
    rw [← coe_mul_zeta_apply]
    simp [g, mul_assoc]
  simp_rw [Nat.floor_div_natCast]
  change ∑ n ∈ Icc 1 N, w n * (u * v) n =
    ∑ r ∈ Icc 1 N, g r * ∑ j ∈ Icc 1 (N / r), (u * v) (r * j)
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ r ∈ n.divisors, g r * (u * v) n := by
      exact sum_congr rfl fun n _ ↦ by rw [hw, sum_mul]
    _ = ∑ r ∈ Icc 1 N, ∑ n ∈ Icc 1 N with r ∣ n, g r * (u * v) n := by
      apply sum_comm'
      intro n r
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨hn, hd, -⟩
        exact ⟨⟨hn, hd⟩, Nat.pos_of_dvd_of_pos hd hn.1, (Nat.le_of_dvd hn.1 hd).trans hn.2⟩
      · rintro ⟨⟨hn, hd⟩, -⟩
        exact ⟨hn, hd, Nat.ne_of_gt hn.1⟩
    _ = _ := by
      refine sum_congr rfl fun r hr ↦ ?_
      have hr₀ : 0 < r := (mem_Icc.mp hr).1
      rw [← mul_sum]
      congr 1
      symm
      apply sum_nbij (r * ·)
      · intro j hj
        obtain ⟨hj₀, hjN⟩ := mem_Icc.mp hj
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hr₀ hj₀,
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr₀).mp hjN⟩, dvd_mul_right r j⟩
      · exact (mul_right_injective₀ hr₀.ne').injOn
      · intro n hn
        obtain ⟨hn, j, rfl⟩ := mem_filter.mp hn
        obtain ⟨hpos, hle⟩ := mem_Icc.mp hn
        refine ⟨j, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hpos, ?_⟩, rfl⟩
        exact (Nat.le_div_iff_mul_le hr₀).mpr (Nat.mul_comm _ _ ▸ hle)
      · exact fun _ _ ↦ rfl

end MetaMathlibExt
