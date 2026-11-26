/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoP

/-!
# Stride sums of generalized Leonardo `p`-numbers

The generalized Leonardo numbers along a stride of length `p + 1` sum to a shifted
endpoint value with a correction from the initial terms and the constant in the recurrence.
-/

public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

-- The statement retains both positivity hypotheses from the source.
set_option linter.unusedVariables false in
/-- **Stride sums of the generalized Leonardo $p$-numbers.** Let $p \ge 1$ and $k \ge 1$ be
natural numbers, and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(j) = 1$ for $0 \le j \le p$ and
$\mathcal{L}_{p,k}(j) = \mathcal{L}_{p,k}(j-1) + \mathcal{L}_{p,k}(j-p-1) + k$ for $j > p$).
Then for all natural numbers $m \le p$ and $n$, the sum
$S = \sum_{i=0}^{n} \mathcal{L}_{p,k}((p+1)i + m)$ satisfies
$S = \mathcal{L}_{p,k}((p+1)n + m + 1) - kn$ if $m < p$, and
$S = \mathcal{L}_{p,k}((p+1)(n+1)) - k(n+1) - 1$ if $m = p$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 4. -/
theorem sum_leonardoPK_stride (p k m n : ℕ)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hm : m ≤ p) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k ((p + 1) * i + m) =
      if m < p then
        leonardoPK p k ((p + 1) * n + m + 1) - (k : ℤ) * n
      else
        leonardoPK p k ((p + 1) * (n + 1)) - (k : ℤ) * (n + 1) - 1 := by
  let f (i : ℕ) := leonardoPK p k ((p + 1) * i + m + 1)
  have diff (i : ℕ) : f (i + 1) - f i =
      leonardoPK p k ((p + 1) * (i + 1) + m) + k := by
    have hidx : (p + 1) * (i + 1) + m = p + ((p + 1) * i + m + 1) := by
      rw [Nat.mul_succ]
      omega
    dsimp [f]
    rw [hidx, leonardoPK_recurrence]
    omega
  have hs := Finset.sum_range_sub f n
  simp only [diff, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_comm (n : ℤ)] at hs
  rw [Finset.sum_range_succ', Nat.mul_zero, Nat.zero_add, leonardoPK_of_le p k m hm]
  by_cases hmp : m < p
  · have hzero : f 0 = 1 := by
      simpa [f] using leonardoPK_of_le p k (m + 1) (by omega)
    rw [hzero] at hs
    dsimp [f] at hs
    rw [ite_eq_left hmp]
    omega
  · have hmp' : m = p := by omega
    subst m
    have hzero : f 0 = 1 + 1 + (k : ℤ) := by
      simpa [f, leonardoPK_of_le p k p le_rfl, leonardoPK_of_le p k 0 (Nat.zero_le p)] using
        leonardoPK_recurrence p k 0
    have hend : (p + 1) * n + p + 1 = (p + 1) * (n + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [hzero] at hs
    dsimp [f] at hs
    rw [hend] at hs
    rw [ite_eq_right hmp, mul_add (k : ℤ), mul_one]
    omega

end MathlibExt.NumberTheory.LeonardoPWanted
