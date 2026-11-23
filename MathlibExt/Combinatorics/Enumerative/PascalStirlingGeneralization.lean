/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Factorial matrices of power series

For a formal power series `f` over a field `K` and a natural number `n`,
`MetaMathlibExt.powerSeriesFactorialMatrix f n` is the `n × n` lower triangular matrix whose entry
in row `a` and column `b` (counted from `0`) is `a! / b!` times the coefficient of `t^(a-b)` in `f`
when `b ≤ a`, and `0` otherwise. Over a field of characteristic zero it is the leading `n × n`
section of the infinite lower triangular matrix `M(f)` of Moghaddamfar, Salehy and Salehy. For
example, the factorial matrix of `exp` is the Pascal matrix, whose entries are the binomial
coefficients `a.choose b`.

## Main statements

* `MetaMathlibExt.powerSeriesFactorialMatrix_apply_self`: in characteristic zero, every diagonal
  entry is the constant coefficient of `f`.
* `MetaMathlibExt.powerSeriesFactorialMatrix_mul`: in characteristic zero,
  `M_n(f) M_n(g) = M_n(f g)`.

## Proof

The entry of `M_n(f) M_n(g)` in row `a` and column `b` is
`∑_c (a! / c!) [t^(a-c)] f · (c! / b!) [t^(c-b)] g`, and only the indices `b ≤ c ≤ a` contribute.
In characteristic zero `c! ≠ 0`, so each such term is `(a! / b!) [t^(a-c)] f · [t^(c-b)] g`, and
`c ↦ (a - c, c - b)` maps these indices bijectively onto the pairs `(i, j)` with `i + j = a - b`.
By the product formula for coefficients, the sum is `(a! / b!) [t^(a-b)] (f g)`. When `a < b` no
index contributes, and both sides are `0`.

## Implementation notes

The declarations keep the full names, statements and docstrings they had in
`WantedExt.Combinatorics.Enumerative.PascalStirlingGeneralizationWanted`, which imports this
module.

## References

* A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and Stirling
  Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4. The declaration docstrings
  give the sections and lemmas they cite.
-/

namespace MetaMathlibExt

@[expose] public section

-- `R` is not used below. It is declared as in the wanted module that these declarations come
-- from, so that `Type*` again gives `K` the universe parameter `u_2` and the moved declarations
-- keep their elaborated types and bodies.
variable {R : Type*} [CommRing R]

/-- **Factorial matrix of a power series.** Let $K$ be a field, let $f$ be a formal power series
over $K$ in the variable $t$, and let $n$ be a natural number. The factorial matrix $M_n(f)$ is
the $n \times n$ matrix over $K$ whose entry in row $a$ and column $b$ (counted from $0$) is
$(a! \cdot 1_K) / (b! \cdot 1_K)$ times the coefficient of $t^{a-b}$ in $f$ when $b \le a$, and
$0$ when $b > a$. Here the quotient is taken in $K$ and is read as $0$ when $b! \cdot 1_K = 0$,
which can happen only in positive characteristic. When $K$ has characteristic zero, the factor is
the integer $a!/b!$ and $M_n(f)$ is the leading $n \times n$ section of the infinite lower
triangular matrix $M(f)$ of Moghaddamfar, Salehy and Salehy.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
noncomputable def powerSeriesFactorialMatrix {K : Type*} [Field K] (f : PowerSeries K) (n : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if (b : ℕ) ≤ a then
      ((a : ℕ).factorial : K) / ((b : ℕ).factorial : K) * PowerSeries.coeff ((a : ℕ) - b) f
    else 0

/-- **Diagonal of the factorial matrix of a power series.** Let $K$ be a field of characteristic
zero, let $f$ be a formal power series over $K$ and let $n \ge 0$. Every diagonal entry of the
leading $n \times n$ section of $M(f)$, the lower triangular matrix whose $(a, b)$ entry, with rows
and columns indexed from $0$, is $\frac{a!}{b!} [t^{a-b}] f$ for $b \le a$ and $0$ for $b > a$,
equals the constant coefficient $[t^0] f$ of $f$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
theorem powerSeriesFactorialMatrix_apply_self {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (n : ℕ) (a : Fin n) :
    powerSeriesFactorialMatrix f n a a = PowerSeries.coeff 0 f := by
  have h : ((a : ℕ).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp [powerSeriesFactorialMatrix, h]

/-- **Multiplicativity of the factorial matrix of a power series.** Let $K$ be a field of
characteristic zero, let $f$ and $g$ be formal power series over $K$ in the variable $t$, and let
$n$ be a natural number. For a power series $h$ over $K$, write $M_n(h)$ for the $n \times n$
factorial matrix of $h$, whose entry in row $a$ and column $b$ (counted from $0$) is
$\frac{a!}{b!}$ times the coefficient of $t^{a-b}$ in $h$ when $b \le a$, and $0$ otherwise. Then
$M_n(f) M_n(g) = M_n(fg)$.

Since these matrices are lower triangular and $M_n(h)$ is the leading $n \times n$ section of the
infinite matrix $M(h)$, this is equivalent to $M(f) M(g) = M(fg)$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 5
(`jis-2026-26.5.4-lem-5`). -/
theorem powerSeriesFactorialMatrix_mul {K : Type*} [Field K] [CharZero K]
    (f g : PowerSeries K) (n : ℕ) :
    powerSeriesFactorialMatrix f n * powerSeriesFactorialMatrix g n =
      powerSeriesFactorialMatrix (f * g) n := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp only [powerSeriesFactorialMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun c =>
    (if c ≤ a then (a.factorial : K) / (c.factorial : K) * PowerSeries.coeff (a - c) f else 0) *
      if b ≤ c then (c.factorial : K) / (b.factorial : K) * PowerSeries.coeff (c - b) g else 0) n]
  split_ifs with hba
  · -- Only the indices `b ≤ c ≤ a` contribute; they correspond to the antidiagonal of `a - b`.
    have hsub : Finset.Icc b a ⊆ Finset.range n := fun c hc => by
      simp only [Finset.mem_Icc, Finset.mem_range] at hc ⊢
      omega
    rw [← Finset.sum_subset hsub fun c _ hc => by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hc
      rcases hc with hc | hc
      · rw [ite_eq_right (show ¬b ≤ c by omega), mul_zero]
      · rw [ite_eq_right (show ¬c ≤ a by omega), zero_mul]]
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_nbij' (fun c => (a - c, c - b)) (fun p => b + p.2) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_Icc] at hc
      simp only [Finset.mem_antidiagonal]
      omega
    · intro p hp
      simp only [Finset.mem_antidiagonal] at hp
      simp only [Finset.mem_Icc]
      omega
    · intro c hc
      simp only [Finset.mem_Icc] at hc
      omega
    · intro p hp
      simp only [Finset.mem_antidiagonal] at hp
      ext <;> simp only <;> omega
    · intro c hc
      simp only [Finset.mem_Icc] at hc
      have hc0 : (c.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero c)
      rw [ite_eq_left hc.2, ite_eq_left hc.1, mul_mul_mul_comm, div_mul_div_cancel₀ hc0]
  · -- No index `c` satisfies `b ≤ c ≤ a`.
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h1 h2
    · exact absurd (h2.trans h1) hba
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]

end

end MetaMathlibExt
