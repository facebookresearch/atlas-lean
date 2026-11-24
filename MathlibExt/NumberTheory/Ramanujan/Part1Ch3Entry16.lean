/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry12

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 16(a)

Recurrence relating varphi(r,n) to varphi(r+1,n) and varphi(r+1,n+1).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16

noncomputable def varphi (a x : ℂ) (s : ℤ) (m : ℂ) : ℂ :=
  Entry12.F s m a * Complex.exp (-m * Complex.log x)

/-- **Ramanujan's three-term recurrence (Chapter 3, Entry 16(a)).** Let $a$, $x$, $n$ be complex
numbers and $r$ an integer, where $x \ne 0$ and $x = a \log x$ with $\log$ the principal branch of
the complex logarithm. Suppose that $|a| > e$, or that $a = e$ and $r \le -2$, and that
$n + k \ne 0$ for every natural number $k$ with $r + k < 0$. For an integer $s$ and a complex
number $m$ put
$$\varphi(s, m) = e^{-m \log x} \sum_{k=0}^{\infty} \frac{(m + k)^{s + k}}{a^k\, k!};$$
the three series used below converge absolutely under these hypotheses. Then
$$n\, \varphi(r, n) = \varphi(r + 1, n) - \log x \cdot \varphi(r + 1, n + 1).$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1) printed p. 66 /
    PDF p. 76, Entry 12 p. 67 / PDF p. 77, and Entry 16(a) p. 78 / PDF p. 88.
Proves `Wanted` entry `ramanujan_part1_ch3_entry16`. The series is `Entry12.F`, and the
recurrence is `Entry12.ramanujan_part1_ch3_entry12` multiplied by `exp (-n * log x)`.
-/
theorem ramanujan_part1_ch3_entry16 (a x n : ℂ)
    (r : ℤ)
        (hx_ne : x ≠ 0)
            (hx_eq : x = a * Complex.log x)
                (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
                    (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
    n * varphi a x r n = varphi a x (r + 1) n - Complex.log x * varphi a x (r + 1) (n + 1) := by
  have hkey : n * Entry12.F r n a
      = Entry12.F (r + 1) n a - a⁻¹ * Entry12.F (r + 1) (n + 1) a := by
    rw [Entry12.ramanujan_part1_ch3_entry12 r n a ha hn, one_div]
    ring
  -- Exponential identity
  set L : ℂ := Complex.log x with hL
  have hE1 : a * L = Complex.exp L := by
    rw [Complex.exp_log hx_ne]
    exact hx_eq.symm
  have hexp : Complex.exp L * Complex.exp (-L) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hainv : a⁻¹ = L * Complex.exp (-L) := by
    apply inv_eq_of_mul_eq_one_right
    calc a * (L * Complex.exp (-L)) = (a * L) * Complex.exp (-L) := by ring
      _ = Complex.exp L * Complex.exp (-L) := by rw [hE1]
      _ = 1 := hexp
  have hE2 : Complex.exp (-(n + 1) * L) = Complex.exp (-L) * Complex.exp (-n * L) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hE : a⁻¹ * Complex.exp (-n * L) = L * Complex.exp (-(n + 1) * L) := by
    rw [hainv, hE2]
    ring
  have hfin : a⁻¹ * Entry12.F (r + 1) (n + 1) a * Complex.exp (-n * L)
      = L * (Entry12.F (r + 1) (n + 1) a * Complex.exp (-(n + 1) * L)) := by
    rw [mul_right_comm, hE]
    ring
  -- Assemble
  unfold varphi
  conv_lhs => rw [← mul_assoc]
  rw [hkey, sub_mul, hfin]

end Entry16

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
