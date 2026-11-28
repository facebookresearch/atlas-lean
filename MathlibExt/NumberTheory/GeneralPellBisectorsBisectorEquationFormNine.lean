/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NegativePellDivisibility
import Mathlib.Tactic.LinearCombination

/-!
# Bisector-equation solutions from the negative Pell sequences

Let `d > 1` be a natural number for which `x² - d y² = -1` has an integer solution. Write
`fₖ, gₖ` for the coordinates of the `k`-th power of its least positive solution, ordered by the
second coordinate. For positive natural numbers `m, n`, set `r = 2m - 1` and `k = r * 2n`.
Then `gᵣ` divides `gₖ`, and `(f_{k-r}, f_{k+r}, gₖ / gᵣ)` satisfies the bisector equation.
The argument uses integer coordinate identities, so `d` need not be square-free.

## References

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
  Rational Slopes*, INTEGERS 24 (2024), Article A111, pp. 1–26, Theorem 3, converse for
  Form (9), and §6. The proof uses Proposition 5, equation (24), Proposition 6(a), equations
  (27) and (28), and Theorem 11(d).
- Thomas Koshy, *Pell and Pell–Lucas Numbers with Applications*, Springer, 2014, §2.4 and
  Theorem 8.4, cited by Hirotsu for the norm and divisibility properties.
- Paulo Ribenboim, *The New Book of Prime Number Records*, Springer, 1996, Chapter 2, IV,
  cited by Hirotsu for the more general Lucas-sequence addition formulas.
- R. D. Carmichael, *On the Numerical Factors of the Arithmetic Forms* $\alpha^n \pm \beta^n$,
  Annals of Mathematics (2) 15 (1913–1914), pp. 30–48, Theorem IV, cited by Hirotsu for
  the divisibility of the second coordinates.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Bisector-equation solutions from the negative Pell sequences.** Let $d > 1$ be a natural
number such that $x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its solution in
positive integers with $Y$ least, and define integers $f_k$ and $g_k$ by
$f_k + g_k \sqrt{d} = (X + Y \sqrt{d})^k$ for natural numbers $k$. Let $m, n > 0$ be natural
numbers and put $a = f_{(2m-1)(2n-1)}$, $b = f_{(2m-1)(2n+1)}$ and
$c = g_{(2m-1) 2n} / g_{2m-1}$. Then $g_{2m-1}$ divides $g_{(2m-1) 2n}$, so $c$ is an integer, and
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$

Source: converse of Theorem 3 for Form (9); the square-freeness of $d$ is not needed here.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (9)
(`integers-2024-A111-thm-3`). -/
public theorem bisector_equation_form_nine (d m n : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (hm : 0 < m) (hn : 0 < n) :
    let a := negPellF d ((2 * m - 1) * (2 * n - 1))
    let b := negPellF d ((2 * m - 1) * (2 * n + 1))
    let c := negPellG d ((2 * m - 1) * (2 * n)) / negPellG d (2 * m - 1)
    negPellG d (2 * m - 1) ∣ negPellG d ((2 * m - 1) * (2 * n)) ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := by
  let f := negPellF d
  let g := negPellG d
  let r := 2 * m - 1
  let i := r * (2 * n - 1)
  let k := r * (2 * n)
  let j := r * (2 * n + 1)
  let c := g k / g r
  change g r ∣ g k ∧ (f i - c) ^ 2 * (f j ^ 2 + 1) = (f j - c) ^ 2 * (f i ^ 2 + 1)
  have hr : 0 < r := by dsimp [r]; omega
  have hrk : r ≤ k := by simpa [k] using Nat.mul_le_mul_left r (show 1 ≤ 2 * n by omega)
  have hdvd : g r ∣ g k := (negPellG_dvd_iff d hd hneg k r hr hrk).2 (dvd_mul_right r _)
  refine ⟨hdvd, ?_⟩
  have hoddR : Odd r := ⟨m - 1, by dsimp [r]; omega⟩
  have hoddI : Odd i := hoddR.mul ⟨n - 1, by omega⟩
  have hoddJ : Odd j := hoddR.mul ⟨n, rfl⟩
  have hnorm (t : ℕ) (ht : Odd t) : f t ^ 2 + 1 = (d : ℤ) * g t ^ 2 := by
    have h := negPell_norm_of_solvable d hd hneg t
    rw [ht.neg_one_pow] at h
    change f t ^ 2 - (d : ℤ) * g t ^ 2 = -1 at h
    linear_combination h
  have hg : g r ≠ 0 := by
    intro hzero
    have h := hnorm r hoddR
    simp [hzero] at h
    have := sq_nonneg (f r)
    omega
  have hquot : g r * c = g k := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdvd
  have hik : i + r = k := by
    simpa only [i, k, Nat.mul_succ] using
      congrArg (r * ·) (show (2 * n - 1).succ = 2 * n by omega)
  have hkj : k + r = j := (Nat.mul_succ r (2 * n)).symm
  have hleft : g r * (f i - c) = -(f r * g i) := by
    have h : g k = f i * g r + g i * f r := hik ▸ (negPell_add d i r).2
    linear_combination -h - hquot
  -- The norm at `r` is `-1`, so its inverse has coordinates `(-f r, g r)`.
  have hright : g r * (f j - c) = f r * g j := by
    have h₁ : f j = f k * f r + (d : ℤ) * g k * g r := hkj ▸ (negPell_add d k r).1
    have h₂ : g j = f k * g r + g k * f r := hkj ▸ (negPell_add d k r).2
    linear_combination g r * h₁ - f r * h₂ - g k * hnorm r hoddR - hquot
  have hcross : (f i - c) * g j = -((f j - c) * g i) := by
    apply mul_left_cancel₀ hg
    linear_combination g j * hleft + g i * hright
  rw [hnorm j hoddJ, hnorm i hoddI]
  calc
    _ = (d : ℤ) * ((f i - c) * g j) ^ 2 := by ring
    _ = (d : ℤ) * ((f j - c) * g i) ^ 2 := by rw [hcross, neg_sq]
    _ = _ := by ring

end MetaMathlibExt
