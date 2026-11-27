/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Divisibility of the polynomial parts in Wolstenholme's theorem

The polynomial parts of Kehila's binomial congruence coefficients have the factor
`k(n-k)/2` over the rationals.
-/

namespace MetaMathlibExt

open Polynomial

namespace exists_polynomial_part_eq_mul_half_mul

private noncomputable def choosePolynomial (m : ℕ) : ℚ[X] :=
  C ((m.factorial : ℚ)⁻¹) * descPochhammer ℚ m

private theorem eval_choosePolynomial (m : ℕ) (x : ℤ) :
    (choosePolynomial m).eval (x : ℚ) = (Ring.choose x m : ℤ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (Ring.descPochhammer_eq_factorial_smul_choose x m)
  simp only [← eval_eq_smeval, descPochhammer_eval_cast, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at h
  simp [choosePolynomial, h, Nat.factorial_ne_zero]

-- Factoring twice after subtracting the constant and linear terms also handles `a = 0`.
private theorem symmetric_eval (p : ℚ[X]) (a : ℚ) :
    ∃ q : ℚ[X], ∀ x : ℚ,
      p.eval x + p.eval (a - x) - (p.eval 0 + p.eval a) =
        x * (a - x) / 2 * q.eval x := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := p) (a := (0 : ℚ))
  obtain ⟨r, hr⟩ := X_sub_C_dvd_sub_C_eval (p := g) (a := a)
  have hp (x : ℚ) : p.eval x - p.eval 0 = x * g.eval x := by
    simpa using congrArg (eval x) hg
  have hg' (x : ℚ) : g.eval x - g.eval a = (x - a) * r.eval x := by
    simpa using congrArg (eval x) hr
  refine ⟨C (-2) * (r + r.comp (C a - X)), fun x => ?_⟩
  simp only [eval_mul, eval_C, eval_add, eval_comp, eval_sub, eval_X]
  calc
    _ = x * (g.eval x - g.eval a) + (a - x) * (g.eval (a - x) - g.eval a) := by
      linear_combination hp x + hp (a - x) - hp a
    _ = _ := by rw [hg' x, hg' (a - x)]; ring

end exists_polynomial_part_eq_mul_half_mul

open exists_polynomial_part_eq_mul_half_mul in
/-- **Divisibility of the polynomial parts by $k(n-k)/2$.** Let $m$ be a natural number and $n$ an
integer. For an integer $x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$,
and for a rational number $x$ write $(x)_r = x(x-1)\cdots(x-r+1)$ for the falling factorial. Then
there is a polynomial $Q \in \mathbb{Q}[X]$ such that for every natural number $k$
$$\binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1 = \frac{k(n-k)}{2} \, Q(k),$$
and for all natural numbers $i$ and $j$ with $1 \le i < j$ there is a polynomial
$Q \in \mathbb{Q}[X]$ such that for every natural number $k$
$$\frac{(n-k)_{j-i} \, (k)_i + (n-k)_i \, (k)_{j-i}}{j!} \binom{m-n}{\max(m-j, 0)} =
\frac{k(n-k)}{2} \, Q(k).$$

For $j \le m$ the left-hand sides are the polynomial parts of the coefficients
$C'_{00}(m, n, k)$ and $C'_{ji}(m, n, k)$ of Theorem 4 (the halving at $j = 2i$ does not affect
divisibility); agreement at every natural number $k$ amounts to divisibility by $k(n-k)/2$
in $\mathbb{Q}[k]$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 1
(`integers-2026-A32-prop-1`). -/
public theorem exists_polynomial_part_eq_mul_half_mul (m : ℕ) (n : ℤ) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let ff : ℚ → ℕ → ℚ := fun x i => ∏ t ∈ Finset.range i, (x - t)
    (∃ Q : ℚ[X], ∀ k : ℕ,
        C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1 =
          (k : ℚ) * (n - k) / 2 * Q.eval (k : ℚ)) ∧
      ∀ j i : ℕ, 1 ≤ i → i < j → ∃ Q : ℚ[X], ∀ k : ℕ,
        (ff ((n : ℚ) - k) (j - i) * ff k i + ff ((n : ℚ) - k) i * ff k (j - i)) / j.factorial *
            C ((m : ℤ) - n) (m - j) =
          (k : ℚ) * (n - k) / 2 * Q.eval (k : ℚ) := by
  dsimp only
  constructor
  · let p := (choosePolynomial m).comp (C (m : ℚ) - X)
    have heval (x : ℤ) : p.eval (x : ℚ) = (Ring.choose ((m : ℤ) - x) m : ℤ) := by
      simpa [p, eval_comp] using eval_choosePolynomial m ((m : ℤ) - x)
    have hzero : p.eval 0 = 1 := by
      simpa [Ring.choose_natCast] using heval 0
    have hn : p.eval (n : ℚ) = (-1 : ℚ) ^ m * ((Ring.choose (n - 1) m : ℤ) : ℚ) := by
      rw [heval, show (m : ℤ) - n = -(n - m) by ring, Ring.choose_neg,
        show n - m + m - 1 = n - 1 by ring]
      simp only [Units.smul_def, zsmul_eq_mul, Int.coe_negOnePow_natCast,
        Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    obtain ⟨Q, hQ⟩ := symmetric_eval p (n : ℚ)
    refine ⟨Q, fun k => ?_⟩
    have hk : p.eval (k : ℚ) = (Ring.choose ((m : ℤ) - k) m : ℤ) := by
      simpa using heval (k : ℤ)
    have hnk : p.eval ((n : ℚ) - k) = (Ring.choose ((k : ℤ) + m - n) m : ℤ) := by
      simpa [show (m : ℤ) - (n - k) = (k : ℤ) + m - n by ring] using heval (n - k)
    rw [← hQ, hk, hnk, hzero, hn]
    ring
  · intro j i hi hij
    let A (r : ℕ) := (descPochhammer ℚ (r - 1)).comp (X - 1)
    have heval (r : ℕ) (hr : 1 ≤ r) (x : ℚ) :
        (∏ t ∈ Finset.range r, (x - t)) = x * (A r).eval x := by
      rw [← descPochhammer_eval_eq_prod_range]
      conv_lhs => rw [← Nat.sub_add_cancel hr, descPochhammer_succ_left, eval_mul, eval_X]
    let s := ((Ring.choose ((m : ℤ) - n) (m - j) : ℤ) : ℚ) / j.factorial
    let Y := C (n : ℚ) - X
    refine ⟨C (2 * s) * ((A (j - i)).comp Y * A i + (A i).comp Y * A (j - i)), fun k => ?_⟩
    simp only [heval i hi, heval (j - i) (by omega), eval_mul, eval_C, eval_add, eval_comp,
      Y, eval_sub, eval_X, s]
    ring

end MetaMathlibExt
