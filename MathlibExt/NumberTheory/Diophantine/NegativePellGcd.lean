/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralPellBisectors

/-!
# Coprimality of the negative Pell sequences

Let $d > 1$ be such that $x^2 - d y^2 = -1$ is solvable in integers, let $(X, Y)$ be its
fundamental solution, and write $(X + Y\sqrt d)^n = f_n + g_n \sqrt d$. Since the norm of
$X + Y \sqrt d$ is $-1$, taking norms gives $f_n^2 - d g_n^2 = (-1)^n$. A common divisor of
$d$ and $f_n$, or of $f_n$ and $g_n$, therefore divides $(-1)^n$, so both greatest common
divisors equal $1$.

This follows Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines
with Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(a).
-/

@[expose] public section

namespace MetaMathlibExt

namespace negPell_gcd_eq_one

/-- An integral solution of `x² - d y² = -1` gives the fundamental solution. -/
private theorem fund {d : ℕ} (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) :
    negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  obtain ⟨x, y, hxy⟩ := hneg
  have hy0 : y ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg x]
  have hnat : (x.natAbs : ℤ) ^ 2 + 1 = (d : ℤ) * (y.natAbs : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
    linarith
  have hnat' : x.natAbs ^ 2 + 1 = d * y.natAbs ^ 2 := by exact_mod_cast hnat
  exact (negPellFund_spec ⟨y.natAbs, Int.natAbs_pos.mpr hy0, x.natAbs, hnat'⟩).2

/-- The norm identity `f_n² - d g_n² = (-1)^n`. -/
private theorem norm {d : ℕ}
    (hX : negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2) (n : ℕ) :
    negPellF d n ^ 2 - d * negPellG d n ^ 2 = (-1) ^ n := by
  set ε : ℤ√(d : ℤ) := ⟨negPellFundX d, negPellFundY d⟩ with hε
  have hnormε : ε.norm = -1 := by
    rw [hε, Zsqrtd.norm_def]
    have hcast : (negPellFundX d : ℤ) ^ 2 + 1 = (d : ℤ) * (negPellFundY d : ℤ) ^ 2 := by
      exact_mod_cast hX
    push_cast
    linarith
  have hpow : ∀ m : ℕ, (ε ^ m).norm = (-1 : ℤ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Zsqrtd.norm_mul, ih, hnormε, pow_succ]
  have h := hpow n
  rw [Zsqrtd.norm_def] at h
  simp only [negPellF, negPellG, hε] at h ⊢
  rw [← h]
  ring

/-- An integer dividing `(-1)^n` is a unit, so a gcd dividing it is `1`. -/
private theorem gcd_eq_one_of_dvd {a b : ℤ} {n : ℕ}
    (h : (Int.gcd a b : ℤ) ∣ (-1) ^ n) : Int.gcd a b = 1 := by
  have h1 : (Int.gcd a b : ℤ) ∣ 1 := by
    rcases neg_one_pow_eq_or ℤ n with h' | h' <;> rw [h'] at h
    · exact h
    · exact (dvd_neg).mp h
  exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg _) h1

end negPell_gcd_eq_one

-- Once `x² - d y² = -1` is solvable, the norm identity gives both equalities for every `d` and
-- every `n`, so the hypotheses `1 < d` and `0 < n` of the statement are not used by the proof.
set_option linter.unusedVariables false in
/-- **Coprimality of the negative Pell sequences.** Let $d > 1$ be a natural number such that
$x^2 - d y^2 = -1$ has an integral solution, let $(X, Y)$ be its solution in natural numbers with
least positive $Y$, and define integers $f_n, g_n$ by $(X + Y\sqrt{d})^n = f_n + g_n\sqrt{d}$.
Then for every $n > 0$, $\gcd(d, f_n) = 1$ and $\gcd(f_n, g_n) = 1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(a) (`integers-2024-A111-thm-11`). -/
theorem negPell_gcd_eq_one (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) (hn : 0 < n) :
    Int.gcd d (negPellF d n) = 1 ∧ Int.gcd (negPellF d n) (negPellG d n) = 1 := by
  have hnorm := negPell_gcd_eq_one.norm (negPell_gcd_eq_one.fund hneg) n
  refine ⟨negPell_gcd_eq_one.gcd_eq_one_of_dvd (n := n) ?_,
    negPell_gcd_eq_one.gcd_eq_one_of_dvd (n := n) ?_⟩
  · rw [← hnorm]
    exact dvd_sub (dvd_pow (Int.gcd_dvd_right _ _) two_ne_zero)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _)
  · rw [← hnorm]
    exact dvd_sub (dvd_pow (Int.gcd_dvd_left _ _) two_ne_zero)
      (dvd_mul_of_dvd_right (dvd_pow (Int.gcd_dvd_right _ _) two_ne_zero) _)

end MetaMathlibExt
