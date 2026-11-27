/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import all MathlibExt.Analysis.CatalanDigammaSeries
import MathlibExt.Analysis.HalfIntegerHarmonic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Catalan series with binomial and central binomial denominators

Specialize the Catalan digamma series to a positive half-integer. The binomial
recurrences convert its denominator, and the digamma difference reduces to
ordinary and odd harmonic numbers.

## References

* Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*,
  INTEGERS 25 (2025), Article A18, pp. 1–12, Theorem 12, identity (28); also Theorem 3,
  identity (7), Lemma 1 and identity (26). <https://math.colgate.edu/~integers/z18/z18.pdf>
* Einar Hille, *On the Logarithmic Derivatives of the Gamma Function*,
  Mathematisk-fysiske Meddelelser 8 (1927), no. 1, pp. 1–58, §2, p. 6, equation (22), citing
  N. E. Nörlund, *Vorlesungen über Differenzenrechnung*, Springer (1924), p. 251.
  This is the inverse-factorial digamma identity (2) underlying the specialization.
-/

namespace MetaMathlibExt

open tsum_catalan_div_four_pow_mul_binom

-- Both denominators grow by `2 * (2 * (n + m) + 1) / (n + 1)`.
private theorem halfInteger_catalan_denominator (m n : ℕ) :
    (4 : ℂ) ^ n * binom ((m : ℂ) - 1 / 2) n * (m.centralBinom : ℂ) =
      ((n + m).choose n : ℂ) * ((n + m).centralBinom : ℂ) := by
  induction n with
  | zero => simp [binom]
  | succ n ih =>
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hk : ((n + m : ℕ) : ℂ) + 1 ≠ 0 := by exact_mod_cast (n + m).succ_ne_zero
    have hc : (((n + m : ℕ) : ℂ) + 1) * ((n + m).choose n : ℂ) =
        ((n + 1 + m).choose (n + 1) : ℂ) * ((n : ℂ) + 1) := by
      exact_mod_cast (by simpa only [Nat.add_right_comm n m 1] using
        Nat.add_one_mul_choose_eq (n + m) n)
    have hb : (((n + m : ℕ) : ℂ) + 1) * ((n + 1 + m).centralBinom : ℂ) =
        2 * (2 * ((n + m : ℕ) : ℂ) + 1) * ((n + m).centralBinom : ℂ) := by
      exact_mod_cast (by simpa only [Nat.add_right_comm n m 1] using
        Nat.succ_mul_centralBinom_succ (n + m))
    rw [pow_succ, binom_succ]
    calc
      _ = (4 ^ n * binom ((m : ℂ) - 1 / 2) n * (m.centralBinom : ℂ)) *
          (2 * (2 * ((n + m : ℕ) : ℂ) + 1) / ((n : ℂ) + 1)) := by
        push_cast
        ring
      _ = _ := by
        rw [ih, (eq_div_iff hn).2 hc.symm, (eq_div_iff hk).2 ((mul_comm _ _).trans hb)]
        field_simp

/-- **Catalan numbers over binomial and central binomial coefficients.** Let $m$ be a positive
integer, $C_n$ the $n$th Catalan number, $H_n = \sum_{j=1}^{n} \frac{1}{j}$ the $n$th harmonic
number and $O_n = \sum_{j=1}^{n} \frac{1}{2j - 1}$. Then
$$\sum_{n=0}^{\infty} \frac{C_n}{\binom{n+m}{n} \binom{2(n+m)}{n+m}} =
\frac{m}{2} \cdot \frac{H_{m-1} - 2 O_{m-1} + 2 \log 2}{\binom{2(m-1)}{m-1}}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 12, identity (28)
(`integers-2025-A18-thm-12`). -/
public theorem tsum_catalan_div_choose_mul_centralBinom {m : ℕ} (hm : 0 < m) :
    ∑' n : ℕ, (catalan n : ℝ) / (((n + m).choose n : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 2 *
          ((harmonic (m - 1) : ℝ) - 2 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) +
            2 * Real.log 2) /
        ((m - 1).centralBinom : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_sub_one]
  let z : ℂ := (k : ℂ) + 1 / 2
  have hz : 0 < z.re := by
    have hcast : z = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) := by push_cast [z]; rfl
    rw [hcast, Complex.ofReal_re]
    positivity
  have h := tsum_catalan_div_four_pow_mul_binom hz
  change ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * binom z n) = _ at h
  have hd (n : ℕ) : (4 : ℂ) ^ n * binom z n * ((k + 1).centralBinom : ℂ) =
      ((n + (k + 1)).choose n : ℂ) * ((n + (k + 1)).centralBinom : ℂ) := by
    simpa only [show ((k + 1 : ℕ) : ℂ) - 1 / 2 = z by push_cast [z]; ring] using
      halfInteger_catalan_denominator (k + 1) n
  let A : ℝ := (harmonic k : ℝ) - 2 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℝ) + 1) + 2 * Real.log 2
  have hψ : -(Complex.digamma z - Complex.digamma (z + 1 / 2)) = (A : ℂ) := by
    have hh := (harmonic_nat_sub_half_values k).1
    rw [show z + 1 / 2 = (k : ℂ) + 1 by dsimp [z]; ring, Complex.digamma_nat_add_one]
    dsimp [A]
    push_cast
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    change Complex.digamma z + _ = _ at hh
    linear_combination -hh
  have hc (n : ℕ) : (n.centralBinom : ℂ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_pos n).ne'
  have hr : 2 * z / ((k + 1).centralBinom : ℂ) =
      ((k : ℂ) + 1) / 2 / (k.centralBinom : ℂ) := by
    have hrec : ((k : ℂ) + 1) * ((k + 1).centralBinom : ℂ) =
        2 * (2 * (k : ℂ) + 1) * (k.centralBinom : ℂ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    dsimp [z]
    field_simp [hc]
    linear_combination -hrec
  change (∑' n : ℕ, (catalan n : ℝ) / _) = (↑(k + 1 : ℕ) : ℝ) / 2 * A / _
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  push_cast
  simp_rw [← hd]
  calc
    _ = (∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * binom z n)) /
        ((k + 1).centralBinom : ℂ) := by
      rw [← tsum_div_const]
      exact tsum_congr fun n ↦ (div_div _ _ _).symm
    _ = (2 * z / ((k + 1).centralBinom : ℂ)) *
        (-(Complex.digamma z - Complex.digamma (z + 1 / 2))) := by rw [h]; ring
    _ = _ := by rw [hr, hψ]; ring

end MetaMathlibExt
