/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularAdditiveUniqueness

/-!
# Small squares under square–triangular additivity

The triangular number factors into two coprime factors by dividing its even factor by two.
The square–triangular identity then relates consecutive squares.
-/

namespace MetaMathlibExt

open ArithmeticFunction

private theorem map_triangular_of_eq_on_prefix (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (N : ℕ) (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ N - 1 → f n = n)
    (v : ℕ) (hv : 0 < v) (hvN : v ≤ N - 2) :
    f (v * (v + 1) / 2) = ↑(v * (v + 1) / 2) := by
  have hcop : v.Coprime (v + 1) := by
    rw [Nat.coprime_self_add_right]
    simp
  rcases Nat.mod_two_eq_zero_or_one v with he | ho
  · have hsplit : v = 2 * (v / 2) := by omega
    have hmul : v * (v + 1) = 2 * ((v / 2) * (v + 1)) := calc
      _ = (2 * (v / 2)) * (v + 1) := congrArg (· * (v + 1)) hsplit
      _ = _ := by ring
    have htri : v * (v + 1) / 2 = (v / 2) * (v + 1) := by omega
    have hdiv : v / 2 ∣ v := ⟨2, by omega⟩
    rw [htri, hf.map_mul_of_coprime (Nat.Coprime.of_dvd_left hdiv hcop),
      hlt (v / 2) (by omega) (by omega), hlt (v + 1) (by omega) (by omega), Nat.cast_mul]
  · have hsplit : v + 1 = 2 * ((v + 1) / 2) := by omega
    have hmul : v * (v + 1) = 2 * (v * ((v + 1) / 2)) := calc
      _ = v * (2 * ((v + 1) / 2)) := congrArg (v * ·) hsplit
      _ = _ := by ring
    have htri : v * (v + 1) / 2 = v * ((v + 1) / 2) := by omega
    have hdiv : (v + 1) / 2 ∣ v + 1 := ⟨2, by omega⟩
    rw [htri, hf.map_mul_of_coprime (Nat.Coprime.of_dvd_right hdiv hcop),
      hlt v (by omega) (by omega), hlt ((v + 1) / 2) (by omega) (by omega), Nat.cast_mul]

/-- **Square–triangular additivity fixes small squares.** Let $t_v = v(v + 1)/2$ denote the
$v$-th triangular number, and let $f$ be a complex-valued multiplicative arithmetic function
with $f(u^2 + t_v) = f(u^2) + f(t_v)$ for all positive integers $u$ and $v$. Let $N \ge 3$ be an
integer such that $f(n) = n$ for every integer $n$ with $1 \le n \le N - 1$. Then
$f(m^2) = m^2$ for every integer $m$ with $1 \le m \le N - 2$.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 2 (`integers-2026-A103-lem-2`). -/
public theorem multiplicative_sq_triangular_additive_sq
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))
    (N : ℕ) (hN : 3 ≤ N) (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ N - 1 → f n = n)
    (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N - 2) :
    f (m ^ 2) = m ^ 2 := by
  let t (v : ℕ) := v * (v + 1) / 2
  change ∀ u v : ℕ, 0 < u → 0 < v → f (u ^ 2 + t v) = f (u ^ 2) + f (t v) at hadd
  have ht (v : ℕ) (hv : 0 < v) (hvN : v ≤ N - 2) : f (t v) = (t v : ℂ) :=
    map_triangular_of_eq_on_prefix f hf N hlt v hv hvN
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hsmall : m ≤ 2
    · rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
      · simpa using hf.map_one
      · -- The additivity hypothesis only permits positive triangular indices.
        have h3 : f 3 = 3 := hlt 3 (by decide) (by omega)
        have h4 := hadd 1 2 (by decide) (by decide)
        norm_num [t, hf.map_one, h3] at h4 ⊢
        exact h4
    · have hid : m ^ 2 + t (m - 2) = (m - 1) ^ 2 + t m :=
        sq_add_triangular_sub_two_eq m (by omega)
      have hprev := ih (m - 1) (by omega) (by omega) (by omega)
      have hc := congrArg (fun n : ℕ ↦ (n : ℂ)) hid
      simp only [Nat.cast_add, Nat.cast_pow] at hc
      apply add_right_cancel (b := (t (m - 2) : ℂ))
      calc
        f (m ^ 2) + ↑(t (m - 2)) = f (m ^ 2 + t (m - 2)) := by
          rw [hadd m (m - 2) (by omega) (by omega), ht (m - 2) (by omega) (by omega)]
        _ = f ((m - 1) ^ 2 + t m) := congrArg f hid
        _ = ((m - 1 : ℕ) : ℂ) ^ 2 + ↑(t m) := by
          rw [hadd (m - 1) m (by omega) (by omega), hprev, ht m (by omega) hmN]
        _ = (m : ℂ) ^ 2 + ↑(t (m - 2)) := hc.symm

end MetaMathlibExt
