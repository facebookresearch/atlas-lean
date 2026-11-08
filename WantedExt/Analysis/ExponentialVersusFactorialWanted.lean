/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MetaMathlibExt

@[expose] public section

open Real Filter Topology

/-- Lemma 2: for `b > a > e^{1/e}`, the sequence `a_n = log_a^{(n)} (b ↑↑ n)`
(the `n`-fold iterated base-`a` logarithm of the power tower `b ↑↑ n`) is
increasing and has a finite limit. The tower is written as the `n`-fold
iterate of `x ↦ b ^ x` from `1` (so `b ↑↑ 0 = 1`, `b ↑↑ 1 = b`), `n` runs over
`ℕ` including `0` (`a_0 = 1`), "increasing" is read as strictly increasing,
and a finite limit is stated as convergence to a real number.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 2 (`jis-2025-25.2.8-lem-2`). -/
public theorem_wanted iterate_logb_tetration_strictMono_and_converges {a b : ℝ}
    (ha : Real.exp (1 / Real.exp 1) < a) (hab : a < b) :
    StrictMono (fun n : ℕ => (Real.logb a)^[n] ((fun x : ℝ => b ^ x)^[n] 1)) ∧
      ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.logb a)^[n] ((fun x : ℝ => b ^ x)^[n] 1))
        atTop (𝓝 L)

/-- Lemma 9, first inequality: `Γ(x + 1) > (x / e)^x` for every real `x ≥ 1`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 9 (`jis-2025-25.2.8-lem-9`). -/
public theorem_wanted div_exp_one_rpow_lt_Gamma_add_one {x : ℝ} (hx : 1 ≤ x) :
    (x / Real.exp 1) ^ x < Real.Gamma (x + 1)

/-- Lemma 9, second inequality: `Γ(x + 1) ln Γ(x + 1) ≤ Γ(x)^{Γ(x)}` for every
real `x > 4`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 9 (`jis-2025-25.2.8-lem-9`). -/
public theorem_wanted Gamma_add_one_mul_log_le_Gamma_rpow_self {x : ℝ} (hx : 4 < x) :
    Real.Gamma (x + 1) * Real.log (Real.Gamma (x + 1)) ≤ Real.Gamma x ^ Real.Gamma x

/-- Normalization of power towers: for `a, b > e^{1/e}` with `a ≠ b` there are `N ≥ 0`,
`k ∈ ℤ` and a convergent sequence `(c_n)` with `1 < c_n < b` and `a ↑↑ n = E_{n+k}(b, c_n)`
for all `n ≥ N`. Here `E_m(b, c)` (the tower `b^{b^{⋯^c}}` with `m` copies of `b`) is the
`m`-fold iterate of `x ↦ b ^ x` from `c`, the tower `a ↑↑ n = E_{n-1}(a, a)` is the `n`-fold
iterate of `x ↦ a ^ x` from `1`, and the index `n + k` is required to be nonnegative for
`n ≥ N` (implicit in the paper).

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 1 (`jis-2025-25.2.8-thm-1`), quoted from the
author's earlier paper. -/
public theorem_wanted exists_tetration_eq_iterate_rpow_eventually {a b : ℝ}
    (ha : Real.exp (1 / Real.exp 1) < a) (hb : Real.exp (1 / Real.exp 1) < b) (hab : a ≠ b) :
    ∃ N : ℕ, ∃ k : ℤ, ∃ c : ℕ → ℝ, (∃ L : ℝ, Tendsto c atTop (𝓝 L)) ∧
      ∀ n ≥ N, 0 ≤ (n : ℤ) + k ∧ 1 < c n ∧ c n < b ∧
        (fun x : ℝ => a ^ x)^[n] 1 = (fun x : ℝ => b ^ x)^[((n : ℤ) + k).toNat] (c n)

/-- For `a, b > e^{1/e}` and `n > 0` there are `p ≥ 0` and `c ∈ (1, b]` with
`a ↑↑ n = E_p(b, c)`, where `a ↑↑ n` is the `n`-fold iterate of `x ↦ a ^ x` from `1` and
`E_p(b, c)` the `p`-fold iterate of `x ↦ b ^ x` from `c`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Lemma 3 (`jis-2025-25.2.8-lem-3`), quoted from the
author's earlier paper. -/
public theorem_wanted exists_tetration_eq_iterate_rpow {a b : ℝ}
    (ha : Real.exp (1 / Real.exp 1) < a) (hb : Real.exp (1 / Real.exp 1) < b) {n : ℕ}
    (hn : 0 < n) :
    ∃ p : ℕ, ∃ c ∈ Set.Ioc 1 b, (fun x : ℝ => a ^ x)^[n] 1 = (fun x : ℝ => b ^ x)^[p] c

/-- Comparison of iterated factorials: for `n, n' ≥ 3` and `k > k'`, if
`F_{k-k'}(n) > n'` then `F_k(n) > F_{k'}(n')`, where `F_j(m) = m!⋯!` (`j` factorials) is
the `j`-fold iterate of `Nat.factorial` at `m`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 4 (`jis-2025-25.2.8-thm-4`). -/
public theorem_wanted iterate_factorial_lt_iterate_factorial {n n' k k' : ℕ} (hn : 3 ≤ n)
    (hn' : 3 ≤ n') (hk : k' < k) (h : n' < Nat.factorial^[k - k'] n) :
    Nat.factorial^[k'] n' < Nat.factorial^[k] n

/-- Iterated factorials as base-`10` power towers: for `k ≥ 3` there are `ℓ ∈ ℤ`, `N > 0`
and a sequence `(c_n)` such that for `n ≥ N`, `1 < c_n ≤ 10` and `F_n(k) = E_{n+ℓ}(10, c_n)`;
`(c_n)_{n ≥ N}` is (strictly) increasing with a limit `c`, and
`E_{n+ℓ}(10, c) / (F_n(k) ln F_n(k)) → 1 / ln 10`. Here `F_n(k)` is the `n`-fold iterate of
`Nat.factorial` at `k` (cast to `ℝ`), `E_m(10, c)` the `m`-fold iterate of `x ↦ 10 ^ x` from
`c`, and `n + ℓ` is required to be nonnegative for `n ≥ N` (implicit in the paper).

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 5 (`jis-2025-25.2.8-thm-5`). -/
public theorem_wanted exists_iterate_factorial_eq_iterate_rpow_ten {k : ℕ} (hk : 3 ≤ k) :
    ∃ ℓ : ℤ, ∃ N : ℕ, 0 < N ∧ ∃ c : ℕ → ℝ, ∃ L : ℝ,
      (∀ n ≥ N, 0 ≤ (n : ℤ) + ℓ ∧ 1 < c n ∧ c n ≤ 10 ∧
        ((Nat.factorial^[n] k : ℕ) : ℝ) = (fun x : ℝ => 10 ^ x)^[((n : ℤ) + ℓ).toNat] (c n)) ∧
      StrictMonoOn c (Set.Ici N) ∧ Tendsto c atTop (𝓝 L) ∧
      Tendsto (fun n : ℕ => (fun x : ℝ => 10 ^ x)^[((n : ℤ) + ℓ).toNat] L /
          (((Nat.factorial^[n] k : ℕ) : ℝ) * Real.log ((Nat.factorial^[n] k : ℕ) : ℝ)))
        atTop (𝓝 (1 / Real.log 10))

/-- Iterated factorials as tetrations: for `k ≥ 3` there are `b_n > e^{1/e}` with
`F_n(k) = b_n ↑↑ n` for every `n ≥ 1`, and `(b_n)` converges to some `b ≤ k!`. Here `F_n(k)`
is the `n`-fold iterate of `Nat.factorial` at `k` and `b ↑↑ n` the `n`-fold iterate of
`x ↦ b ^ x` from `1`; `n = 0` is excluded since the paper's `b ↑↑ n = E_{n-1}(b, b)` is
defined only for `n ≥ 1`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 8 (`jis-2025-25.2.8-thm-8`). -/
public theorem_wanted exists_iterate_factorial_eq_tetration {k : ℕ} (hk : 3 ≤ k) :
    ∃ b : ℕ → ℝ, (∀ n ≥ 1, Real.exp (1 / Real.exp 1) < b n ∧
        ((Nat.factorial^[n] k : ℕ) : ℝ) = (fun x : ℝ => b n ^ x)^[n] 1) ∧
      ∃ L ≤ ((k.factorial : ℕ) : ℝ), Tendsto b atTop (𝓝 L)

/-- Iterated Gamma values as power towers: let `z > 1` be the nontrivial solution of
`Γ(z) = z`. For `b > e^{1/e}` and `x > z` there are `ℓ ∈ ℤ`, `N > 0` and a sequence `(c_n)`
such that for `n ≥ N`, `1 < c_n ≤ b` and `Γ^n(x) = E_{n+ℓ}(b, c_n)`; `(c_n)_{n ≥ N}` is
(strictly) increasing with a limit `c`, and
`E_{n+ℓ}(b, c) / ((Γ^n(x) - 1) ln(Γ^n(x) - 1)) → 1 / ln b`. `Γ^n` is the `n`-fold iterate
of `Real.Gamma`, `E_m(b, c)` the `m`-fold iterate of `x ↦ b ^ x` from `c`, and `n + ℓ` is
required to be nonnegative for `n ≥ N`. Corrected reading of the printed statement: `x > z`
for the printed `x ≥ z` (at `x = z` the orbit is constant while `E_{n+ℓ}(b, c_n)` tends to
infinity); `Γ^n(x)` for the printed `Γ^n(k)` (`k` is unbound); and `c_n ≤ b`, the bound of
the proof and of its restatement in the proof of Theorem 12, for the printed `c_n ≤ 10`
(copied from Theorem 5).

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 10 (`jis-2025-25.2.8-thm-10`). -/
public theorem_wanted exists_iterate_Gamma_eq_iterate_rpow {z b x : ℝ} (hz : 1 < z)
    (hΓz : Real.Gamma z = z) (hb : Real.exp (1 / Real.exp 1) < b) (hx : z < x) :
    ∃ ℓ : ℤ, ∃ N : ℕ, 0 < N ∧ ∃ c : ℕ → ℝ, ∃ L : ℝ,
      (∀ n ≥ N, 0 ≤ (n : ℤ) + ℓ ∧ 1 < c n ∧ c n ≤ b ∧
        Real.Gamma^[n] x = (fun y : ℝ => b ^ y)^[((n : ℤ) + ℓ).toNat] (c n)) ∧
      StrictMonoOn c (Set.Ici N) ∧ Tendsto c atTop (𝓝 L) ∧
      Tendsto (fun n : ℕ => (fun y : ℝ => b ^ y)^[((n : ℤ) + ℓ).toNat] L /
          ((Real.Gamma^[n] x - 1) * Real.log (Real.Gamma^[n] x - 1)))
        atTop (𝓝 (1 / Real.log b))

/-- For `n > 0` and `b ≥ e`, `Γ(E_n(b, b)) > E_{n+1}(b, b)`, where `E_m(b, b)` is the
`m`-fold iterate of `x ↦ b ^ x` from `b`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Lemma 11 (`jis-2025-25.2.8-lem-11`). -/
public theorem_wanted iterate_rpow_succ_lt_Gamma_iterate_rpow {b : ℝ} (hb : Real.exp 1 ≤ b)
    {n : ℕ} (hn : 0 < n) :
    (fun x : ℝ => b ^ x)^[n + 1] b < Real.Gamma ((fun x : ℝ => b ^ x)^[n] b)

/-- Tetrations as iterated Gamma values: let `z > 1` be the nontrivial solution of
`Γ(z) = z`. For `b > z` there is a convergent sequence `(x_n)`, strictly decreasing for all
sufficiently large `n`, with `b ↑↑ n = Γ^n(x_n)` for `n ≥ 1`. Here `b ↑↑ n` is the `n`-fold
iterate of `x ↦ b ^ x` from `1` and `Γ^n` the `n`-fold iterate of `Real.Gamma`; `n = 0` is
excluded since the paper's `b ↑↑ n = E_{n-1}(b, b)` is defined only for `n ≥ 1`.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 12 (`jis-2025-25.2.8-thm-12`). -/
public theorem_wanted exists_tetration_eq_iterate_Gamma {z b : ℝ} (hz : 1 < z)
    (hΓz : Real.Gamma z = z) (hb : z < b) :
    ∃ x : ℕ → ℝ, (∀ n ≥ 1, (fun y : ℝ => b ^ y)^[n] 1 = Real.Gamma^[n] (x n)) ∧
      (∃ L : ℝ, Tendsto x atTop (𝓝 L)) ∧ ∃ M : ℕ, StrictAntiOn x (Set.Ici M)

end

end MetaMathlibExt
