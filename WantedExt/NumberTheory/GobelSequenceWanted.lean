/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace MetaMathlibExt

open Filter Topology Asymptotics

@[expose] public section

/-- The `(k, l)`-Göbel sequence `g_{k,l}(n)`: `g_{k,l}(1) = l` and
`(n + 1) g_{k,l}(n + 1) = g_{k,l}(n) (n + g_{k,l}(n)^{k-1})` for `n ≥ 1`.
The paper indexes from `n = 1` and takes `k, l ≥ 2` (Lemma 5 also admits
`k, l ≥ 1`); here `k, l` are arbitrary naturals and the unused value at
`n = 0` is set to `0`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public def gobelSequence (k l : ℕ) : ℕ → ℚ
  | 0 => 0
  | 1 => l
  | n + 2 => gobelSequence k l (n + 1) * ((n + 1 : ℚ) + gobelSequence k l (n + 1) ^ (k - 1))
      / (n + 2)

/-- Initial value `g_{k,l}(1) = l`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public theorem gobelSequence_one (k l : ℕ) : gobelSequence k l 1 = l := rfl

/-- The defining recursion `(n + 1) g_{k,l}(n + 1) = g_{k,l}(n) (n + g_{k,l}(n)^{k-1})`
for `n ≥ 1`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public theorem gobelSequence_succ (k l n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℚ) * gobelSequence k l (n + 1)
      = gobelSequence k l n * ((n : ℚ) + gobelSequence k l n ^ (k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show (↑(m + 1) + 1 : ℚ) * (gobelSequence k l (m + 1) *
      ((m + 1 : ℚ) + gobelSequence k l (m + 1) ^ (k - 1)) / (m + 2)) = _
  have h : (m + 2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Göbel's original sequence `g_{2,2}` starts `2, 3, 5, 10, 28`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 1. -/
public theorem gobelSequence_two_two_small :
    gobelSequence 2 2 2 = 3 ∧ gobelSequence 2 2 3 = 5 ∧ gobelSequence 2 2 4 = 10 ∧
      gobelSequence 2 2 5 = 28 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gobelSequence]

/-- Theorem 2: every `(k, l)`-Göbel sequence with `k, l ≥ 2` is integral for
`1 ≤ n ≤ 6`, and `g_{k,l}(7)` fails to be an integer exactly when `k ≡ 2 (mod 6)`
and `l ≡ 3 (mod 7)`. Together these say `min_{k,l ≥ 2} N_{k,l} = 7` with
`N_{k,l} = 7` iff `k ≡ 2 (mod 6)` and `l ≡ 3 (mod 7)`, where `N_{k,l}` is the
first index at which `g_{k,l}` is not an integer; the threshold `N_{k,l}` is
not introduced as a separate definition.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 2 (`jis-2024-24.8.1-thm-2`). -/
public theorem_wanted gobelSequence_integral_le_six_and_seven_iff :
    (∀ k l : ℕ, 2 ≤ k → 2 ≤ l → ∀ n : ℕ, 1 ≤ n → n ≤ 6 →
        ∃ z : ℤ, gobelSequence k l n = z) ∧
      ∀ k l : ℕ, 2 ≤ k → 2 ≤ l →
        ((¬ ∃ z : ℤ, gobelSequence k l 7 = z) ↔ k % 6 = 2 ∧ l % 7 = 3)

/-- Theorem 4 (generalized Zagier asymptotic): for `k, l ≥ 2` there are a constant
`C > 1` and coefficients `a_r` with
`g_{k,l}(n) ∼ C^{k^n} n^{1/(k-1)} (1 + ∑_{r ≥ 1} a_r / n^r)` as an asymptotic
expansion in the paper's sense: for every `R ≥ 0` the error after the terms
`r ≤ R` is `O(C^{k^n} n^{1/(k-1)} n^{-(R+1)})`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 4 (`jis-2024-24.8.1-thm-4`). -/
public theorem_wanted gobelSequence_asymptotic_expansion (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    ∃ C : ℝ, 1 < C ∧ ∃ a : ℕ → ℝ, ∀ R : ℕ,
      (fun n : ℕ => (gobelSequence k l n : ℝ)
          - C ^ (k ^ n) * (n : ℝ) ^ ((1 : ℝ) / (k - 1))
            * (1 + ∑ r ∈ Finset.Icc 1 R, a r / (n : ℝ) ^ r))
        =O[atTop]
      (fun n : ℕ => C ^ (k ^ n) * (n : ℝ) ^ ((1 : ℝ) / (k - 1)) / (n : ℝ) ^ (R + 1))

/-- Lemma 5 (key properties), with `r = ν_p(N!)` and `k, l ≥ 1`. Membership in
`ℤ_(p)` is written `0 ≤ padicValRat p x`, and `x ∈ p^s ℤ_(p)` is written
`x = 0 ∨ s ≤ padicValRat p x`. Parts:
(1) if `p > N` then `g_{k,l}(N) ∈ ℤ_(p)`;
(2) if `g_{k,l}(n) ∉ ℤ_(p)` then `g_{k,l}(n + 1) ∉ ℤ_(p)`;
(3) if `p ≤ N`, `k₁, k₂ ≥ r` and `k₁ ≡ k₂ (mod φ(p^r))`, then `g_{k₁,l}(n) ∈ ℤ_(p)`
iff `g_{k₂,l}(n) ∈ ℤ_(p)`, and then `g_{k₁,l}(n) - g_{k₂,l}(n) ∈ p^{r - ν_p(n!)} ℤ_(p)`;
(4) the same with `l₁ ≡ l₂ (mod p^r)` in place of the condition on `k`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 5 (`jis-2024-24.8.1-lem-5`). -/
public theorem_wanted gobelSequence_padic_key_properties (p : ℕ) (hp : p.Prime)
    (N : ℕ) (hN : 1 ≤ N) :
    (∀ k l : ℕ, 1 ≤ k → 1 ≤ l → N < p → 0 ≤ padicValRat p (gobelSequence k l N)) ∧
    (∀ k l n : ℕ, 1 ≤ k → 1 ≤ l → 1 ≤ n → n ≤ N →
        padicValRat p (gobelSequence k l n) < 0 →
          padicValRat p (gobelSequence k l (n + 1)) < 0) ∧
    (∀ k₁ k₂ l n : ℕ, p ≤ N → 1 ≤ l → 1 ≤ n → n ≤ N →
        padicValNat p N.factorial ≤ k₁ → padicValNat p N.factorial ≤ k₂ →
        k₁ ≡ k₂ [MOD (p ^ padicValNat p N.factorial).totient] →
        ((0 ≤ padicValRat p (gobelSequence k₁ l n) ↔
            0 ≤ padicValRat p (gobelSequence k₂ l n)) ∧
          (0 ≤ padicValRat p (gobelSequence k₁ l n) →
            gobelSequence k₁ l n - gobelSequence k₂ l n = 0 ∨
              ((padicValNat p N.factorial : ℤ) - padicValNat p n.factorial
                ≤ padicValRat p (gobelSequence k₁ l n - gobelSequence k₂ l n))))) ∧
    (∀ k l₁ l₂ n : ℕ, p ≤ N → 1 ≤ k → 1 ≤ l₁ → 1 ≤ l₂ → 1 ≤ n → n ≤ N →
        l₁ ≡ l₂ [MOD p ^ padicValNat p N.factorial] →
        ((0 ≤ padicValRat p (gobelSequence k l₁ n) ↔
            0 ≤ padicValRat p (gobelSequence k l₂ n)) ∧
          (0 ≤ padicValRat p (gobelSequence k l₁ n) →
            gobelSequence k l₁ n - gobelSequence k l₂ n = 0 ∨
              ((padicValNat p N.factorial : ℤ) - padicValNat p n.factorial
                ≤ padicValRat p (gobelSequence k l₁ n - gobelSequence k l₂ n)))))

/-- Lemma 6: Theorem 2 is equivalent to the conjunction of four finite `p`-adic
claims about `g_{k,l}(7)` (membership in `ℤ_(p)` written `0 ≤ padicValRat p x`):
`g_{k,l}(7) ∈ ℤ_(2)` for `2 ≤ k ≤ 11`, `1 ≤ l ≤ 16`; `g_{k,l}(7) ∈ ℤ_(3)` for
`2 ≤ k ≤ 7`, `1 ≤ l ≤ 9`; `g_{k,l}(7) ∈ ℤ_(5)` for `1 ≤ k ≤ 4`, `1 ≤ l ≤ 5`; and for
`1 ≤ k ≤ 6`, `1 ≤ l ≤ 7`, `g_{k,l}(7) ∉ ℤ_(7)` iff `(k, l) = (2, 3)`. The left side
is the Theorem 2 statement as formalized in
`gobelSequence_integral_le_six_and_seven_iff`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 6 (`jis-2024-24.8.1-lem-6`). -/
public theorem_wanted gobelSequence_seven_iff_padic_claims :
    ((∀ k l : ℕ, 2 ≤ k → 2 ≤ l → ∀ n : ℕ, 1 ≤ n → n ≤ 6 →
        ∃ z : ℤ, gobelSequence k l n = z) ∧
      ∀ k l : ℕ, 2 ≤ k → 2 ≤ l →
        ((¬ ∃ z : ℤ, gobelSequence k l 7 = z) ↔ k % 6 = 2 ∧ l % 7 = 3)) ↔
    ((∀ k ∈ Finset.Icc 2 11, ∀ l ∈ Finset.Icc 1 16,
        0 ≤ padicValRat 2 (gobelSequence k l 7)) ∧
      (∀ k ∈ Finset.Icc 2 7, ∀ l ∈ Finset.Icc 1 9,
        0 ≤ padicValRat 3 (gobelSequence k l 7)) ∧
      (∀ k ∈ Finset.Icc 1 4, ∀ l ∈ Finset.Icc 1 5,
        0 ≤ padicValRat 5 (gobelSequence k l 7)) ∧
      (∀ k ∈ Finset.Icc 1 6, ∀ l ∈ Finset.Icc 1 7,
        (padicValRat 7 (gobelSequence k l 7) < 0 ↔ k = 2 ∧ l = 3)))

/-- Lemma 7: for `k, l ≥ 2` and `n ≥ 1`, the real numbers
`C_{k,l}(n) = g_{k,l}(n)^{1/k^n}` satisfy `C_{k,l}(n) > C_{k,l}(n + 1) > 1`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 7 (`jis-2024-24.8.1-lem-7`). -/
public theorem_wanted gobelSequence_root_strictAnti (k l n : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hn : 1 ≤ n) :
    (gobelSequence k l (n + 1) : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1))
        < (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n) ∧
      1 < (gobelSequence k l (n + 1) : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ (n + 1))

/-- Lemma 8: let `k ≥ 2`, let `σ_k = exp (∑_{m ≥ 1} log m / k^m)` be the `k`-Somos
constant, and let `t` satisfy `t(n + 1) = t(n)^k / (n + 1)`. If `t(0) > σ_k`, then
`t(n)^{1/k^n}` is antitone (it is constant from `n = 0` to `n = 1`, so the paper's
"decreases monotonically" is the non-strict reading) and tends to some `c > 1`.
The sum is written over all `m : ℕ`; the `m = 0` term is `log 0 = 0`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 8 (`jis-2024-24.8.1-lem-8`). -/
public theorem_wanted somosLike_root_antitone_tendsto (k : ℕ) (hk : 2 ≤ k) (t : ℕ → ℝ)
    (ht : ∀ n : ℕ, t (n + 1) = t n ^ k / (n + 1))
    (h0 : Real.exp (∑' m : ℕ, Real.log m / (k : ℝ) ^ m) < t 0) :
    ∃ c : ℝ, 1 < c ∧ Antitone (fun n : ℕ => t n ^ ((1 : ℝ) / (k : ℝ) ^ n)) ∧
      Tendsto (fun n : ℕ => t n ^ ((1 : ℝ) / (k : ℝ) ^ n)) atTop (𝓝 c)

/-- Lemma 9: for `k, l ≥ 2` and a sequence `t` with `t(n + 1) = t(n)^k / (n + 1)`, if
`l ≥ t(0)^k` then `g_{k,l}(n) ≥ t(n)` for all `n ≥ 1`. The paper assumes the real
`t(0) > 1`; the statement holds without it (for even `k`, `t(n) ≥ 0` for `n ≥ 1`;
for odd `k`, `x ↦ x^k` is monotone), so that hypothesis is dropped.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 9 (`jis-2024-24.8.1-lem-9`). -/
public theorem_wanted somosLike_le_gobelSequence (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (t : ℕ → ℝ) (ht : ∀ n : ℕ, t (n + 1) = t n ^ k / (n + 1)) (h0 : t 0 ^ k ≤ l)
    (n : ℕ) (hn : 1 ≤ n) :
    t n ≤ gobelSequence k l n

/-- Proposition 10: for `k, l ≥ 2` the sequence `C_{k,l}(n) = g_{k,l}(n)^{1/k^n}`
converges to a limit `C_{k,l} > 1`. The paper defines `C_{k,l}` as this limit
(convergence follows from Lemma 7); the statement packages existence of the
limit with the strict bound.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Proposition 10 (`jis-2024-24.8.1-prop-10`). -/
public theorem_wanted gobelSequence_root_tendsto_gt_one (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    ∃ C : ℝ, 1 < C ∧
      Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n)) atTop (𝓝 C)

/-- Theorem 11: for `k, l ≥ 2`, with `C_{k,l}` the limit of
`C_{k,l}(n) = g_{k,l}(n)^{1/k^n}`, and every real `R > 0`,
`exp (∑_{m ≥ 1} log (m + n) / k^m) - (C_{k,l}(n) / C_{k,l})^{k^n} = O(n^{-R})`.
The sum is reindexed `m ↦ m + 1` over `ℕ`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 11 (`jis-2024-24.8.1-thm-11`). -/
public theorem_wanted gobelSequence_error_isBigO (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (R : ℝ) (hR : 0 < R) :
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n) / C) ^ (k ^ n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-R))

/-- Lemma 12: for `k, l ≥ 2`, `n ≥ 1`, and `C = C_{k,l}` the limit of
`C_{k,l}(n) = g_{k,l}(n)^{1/k^n}`, the error
`ε_{k,l}(n) = ∑_{m ≥ 1} log (m + n) / k^m - k^n (log C_{k,l}(n) - log C_{k,l})` equals
`∑_{m ≥ 1} k^{-m} log (1 + (m + n - 1) / g_{k,l}(m + n - 1)^{k-1})`, and this sum is at
most `2n / C_{k,l}^{(k-1) k^n}`. The definition of `ε_{k,l}` is taken from the
paper's Section 3.2; both sums are reindexed `m ↦ m + 1` over `ℕ`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 12 (`jis-2024-24.8.1-lem-12`). -/
public theorem_wanted gobelSequence_error_eq_tsum_le (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (n : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - (k : ℝ) ^ n * (Real.log ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
          - Real.log C)
      = ∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1))
          / (k : ℝ) ^ (m + 1) ∧
    ∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1))
          / (k : ℝ) ^ (m + 1)
      ≤ 2 * n / C ^ ((k - 1) * k ^ n)

/-- Theorem 15 (Sondow and Hadjicostas): for `k ≥ 2` let
`a_{k,r} = ∑_{m_1 + 2 m_2 + ⋯ + r m_r = r} ∏_{j=1}^{r} (1 / m_j!)
((-1)^{j-1} / j · A_j(k) / (k-1)^{j+1})^{m_j}`, where `A_j` is the Eulerian
polynomial. Then `exp (∑_{m ≥ 1} log (m + n) / k^m) ∼ n^{1/(k-1)} (1 + ∑_{r ≥ 1} a_{k,r} / n^r)`
as an asymptotic expansion: for every `R ≥ 0` the error after the terms `r ≤ R` is
`O(n^{1/(k-1)} n^{-(R+1)})`. The Eulerian ratio is replaced by its defining series
`A_j(k) / (k-1)^{j+1} = ∑_{m ≥ 1} m^j / k^m` (the paper's definition of `A_j`); the
partition sum ranges over `m : Fin r → ℕ` with entries at most `r` (the constraint
forces this), index `j` of `Fin r` standing for the paper's `j + 1`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 15, quoting Sondow and Hadjicostas (2007), Theorem 9 and
Lemma 1 (`jis-2024-24.8.1-thm-15`). -/
public theorem_wanted somos_tsum_asymptotic_expansion (k : ℕ) (hk : 2 ≤ k) (a : ℕ → ℝ)
    (ha : ∀ r : ℕ, a r =
      ∑ m ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (r + 1)).filter
          (fun m => ∑ j : Fin r, ((j : ℕ) + 1) * m j = r),
        ∏ j : Fin r, (1 / ((m j).factorial : ℝ)) *
          ((-1 : ℝ) ^ (j : ℕ) / ((j : ℕ) + 1) *
            ∑' i : ℕ, (i : ℝ) ^ ((j : ℕ) + 1) / (k : ℝ) ^ i) ^ (m j))
    (R : ℕ) :
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - (n : ℝ) ^ ((1 : ℝ) / (k - 1)) * (1 + ∑ r ∈ Finset.Icc 1 R, a r / (n : ℝ) ^ r))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (k - 1)) / (n : ℝ) ^ (R + 1))

/-- The residue in `ZMod m` of a rational `x` whose denominator is prime to `m`,
namely `num x · (den x)⁻¹`. Used to read congruences in `ℤ_(p)` modulo `p^r`; on
other inputs `ZMod.inv` gives a junk value.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 4 (residues of `g_{k,l}(n)` modulo `p^r` in `ℤ_(p)`). -/
public def ratResidue (m : ℕ) (x : ℚ) : ZMod m :=
  (x.num : ZMod m) * (x.den : ZMod m)⁻¹

/-- On integers `ratResidue` is the usual cast.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 4. -/
public theorem ratResidue_intCast (m : ℕ) (z : ℤ) : ratResidue m z = (z : ZMod m) := by
  simp [ratResidue]

/-- Theorem 18: for a prime `p` and `k, l, r ≥ 2`, let
`I = {1 ≤ n < p : g_{k,l}(n) ≡ 0 (mod p^{r-1})}` (congruence in `ℤ_(p)`) and let
`G^r_{k,l,p}` be the set of residues of `g_{k,l}(n)` modulo `p^r` for `n ∈ I`. Then
`G^r_{k,l,p} = {0}` or `|G^r_{k,l,p}| = |I|`. For `n < p`, `g_{k,l}(n) ∈ ℤ_(p)`, so the
residue is `ratResidue (p^r)`; `x ≡ 0 (mod p^{r-1})` is written
`x = 0 ∨ r - 1 ≤ padicValRat p x`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 18 (`jis-2024-24.8.1-thm-18`). -/
public theorem_wanted gobelSequence_residues_singleton_or_injective (p : ℕ) (hp : p.Prime)
    (k l r : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (hr : 2 ≤ r) :
    ((Finset.Ico 1 p).filter (fun n => gobelSequence k l n = 0 ∨
          ((r : ℤ) - 1 ≤ padicValRat p (gobelSequence k l n)))).image
        (fun n => ratResidue (p ^ r) (gobelSequence k l n)) = {0} ∨
      (((Finset.Ico 1 p).filter (fun n => gobelSequence k l n = 0 ∨
          ((r : ℤ) - 1 ≤ padicValRat p (gobelSequence k l n)))).image
        (fun n => ratResidue (p ^ r) (gobelSequence k l n))).card =
      ((Finset.Ico 1 p).filter (fun n => gobelSequence k l n = 0 ∨
          ((r : ℤ) - 1 ≤ padicValRat p (gobelSequence k l n)))).card

/-- Lemma 20: for a prime `p`, `k, l, r ≥ 2`, `1 ≤ a < p` and `0 ≤ b < p`, if
`g_{k,l}(a) ≡ b p^{r-1} (mod p^r)` then `n g_{k,l}(n) ≡ a b p^{r-1} (mod p^r)` for every
`a ≤ n < p`. Congruences are in `ℤ_(p)`: `x ≡ y (mod p^r)` is written
`x - y = 0 ∨ r ≤ padicValRat p (x - y)`.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 20 (`jis-2024-24.8.1-lem-20`). -/
public theorem_wanted gobelSequence_mul_index_congr (p : ℕ) (hp : p.Prime) (k l r a b : ℕ)
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hr : 2 ≤ r) (ha₁ : 1 ≤ a) (hap : a < p) (hbp : b < p)
    (hg : gobelSequence k l a - b * (p : ℚ) ^ (r - 1) = 0 ∨
      (r : ℤ) ≤ padicValRat p (gobelSequence k l a - b * (p : ℚ) ^ (r - 1)))
    (n : ℕ) (han : a ≤ n) (hnp : n < p) :
    n * gobelSequence k l n - a * b * (p : ℚ) ^ (r - 1) = 0 ∨
      (r : ℤ) ≤ padicValRat p (n * gobelSequence k l n - a * b * (p : ℚ) ^ (r - 1))

end

end MetaMathlibExt
