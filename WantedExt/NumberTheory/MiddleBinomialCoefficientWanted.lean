/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.Data.Set.Density

namespace MetaMathlibExt

@[expose] public section

open Nat Filter Topology

/-- **Valuation of a product of consecutive integers.** Let $m$ and $k$ be natural numbers and
$p$ a prime, and write $v_p(n)$ for the exponent of $p$ in a positive integer $n$. Then
$v_p\bigl((m+k)!/m!\bigr) \le v_p(k!) + \max \{ v_p(m + i) : 1 \le i \le k \}$, where the
maximum is $0$ when $k = 0$.

The quotient $(m+k)!/m! = (m+1) \cdots (m+k)$ is an integer. Unlike the source, the inequality
is stated also for $m = 0$ and $k = 0$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 3 (`integers-2026-A47-lem-3`). -/
public theorem_wanted padicValNat_factorial_div_factorial_le (m k p : ℕ) (hp : p.Prime) :
    padicValNat p ((m + k)! / m !) ≤
      padicValNat p k ! + (Finset.Icc 1 k).sup fun i => padicValNat p (m + i)

/-- **Valuations of the middle binomial coefficient on a set of density one.** Write $v_p(n)$ for
the exponent of a prime $p$ in a positive integer $n$, and for $m \ge 2$ let
$\alpha_p(m) = v_p\bigl(\binom{2m}{m}\bigr) / (\log m / \log p)$. There is a set $S$ of natural
numbers of natural density $1$ such that: $\alpha_2(m) \to 1/2$ as $m \to \infty$ within $S$; for
every $\varepsilon > 0$, $\alpha_3(m) \ge 34/81 - \varepsilon$ for all sufficiently large
$m \in S$; and $\alpha_p(m) \ge 0.39$ for every $m \in S$ and every prime $p$ with
$3 < p < 2 \log m$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 1 (`integers-2026-A47-lem-1`). -/
public theorem_wanted exists_density_one_padicValNat_centralBinom_bounds :
    ∃ S : Set ℕ, S.HasDensity 1 ∧
      Tendsto (fun m : ℕ => (padicValNat 2 (centralBinom m) : ℝ) / (Real.log m / Real.log 2))
        (atTop ⊓ 𝓟 S) (𝓝 (1 / 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop ⊓ 𝓟 S,
        (34 / 81 : ℝ) - ε ≤ (padicValNat 3 (centralBinom m) : ℝ) / (Real.log m / Real.log 3)) ∧
      ∀ m ∈ S, ∀ p : ℕ, p.Prime → 3 < p → (p : ℝ) < 2 * Real.log m →
        (0.39 : ℝ) ≤ (padicValNat p (centralBinom m) : ℝ) / (Real.log m / Real.log p)

/-- **Products of consecutive integers dividing the middle binomial coefficient.** Let $\eta$ be
a real number with $\eta < 1 / \log 4$. The set of natural numbers $m$ such that
$(m+k)!/m! = (m+1)(m+2) \cdots (m+k)$ divides $\binom{2m}{m}$ for every integer $k$ with
$1 \le k \le \eta \log m$ has natural density $1$.

The constant $1 / \log 4$ is the threshold imposed by the prime $2$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Theorem 1 (`integers-2026-A47-thm-1`). -/
public theorem_wanted factorial_div_factorial_dvd_centralBinom_density_one (η : ℝ)
    (hη : η < 1 / Real.log 4) :
    ({m : ℕ | ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ η * Real.log m → (m + k)! / m ! ∣ centralBinom m} :
      Set ℕ).HasDensity 1

/-- **Short runs of consecutive integers have small valuations almost always.** Write $v_p(n)$
for the exponent of a prime $p$ in a positive integer $n$. The set of natural numbers $m$ such
that $\max \{ v_p(m + i) : 1 \le i \le k \} \le 3 \log k / \log p$ for every integer $k$ with
$\frac{1}{2} \log m < k < \log m$ and every prime $p \le 2k$ has natural density $1$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 2 (`integers-2026-A47-lem-2`). -/
public theorem_wanted max_padicValNat_add_le_density_one :
    ({m : ℕ | ∀ k : ℕ, Real.log m / 2 < k → (k : ℝ) < Real.log m → ∀ p : ℕ, p.Prime →
        p ≤ 2 * k →
          (((Finset.Icc 1 k).sup fun i => padicValNat p (m + i) : ℕ) : ℝ) ≤
            3 * Real.log k / Real.log p} : Set ℕ).HasDensity 1

open scoped Classical in
/-- **Small valuations of the middle binomial coefficient are rare.** For a natural number $x$
let $K = \lfloor \exp(0.8 \sqrt{\log x}) \rfloor$ and, for a prime $p$, let
$D_p = 1 + \lfloor \log x / \log p \rfloor$. Write $v_p(n)$ for the exponent of $p$ in a
positive integer $n$. Then the number of integers $m$ with $1 \le m \le x$ for which some prime
$p \le 2K$ satisfies $v_p\bigl(\binom{2m}{m}\bigr) \le D_p / \log D_p$ is $o(x)$ as $x \to \infty$.

For large $x$ every prime $p \le 2K$ is at most $x$, so $D_p \ge 2$ and $\log D_p > 0$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 4 (`integers-2026-A47-lem-4`). -/
public theorem_wanted card_padicValNat_centralBinom_le_isLittleO :
    (fun x : ℕ => ((((Finset.Icc 1 x).filter fun m => ∃ p : ℕ, p.Prime ∧
        p ≤ 2 * ⌊Real.exp (0.8 * Real.sqrt (Real.log x))⌋₊ ∧
          (padicValNat p (centralBinom m) : ℝ) ≤
            ((1 + ⌊Real.log x / Real.log p⌋₊ : ℕ) : ℝ) /
              Real.log ((1 + ⌊Real.log x / Real.log p⌋₊ : ℕ) : ℝ)).card : ℕ) : ℝ))
      =o[atTop] fun x : ℕ => (x : ℝ)

open scoped Classical in
/-- **Large valuations in short runs of consecutive integers are rare.** For a natural number
$x$ let $K = \lfloor \exp(0.8 \sqrt{\log x}) \rfloor$ and, for a prime $p$, let
$D_p = 1 + \lfloor \log x / \log p \rfloor$. Write $v_p(n)$ for the exponent of $p$ in a
positive integer $n$. Then the number of integers $m$ with $1 \le m \le x$ for which some prime
$p < 2K$ satisfies $\max \{ v_p(m + i) : 1 \le i \le K \} > D_p / \log D_p$ is $o(x)$ as
$x \to \infty$.

For large $x$ every prime $p < 2K$ is at most $x$, so $D_p \ge 2$ and $\log D_p > 0$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 5 (`integers-2026-A47-lem-5`). -/
public theorem_wanted card_max_padicValNat_add_gt_isLittleO :
    (fun x : ℕ => ((((Finset.Icc 1 x).filter fun m => ∃ p : ℕ, p.Prime ∧
        p < 2 * ⌊Real.exp (0.8 * Real.sqrt (Real.log x))⌋₊ ∧
          ((1 + ⌊Real.log x / Real.log p⌋₊ : ℕ) : ℝ) /
              Real.log ((1 + ⌊Real.log x / Real.log p⌋₊ : ℕ) : ℝ) <
            (((Finset.Icc 1 ⌊Real.exp (0.8 * Real.sqrt (Real.log x))⌋₊).sup
              fun i => padicValNat p (m + i) : ℕ) : ℝ)).card : ℕ) : ℝ))
      =o[atTop] fun x : ℕ => (x : ℝ)

/-- **Binomial coefficients dividing the middle binomial coefficient.** The set of natural
numbers $m$ such that $\binom{m+k}{k}$ divides $\binom{2m}{m}$ for every integer $k$ with
$1 \le k \le \exp(0.8 \sqrt{\log m})$ has natural density $1$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Theorem 2 (`integers-2026-A47-thm-2`). -/
public theorem_wanted choose_dvd_centralBinom_density_one :
    ({m : ℕ | ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.exp (0.8 * Real.sqrt (Real.log m)) →
        (m + k).choose k ∣ centralBinom m} : Set ℕ).HasDensity 1

end

end MetaMathlibExt
