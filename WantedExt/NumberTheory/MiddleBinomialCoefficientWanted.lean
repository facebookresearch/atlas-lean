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

/-- For all natural numbers `m`, `k` and every prime `p`,
`v_p((m + k)! / m!) ≤ v_p(k!) + max {v_p(m + i) : 1 ≤ i ≤ k}`.

The paper states this for `m, k > 0`; the inequality also holds when `m = 0` or `k = 0`
(the maximum over an empty range is `0`), so those hypotheses are dropped. The quotient
`(m + k)! / m!` is exact.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 3 (`integers-2026-A47-lem-3`). -/
public theorem_wanted padicValNat_factorial_div_factorial_le (m k p : ℕ) (hp : p.Prime) :
    padicValNat p ((m + k)! / m !) ≤
      padicValNat p k ! + (Finset.Icc 1 k).sup fun i => padicValNat p (m + i)

/-- Lemma 1: with `α_p(m) = v_p(C(2m, m)) / (log m / log p)`, there is a set `S` of natural
density `1` on which `α_2(m) = 1/2 + o(1)`, `α_3(m) ≥ 34/81 + o(1)`, and `α_p(m) ≥ 0.39` for
every prime `p` with `3 < p < 2 log m`. The `o(1)` terms are limits along `m → ∞` within `S`;
the third bound has no `o(1)` in the record and is stated for every `m ∈ S`.

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

/-- Theorem 1: for every fixed `η < 1 / log 4`, the set of `m` such that
`(m + k)! / m! = (m + 1)(m + 2) ⋯ (m + k)` divides `C(2m, m)` for every positive integer
`k ≤ η log m` has natural density `1`. The divisibility sign is lost in the extracted display;
it is the relation of the record's own continuation ("replacing the product with `C(m+k, k)`",
"`C(m+k, k) ∣ C(2m, m)` almost always"), and `1 / log 4` is the `2`-adic threshold for it.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Theorem 1 (`integers-2026-A47-thm-1`). -/
public theorem_wanted factorial_div_factorial_dvd_centralBinom_density_one (η : ℝ)
    (hη : η < 1 / Real.log 4) :
    ({m : ℕ | ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ η * Real.log m → (m + k)! / m ! ∣ centralBinom m} :
      Set ℕ).HasDensity 1

/-- Lemma 2: the set of `m` such that `max {v_p(m + i) : 1 ≤ i ≤ k} ≤ 3 log k / log p` for all
`k` with `(1/2) log m < k < log m` and all primes `p ≤ 2k` has natural density `1`.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 2 (`integers-2026-A47-lem-2`). -/
public theorem_wanted max_padicValNat_add_le_density_one :
    ({m : ℕ | ∀ k : ℕ, Real.log m / 2 < k → (k : ℝ) < Real.log m → ∀ p : ℕ, p.Prime →
        p ≤ 2 * k →
          (((Finset.Icc 1 k).sup fun i => padicValNat p (m + i) : ℕ) : ℝ) ≤
            3 * Real.log k / Real.log p} : Set ℕ).HasDensity 1

open scoped Classical in
/-- Lemma 4: with `D = D_p = 1 + ⌊log x / log p⌋` and `K = ⌊exp(0.8 √(log x))⌋`, the number of
`m ≤ x` with `v_p(C(2m, m)) ≤ D / log D` for some prime `p ≤ 2K` is `o(x)` as `x → ∞`
(counted over `1 ≤ m ≤ x`).

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
/-- Lemma 5: with `D = D_p` and `K` as in Lemma 4, the number of `m ≤ x` such that
`max {v_p(m + i) : 1 ≤ i ≤ K} > D / log D` for some prime `p < 2K` is `o(x)` as `x → ∞`
(counted over `1 ≤ m ≤ x`).

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

/-- Theorem 2: the set of `m` such that `C(m + k, k)` divides `C(2m, m)` for every positive
integer `k ≤ exp(0.8 √(log m))` has natural density `1`. The divisibility sign, lost in the
extracted display, is read from the paper.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Theorem 2 (`integers-2026-A47-thm-2`). -/
public theorem_wanted choose_dvd_centralBinom_density_one :
    ({m : ℕ | ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.exp (0.8 * Real.sqrt (Real.log m)) →
        (m + k).choose k ∣ centralBinom m} : Set ℕ).HasDensity 1

end

end MetaMathlibExt
