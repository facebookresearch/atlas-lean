/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! # Thinned Wallis-type prime products modulo `2^m`

Statement-only requests from Mike Winkler, *Thinned Wallis-Type Prime Products in Residue
Classes Modulo 2^m*, INTEGERS 26 (2026), Article A90. Following the source
(arXiv:2602.13371v4, abstract and Sections 1–4): for an odd prime `p`,
`A(p) = (p - χ₄(p))/(p + χ₄(p))` with `χ₄ = ZMod.χ₄`; for `q = 2^m`, `m ≥ 2`, and a set
`S` of reduced residues modulo `q`, `P_S(x) = ∏_{p ≤ x, p mod q ∈ S} A(p)` over primes;
`μ(S) = ∑_{a ∈ S} χ₄(a)`, where `χ₄(a)` is `χ₄` of the reduction of `a` modulo `4`. Since
every element of `S` is a unit and `2` is not a unit modulo `2^m`, the product only
involves odd primes.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- For every odd prime `p`, `A(p) = (p - χ₄(p))/(p + χ₄(p)) = (1 - χ₄(p)/p)²/(1 - 1/p²)`.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Lemma 1 (`integers-2026-A90-lem-1`). -/
public theorem_wanted wallis_prime_factor_eq
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)) =
      (1 - (ZMod.χ₄ (p : ZMod 4) : ℝ) / p) ^ 2 / (1 - 1 / (p : ℝ) ^ 2)

/-- For `q = 2^m` with `m ≥ 2` and a set `S` of reduced residues modulo `q`, there is
`K(q, S) ∈ (0, ∞)` with `P_S(x) = K(q, S) (log x)^{-2μ(S)/φ(q)} (1 + o(1))` as `x → ∞`.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Theorem 1 (`integers-2026-A90-thm-1`). -/
public theorem_wanted thinned_wallis_prime_product_asymptotic
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun x : ℝ =>
          (∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
            ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) /
            (K * Real.log x ^
              (-2 * ((∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) /
                (Nat.totient (2 ^ m) : ℝ))))
        atTop (𝓝 1)

/-- With the notation of Theorem 1, `lim_{x → ∞} P_S(x)` exists in `(0, ∞)` if and only if
`μ(S) = 0`.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Corollary 1 (`integers-2026-A90-cor-1`). -/
public theorem_wanted thinned_wallis_prime_product_tendsto_pos_iff
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a) :
    (∃ L : ℝ, 0 < L ∧
        Tendsto (fun x : ℝ =>
            ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
                (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
              ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
          atTop (𝓝 L)) ↔
      ∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) = 0

/-- With `C(q, a) = lim_{x → ∞} (log x)^{1/φ(q)} ∏_{p ≤ x, p ≡ a (q)} (1 - 1/p)` and
`D(q, a) = ∏_{p ≡ a (q)} (1 - 1/p²)`, for every set `S` of reduced residues modulo
`q = 2^m`, `P_S(x) = (∏_{a ∈ S} (C(q, a)²/D(q, a))^{χ₄(a)}) (log x)^{-2μ(S)/φ(q)} (1 + o(1))`;
in particular `K(q, S) = ∏_{a ∈ S} (C(q, a)²/D(q, a))^{χ₄(a)}`, and if `μ(S) = 0` then
`lim P_S(x)` equals this product. The constants `C(q, a)` and `D(q, a)` enter through
hypotheses stating the defining limits.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Theorem 2 (`integers-2026-A90-thm-2`). -/
public theorem_wanted thinned_wallis_prime_product_constant
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a)
    (C D : ZMod (2 ^ m) → ℝ)
    (hC : ∀ a ∈ S, Tendsto (fun x : ℝ =>
        Real.log x ^ (1 / (Nat.totient (2 ^ m) : ℝ)) *
          ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a), (1 - 1 / (p : ℝ)))
        atTop (𝓝 (C a)))
    (hD : ∀ a ∈ S, Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a), (1 - 1 / (p : ℝ) ^ 2))
        atTop (𝓝 (D a))) :
    Tendsto (fun x : ℝ =>
        (∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) /
          ((∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ ((a.val : ℕ) : ZMod 4)) *
            Real.log x ^
              (-2 * ((∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) /
                (Nat.totient (2 ^ m) : ℝ))))
      atTop (𝓝 1) ∧
    (∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) = 0 →
      Tendsto (fun x : ℝ =>
          ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
            ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
        atTop (𝓝 (∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ ((a.val : ℕ) : ZMod 4))))

end

end MetaMathlibExt
