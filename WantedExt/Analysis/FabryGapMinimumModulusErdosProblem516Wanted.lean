/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum modulus of entire functions with Fabry gaps (Erdős Problem 516)

Erdős Problem 516 (Pólya): if `f(z) = ∑ aₖ z ^ (nₖ)` is entire of finite order with `nₖ / k → ∞`, is
`limsup_{r → ∞} log m(r) / log M(r) = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Analysis.FabryGapMinimumModulusErdosProblem516Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #516, https://www.erdosproblems.com/516 (status PROVED
(LEAN)). UnsolvedMath record UM-30006913 (`EP-516`), dataset ulamai/UnsolvedMath v1.8.0.

Exponents are strictly increasing and coefficients nonzero (so `f` is transcendental and `M(r) →
∞`). Finite order: `|f(z)| ≤ C exp(|z| ^ ρ)`. Since `m(r) ≤ M(r)`, the ratio is at most `1` once
`M(r) > 1`, so the limsup statement is "for every `0 < ε < 1` there are arbitrarily large `r` with
`M(r) ^ (1 - ε) ≤ m(r)`", stated without `log` or `limsup`. Compared with the formal-conjectures
statement `ErdosProblems/516.lean` (equivalent; it uses `limsup` of a `log` ratio; no code
imported).
-/

/-- Erdős Problem 516 (Pólya): if `f(z) = ∑ₖ aₖ z ^ nₖ` is entire of finite order, with strictly
increasing exponents `nₖ`, nonzero coefficients and `nₖ / k → ∞`, then
`limsup_{r → ∞} log m(r) / log M(r) = 1`, where `m(r)` and `M(r)` are the minimum and maximum of
`|f|` on `|z| = r`. Unfolded: for every `0 < ε < 1` there are arbitrarily large `r` with
`M(r) ^ (1 - ε) ≤ m(r)`; the ratio is at most `1` once `M(r) > 1`. -/
def fabryGapMinModulusLimsup : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ), StrictMono n → (∀ k, a k ≠ 0) →
    Filter.Tendsto (fun k => (n k : ℝ) / k) Filter.atTop Filter.atTop →
    (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
    (∃ C ρ : ℝ, ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      ∀ z w : ℂ, ‖z‖ = r → ‖w‖ = r → ‖f w‖ ^ (1 - ε) ≤ ‖f z‖

/--
Resolved true: Fuchs (Theorem 1) proved that for every `ε > 0`, `log m(r) > (1 - ε) log M(r)` holds
outside a set of `r` of logarithmic density `0`, so at arbitrarily large `r`. Source: T. F. Bloom,
Erdős Problems, Problem #516, https://www.erdosproblems.com/516 (status PROVED (LEAN)); resolution:
W. H. J. Fuchs, Proof of a conjecture of G. Pólya concerning gap series, Illinois J. Math. 7 (1963),
661-667, Theorem 1: if f = ∑ c_n z^{λ_n} is entire of finite order and the increasing exponents
satisfy λ_n / n → ∞, then for every ε > 0, log L(r, f) > (1 - ε) log M(r, f) outside a set of r of
logarithmic density 0 (L the minimum modulus); erdosproblems.com/516,
https://doi.org/10.1215/ijm/1255645102.
-/
public theorem_wanted fabryGapMinModulusLimsup_holds : fabryGapMinModulusLimsup

end MathlibExt.Analysis.FabryGapMinimumModulusErdosProblem516Wanted
