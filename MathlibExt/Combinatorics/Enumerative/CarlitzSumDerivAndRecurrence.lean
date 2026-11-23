/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivative and recurrence of the shifted alternating binomial power sums

Specializing the alternating binomial power sum to step one and translating its shift by one
gives the Carlitz sums.
-/

namespace MetaMathlibExt

/-- **Derivative and recurrence of the shifted alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$ and, for a complex number
$n$, let $c_{\ell,m}(n) = p_{\ell,m}(1, n + 1)$. For natural numbers $\ell, m \ge 1$ and every
complex number $n$, the complex derivative of $c_{\ell,m}$ at $n$ is $\ell\, c_{\ell-1,m}(n)$, and
$c_{\ell,m}(n) = (m + n + 1)\, c_{\ell-1,m}(n) - m\, c_{\ell-1,m-1}(n)$.

The variable $n$ is complex here because the paper differentiates in $n$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 4, Equation (3.38) (`integers-2024-A70-cor-4`). -/
public theorem carlitzSum_deriv_and_recurrence {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    (n : ℂ) :
    deriv (fun z => alternatingBinomialPowerSum ℓ m 1 (z + 1)) n =
        ℓ * alternatingBinomialPowerSum (ℓ - 1) m 1 (n + 1) ∧
      alternatingBinomialPowerSum ℓ m 1 (n + 1) =
        (m + n + 1) * alternatingBinomialPowerSum (ℓ - 1) m 1 (n + 1) -
          m * alternatingBinomialPowerSum (ℓ - 1) (m - 1) 1 (n + 1) := by
  constructor
  · rw [deriv_comp_add_const (alternatingBinomialPowerSum ℓ m 1)]
    exact (alternatingBinomialPowerSum_recurrences 1 (n + 1) ℓ m).2.2.2.2.2.1 hℓ
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓ)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    simpa [Nat.cast_succ, add_assoc] using
      (alternatingBinomialPowerSum_recurrences 1 (n + 1) d k).2.2.2.2.1

end MetaMathlibExt
