/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PadicValNat
public import MathlibExt.Analysis.Series.TwoAdicMultiples

/-!
# Truncated two-adic regrouping

`tsum_twoAdic_truncated_regroup` regroups a weighted series over the positive multiples
of a power of two, with the weight determined by the two-adic valuation of each index.
-/

namespace MetaMathlibExt

/-- **Truncated two-adic regrouping.** For every natural number $J$ and all sequences
$\varphi, c : \mathbb{N} \to \mathbb{C}$,
$$\sum_{j \ge J,\ n \ge 1} \varphi(j) c_{(2n-1) 2^j}
= \sum_{p \ge 1} \varphi(J + \nu_2(p)) c_{p 2^J},$$
where $\nu_2(p)$ is the exponent of the largest power of $2$ dividing $p$, the left side runs over
the pairs $(j, n)$ of natural numbers with $j \ge J$ and $n \ge 1$, the right side runs over the
positive integers $p$, and each side is an unconditional sum, taken to be $0$ when its family is
not summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 13, in sum form (`jis-2024-24.5.5-prop-13`). -/
public theorem tsum_twoAdic_truncated_regroup (J : ℕ) (φ c : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, φ (x.1 + J) * c ((2 * x.2 + 1) * 2 ^ (x.1 + J))
      = ∑' p : ℕ, φ (J + padicValNat 2 (p + 1)) * c ((p + 1) * 2 ^ J) := by
  have hval (j n : ℕ) : padicValNat 2 ((2 * n + 1) * 2 ^ j) = j := by
    exact congrArg Prod.fst (Nat.maxPowDvdDiv_of_pow_mul_eq (by positivity)
      (Nat.mul_comm (2 ^ j) (2 * n + 1)) (by omega))
  simpa only [Nat.add_zero, pow_zero, Nat.mul_one, hval, pow_add, Nat.mul_assoc,
    Nat.add_comm (padicValNat 2 _) J] using
    tsum_twoAdic_high_regroup 0 (fun p => φ (padicValNat 2 p + J) * c (p * 2 ^ J))

end MetaMathlibExt
