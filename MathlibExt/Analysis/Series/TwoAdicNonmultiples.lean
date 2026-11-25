/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.PadicValNat

/-!
# Regrouping the non-multiples of a power of two

The positive integers with two-adic valuation below `J` are exactly the non-multiples
of `2 ^ J`. The valuation and the odd part of each integer give the inverse reindexing.
-/

namespace MetaMathlibExt
namespace tsum_twoAdic_low_regroup

private theorem factor_odd_mul_pow (j n : ℕ) :
    Nat.maxPowDvdDiv 2 ((2 * n + 1) * 2 ^ j) = (j, 2 * n + 1) :=
  Nat.maxPowDvdDiv_of_pow_mul_eq (by positivity) (Nat.mul_comm _ _) (by omega)

/-- Factor a positive non-multiple of `2 ^ J` into a power of two and an odd part. -/
private def indexEquiv (J : ℕ) : Fin J × ℕ ≃ {p : ℕ // 0 < p ∧ ¬ 2 ^ J ∣ p} where
  toFun x := ⟨(2 * x.2 + 1) * 2 ^ (x.1 : ℕ), by positivity, by
    rw [Nat.pow_dvd_iff_le_multiplicity (by decide) (by positivity), ← Nat.padicValNat_def,
      padicValNat, factor_odd_mul_pow]
    exact Nat.not_le_of_lt x.1.isLt⟩
  invFun p := (⟨padicValNat 2 p, lt_of_not_ge fun h =>
    p.2.2 ((Nat.pow_dvd_iff_le_multiplicity (by decide) p.2.1.ne').2 (Nat.padicValNat_def ▸ h))⟩,
    p.val.divMaxPow 2 / 2)
  left_inv := by
    rintro ⟨j, n⟩
    simp [padicValNat, Nat.divMaxPow, factor_odd_mul_pow]
    omega
  right_inv := by
    intro p
    apply Subtype.ext
    have hodd := Nat.not_dvd_divMaxPow (p := 2) (by decide) p.2.1.ne'
    have h : 2 * (p.val.divMaxPow 2 / 2) + 1 = p.val.divMaxPow 2 := by omega
    exact (congrArg (· * 2 ^ padicValNat 2 p) h).trans (Nat.divMaxPow_mul_pow_padicValNat 2 p)

end tsum_twoAdic_low_regroup

/-- **Two-adic regrouping of the non-multiples of a power of two.** For every natural number $J$
and every sequence $c : \mathbb{N} \to \mathbb{C}$,
$$\sum_{0 \le j < J,\ n \ge 1} c_{(2n-1) 2^j} = \sum_{p \ge 1,\ 2^J \nmid p} c_p,$$
where the left side runs over the pairs $(j, n)$ of natural numbers with $j < J$ and $n \ge 1$,
the right side runs over the positive integers $p$ not divisible by $2^J$, and each side is an
unconditional sum, taken to be $0$ when its family is not summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 14, second display in sum form (`jis-2024-24.5.5-cor-14`). -/
public theorem tsum_twoAdic_low_regroup (J : ℕ) (c : ℕ → ℂ) :
    ∑' x : Fin J × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 : ℕ))
      = ∑' p : {p : ℕ // 0 < p ∧ ¬ 2 ^ J ∣ p}, c p := by
  exact (tsum_twoAdic_low_regroup.indexEquiv J).tsum_eq (fun p => c p)

end MetaMathlibExt
