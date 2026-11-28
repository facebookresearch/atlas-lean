/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence

/-!
# Prime-power congruence for powers of Euler products

The coefficientwise congruence for powers of the Euler products `qEulerProduct`: for a
prime `p` and natural numbers `j, k, m ≥ 1`, the coefficients of `𝔣 m ^ (p ^ j * k)` agree
modulo `p ^ j` with those of `𝔣 (p * m) ^ (p ^ (j - 1) * k)`.

Statements from James A. Sellers, *Elementary Proofs of Congruences for POND and PEND
Partitions*, Journal of Integer Sequences 27 (2024), Article 24.4.7 (arXiv:2308.09999).
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Prime-power congruence for powers of Euler products.** Let $p$ be a prime, let
$j, k, m \ge 1$ be natural numbers, and let $f_m = \prod_{i \ge 1} (1 - q^{mi})$. Then for every
natural number $n$, the coefficient of $q^n$ in $f_m^{p^j k}$ is congruent modulo $p^j$ to the
coefficient of $q^n$ in $f_{pm}^{p^{j-1} k}$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 16
(`jis-2024-24.4.7-lem-16`). -/
public theorem qEulerProduct_pow_prime_pow_congruence (p j k m : ℕ) (hp : p.Prime)
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hm : 1 ≤ m) (n : ℕ) :
    coeff n (𝔣 m ^ (p ^ j * k)) ≡ coeff n (𝔣 (p * m) ^ (p ^ (j - 1) * k)) [ZMOD (p : ℤ) ^ j] := by
  have h := qEulerProduct_iterated_primePower_congruence p j m 1 k hp
    (by omega) (by omega) (by omega) hj n
  simpa only [pow_one, Nat.mul_comm m p, Nat.sub_add_cancel hj] using h

end

end MetaMathlibExt
