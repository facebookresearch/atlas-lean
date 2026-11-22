/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

/-!
# The Euler products `f_k = (q^k; q^k)_∞`

The integer power series `f_k = ∏_{m ≥ 1} (1 - q^{k m})`, the standard shorthand of partition
congruence papers, as an infinite product in the coefficientwise topology.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 2.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **The Euler products of partition theory.** For a natural number $k$, the Euler product
$f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$ is this infinite product in the ring of
integer power series in $q$, taken in the coefficientwise topology. It is used for $k \ge 1$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 2. -/
noncomputable def qEulerProduct (k : ℕ) : ℤ⟦X⟧ :=
  ∏' m : ℕ, (1 - X ^ (k * (m + 1)))

/-- **Pentagonal series expansion of the first Euler product.** The Euler product
$f_1 = \prod_{m \ge 1} (1 - q^m)$ equals the pentagonal series
$\sum_{j \in \mathbb{Z}} (-1)^j q^{j(3j-1)/2}$ as an integer power series.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 2. -/
theorem qEulerProduct_one : qEulerProduct 1 = pentagonalSeries ℤ := by
  simp only [qEulerProduct, one_mul]
  exact WithPiTopology.tprod_one_sub_X_pow ℤ

/-- **Constant term of the Euler products.** For every natural number $k \ge 1$, the integer power
series $f_k = \prod_{m \ge 1} (1 - q^{km})$ has constant coefficient $1$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1
(notation `E_k`); James A. Sellers, *Elementary Proofs of Congruences for POND and PEND
Partitions*, Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 2. -/
theorem constantCoeff_qEulerProduct {k : ℕ} (hk : 1 ≤ k) :
    constantCoeff (qEulerProduct k) = 1 := by
  have hmul : Multipliable fun m : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (m + 1)) := by
    simp_rw [sub_eq_add_neg]
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    rw [order_neg, order_X_pow]
    norm_cast
    nlinarith
  rw [qEulerProduct, hmul.map_tprod _ (WithPiTopology.continuous_constantCoeff ℤ)]
  have h1 : ∀ m : ℕ, constantCoeff ((1 : ℤ⟦X⟧) - X ^ (k * (m + 1))) = 1 := fun m => by
    have : k * (m + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero m)
    simp [zero_pow this]
  simp [h1]

end

end MetaMathlibExt
