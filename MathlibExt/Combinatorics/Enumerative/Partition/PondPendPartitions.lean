/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-!
# POND and PEND partitions

This file defines the two partition counts and proves Sellers' Euler product formula for the
generating function of PEND partitions.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **The POND condition.** A multiset $s$ of natural numbers (the parts of a partition)
satisfies the POND condition when no odd number occurs in $s$ exactly once; equivalently,
every odd part that occurs in $s$ has multiplicity at least $2$, so the odd parts are not
distinct.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def IsPondParts (s : Multiset ℕ) : Prop :=
  ∀ i ∈ s, Odd i → s.count i ≠ 1

/-- **The PEND condition.** A multiset $s$ of natural numbers (the parts of a partition)
satisfies the PEND condition when no even number occurs in $s$ exactly once; equivalently,
every even part that occurs in $s$ has multiplicity at least $2$, so the even parts are not
distinct.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def IsPendParts (s : Multiset ℕ) : Prop :=
  ∀ i ∈ s, Even i → s.count i ≠ 1

instance instDecidablePredMultisetNatIsPondParts : DecidablePred IsPondParts := fun s => by
  unfold IsPondParts
  infer_instance

instance instDecidablePredMultisetNatIsPendParts : DecidablePred IsPendParts := fun s => by
  unfold IsPendParts
  infer_instance

/-- **Number of POND partitions.** For a natural number $n$, $\mathrm{pond}(n)$ is the number of
partitions of $n$ that are POND, that is, in which every odd part that occurs has multiplicity
at least $2$ (OEIS A265256).

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def pondCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter fun p => IsPondParts p.parts).card

/-- **The PEND partition function.** For a natural number $n$, $\mathrm{pend}(n)$ is the number
of PEND partitions of $n$: partitions of $n$ in which every even part that occurs appears at
least twice (OEIS A265254).

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
def pendCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter fun p => IsPendParts p.parts).card

/-- **The number of POND partitions of zero.** The number $\mathrm{pond}(0)$ of POND
partitions of $0$ equals $1$: the only partition of $0$ is the empty partition, and it is POND.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1 (OEIS A265256). -/
theorem pondCount_zero : pondCount 0 = 1 := by
  decide

/-- **PEND partitions of zero.** The number of PEND partitions of $0$ is $1$, that is,
$\mathrm{pend}(0) = 1$.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1 (OEIS A265254). -/
theorem pendCount_zero : pendCount 0 = 1 := by
  decide

/-- **Examples of POND and PEND parts.** The multisets of parts $\{1, 1\}$ and $\{2\}$ satisfy
the POND condition, while $\{1\}$ and $\{2, 1\}$ do not; the multisets $\{1\}$ and $\{2, 2\}$
satisfy the PEND condition, while $\{2\}$ and $\{2, 4\}$ do not.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Section 1. -/
theorem isPondParts_isPendParts_examples :
    IsPondParts {1, 1} ∧ ¬ IsPondParts {1} ∧ ¬ IsPondParts {2, 1} ∧ IsPondParts {2} ∧
      IsPendParts {1} ∧ IsPendParts {2, 2} ∧ ¬ IsPendParts {2} ∧ ¬ IsPendParts {2, 4} := by
  decide

end

local notation "𝔣" => qEulerProduct

namespace pendCount_generatingFunction

private def weight (i c : ℕ) : ℤ := if Even i → c ≠ 1 then 1 else 0

private theorem genFun_eq :
    Nat.Partition.genFun weight = PowerSeries.mk fun n => (pendCount n : ℤ) := by
  ext n
  simp_rw [Nat.Partition.coeff_genFun, Finsupp.prod, weight, Finset.prod_boole]
  simp [pendCount, IsPendParts]

private theorem hasProd_euler (k : ℕ) (hk : 0 < k) :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (i + 1))) (𝔣 k) := by
  suffices Multipliable (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (i + 1))) from this.hasProd
  simp_rw [sub_eq_add_neg]
  apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp only [order_neg, order_X_pow]
  exact ENat.tendsto_natCast_nhds_top.comp <| Filter.tendsto_atTop_mono
    (fun i => Nat.le_mul_of_pos_left (i + 1) hk) (Filter.tendsto_add_atTop_nat 1)

-- The factor for a part of size i + 1 is geometric, with its linear term
-- removed exactly when the part is even.
private theorem hasProd_correction :
    HasProd (fun i : ℕ => if Even (i + 1) then
      1 - (X : ℤ⟦X⟧) ^ (i + 1) + (X ^ (i + 1)) ^ 2 else 1)
      (𝔣 1 * (PowerSeries.mk fun n => (pendCount n : ℤ))) := by
  rw [← genFun_eq]
  have heuler := hasProd_euler 1 (by decide)
  simp only [one_mul] at heuler
  apply (heuler.mul (Nat.Partition.hasProd_genFun weight)).congr_fun
  intro i
  let y : ℤ⟦X⟧ := X ^ (i + 1)
  let omitted := if Even (i + 1) then y else 0
  have hy : y.constantCoeff = 0 := by simp [y]
  have hs := WithPiTopology.summable_pow_of_constantCoeff_eq_zero hy
  have h := hs.hasSum.sub (hasSum_ite_eq (1 : ℕ) omitted)
  have hfactor : 1 + ∑' j : ℕ, weight (i + 1) (j + 1) • y ^ (j + 1) =
      (∑' j : ℕ, y ^ j) - omitted := by
    rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
    simp only [pow_zero, Nat.zero_ne_one, ite_false, sub_zero]
    congr 1
    apply tsum_congr
    intro j
    by_cases he : Even (i + 1) <;> cases j <;> simp [weight, omitted, he]
  simp only [pow_mul]
  change (if Even (i + 1) then 1 - y + y ^ 2 else 1) =
    (1 - y) * (1 + ∑' j : ℕ, weight (i + 1) (j + 1) • y ^ (j + 1))
  rw [hfactor, mul_sub, mul_comm (1 - y) (∑' j : ℕ, y ^ j),
    WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hy]
  by_cases he : Even (i + 1) <;> simp [omitted, he]
  ring

-- Index the product for f_(2k) by all positive part sizes, with factor 1 at odd sizes.
private theorem hasProd_evenEuler (k : ℕ) (hk : 0 < k) :
    HasProd (fun i : ℕ => if Even (i + 1) then 1 - ((X : ℤ⟦X⟧) ^ (i + 1)) ^ k else 1)
      (𝔣 (2 * k)) := by
  rw [← one_mul (𝔣 (2 * k))]
  apply HasProd.even_mul_odd
  · apply hasProd_one.congr_fun
    intro i
    simp [parity_simps]
  · apply (hasProd_euler (2 * k) (by omega)).congr_fun
    intro i
    rw [ite_eq_left (show Even (2 * i + 1 + 1) from ⟨i + 1, by omega⟩), ← pow_mul]
    ring_nf

end pendCount_generatingFunction

open pendCount_generatingFunction in
/-- **Generating function for PEND partitions.** Let $\mathrm{pend}(n)$ be the number of PEND
partitions of $n$, and let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series
in $q$, $f_1 f_4 f_6 \sum_{n \ge 0} \mathrm{pend}(n) q^n = f_2 f_{12}$. This is the identity
$\sum_{n \ge 0} \mathrm{pend}(n) q^n = f_2 f_{12} / (f_1 f_4 f_6)$ with the denominator cleared.

Source: James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*,
Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 18
(`jis-2024-24.4.7-thm-18`). -/
public theorem pendCount_generatingFunction :
    𝔣 1 * 𝔣 4 * 𝔣 6 * (PowerSeries.mk fun n => (pendCount n : ℤ)) =
      𝔣 2 * 𝔣 12 := by
  have lhs := (hasProd_correction.mul (hasProd_evenEuler 2 (by decide))).mul
    (hasProd_evenEuler 3 (by decide))
  have rhs := (hasProd_evenEuler 1 (by decide)).mul (hasProd_evenEuler 6 (by decide))
  rw [mul_right_comm (𝔣 1 * 𝔣 4), mul_right_comm (𝔣 1)]
  apply HasProd.unique lhs
  apply rhs.congr_fun
  intro i
  by_cases he : Even (i + 1) <;> simp [he]
  ring

end MetaMathlibExt
