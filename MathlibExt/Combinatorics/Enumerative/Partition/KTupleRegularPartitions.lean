/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Tuples of regular partitions

The tuple-count recurrence gives powers of the single-partition generating series.
Modulo two, the series for 2-regular partitions equals the first Euler product,
whose cube has odd coefficients exactly at triangular indices.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Number of $\ell$-regular partitions.** For natural numbers $\ell$ and $n$, the number of
$\ell$-regular partitions of $n$ is the number of partitions of $n$ none of whose parts is
divisible by $\ell$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction
(definition of ℓ-regular partitions).
-/
public def lRegularPartitionCount (ℓ n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p => ∀ a ∈ p.parts, ¬ ℓ ∣ a).card

/-- **Number of $k$-tuples of $\ell$-regular partitions.** For natural numbers $\ell$, $k$ and
$n$, the number $T_{\ell,k}(n)$ is defined by recursion on $k$: $T_{\ell,0}(n)$ is $1$ if
$n = 0$ and $0$ otherwise, and
$$T_{\ell,k+1}(n) = \sum_{i=0}^{n} r_\ell(i) \, T_{\ell,k}(n-i),$$
where $r_\ell(i)$ is the number of $\ell$-regular partitions of $i$.

Peeling off the first component in this way, $T_{\ell,k}(n)$ counts the $k$-tuples
$(\lambda_1, \dots, \lambda_k)$ of $\ell$-regular partitions of $n_1, \dots, n_k$ with
$n_1 + \dots + n_k = n$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction
(definition of `T_{ℓ,k}`).
-/
public def kTupleRegularPartitionCount (ℓ : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ Finset.range (n + 1),
      lRegularPartitionCount ℓ i * kTupleRegularPartitionCount ℓ k (n - i)

/-- **The empty tuple of $\ell$-regular partitions.** For all natural numbers $\ell$ and $n$,
writing $T_{\ell,k}(n)$ for the number of $k$-tuples of $\ell$-regular partitions with total
$n$, we have $T_{\ell,0}(n) = 1$ if $n = 0$ and $T_{\ell,0}(n) = 0$ otherwise.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction
(definition of `T_{ℓ,k}`).
-/
public theorem kTupleRegularPartitionCount_zero (ℓ n : ℕ) :
    kTupleRegularPartitionCount ℓ 0 n = if n = 0 then 1 else 0 := rfl

/-- **Recurrence for tuples of $\ell$-regular partitions.** For all natural numbers $\ell$, $k$
and $n$, writing $r_\ell(i)$ for the number of $\ell$-regular partitions of $i$ and
$T_{\ell,k}(n)$ for the number of $k$-tuples of $\ell$-regular partitions with total $n$,
$$T_{\ell,k+1}(n) = \sum_{i=0}^{n} r_\ell(i) \, T_{\ell,k}(n-i).$$

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction
(definition of `T_{ℓ,k}`).
-/
public theorem kTupleRegularPartitionCount_succ (ℓ k n : ℕ) :
    kTupleRegularPartitionCount ℓ (k + 1) n = ∑ i ∈ Finset.range (n + 1),
      lRegularPartitionCount ℓ i * kTupleRegularPartitionCount ℓ k (n - i) := rfl

/--
**Triples of $\ell$-regular partitions.** For natural numbers $\ell$ and $n$,
$T_\ell(n) = T_{\ell,3}(n)$ is the number of triples $(\lambda_1, \lambda_2, \lambda_3)$ of
$\ell$-regular partitions (partitions with no part divisible by $\ell$) whose sizes add up to
$n$.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition
of `T_ℓ`).
-/
public def tripleRegularPartitionCount (ℓ n : ℕ) : ℕ :=
  kTupleRegularPartitionCount ℓ 3 n

/-- **Zero has one $\ell$-regular partition.** For every natural number $\ell$, the number of
$\ell$-regular partitions of $0$ is $1$; the only one is the empty partition.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction
(definition of ℓ-regular partitions).
-/
public theorem lRegularPartitionCount_zero (ℓ : ℕ) : lRegularPartitionCount ℓ 0 = 1 := by
  simp [lRegularPartitionCount]

/-- **One tuple of $\ell$-regular partitions of total zero.** For all natural numbers $\ell$
and $k$, writing $T_{\ell,k}(n)$ for the number of $k$-tuples of $\ell$-regular partitions
with total $n$, we have $T_{\ell,k}(0) = 1$: the only such tuple of total $0$ is the tuple of
empty partitions.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction
(definition of `T_{ℓ,k}`).
-/
public theorem kTupleRegularPartitionCount_at_zero (ℓ k : ℕ) :
    kTupleRegularPartitionCount ℓ k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [kTupleRegularPartitionCount, lRegularPartitionCount_zero, ih]

end

private def lRegularSeries (R : Type*) [Semiring R] (ℓ : ℕ) : PowerSeries R :=
  mk fun n => (lRegularPartitionCount ℓ n : R)

private theorem coeff_lRegularSeries_pow (R : Type*) [Semiring R] (ℓ k n : ℕ) :
    coeff n (lRegularSeries R ℓ ^ k) = (kTupleRegularPartitionCount ℓ k n : R) := by
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 0 <;> simp [coeff_one, kTupleRegularPartitionCount_zero, hn]
  | succ k ih =>
    rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      kTupleRegularPartitionCount_succ, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ih, Nat.cast_mul, lRegularSeries, coeff_mk]

-- By Glaisher's identity the odd-part series has one factor `1 + X ^ (i + 1)` per size.
private theorem qEulerProduct_one_mul_twoRegularSeries :
    qEulerProduct 1 * lRegularSeries ℤ 2 = qEulerProduct 2 := by
  have hparts : HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) + X ^ (i + 1)) (lRegularSeries ℤ 2) := by
    change HasProd _ (mk fun n => ((Nat.Partition.restricted n (¬ 2 ∣ ·)).card : ℤ))
    simpa only [Nat.Partition.card_restricted_eq_card_countRestricted _ (by decide : 0 < 2),
      Finset.sum_range_succ, Finset.sum_range_zero, mul_zero, mul_one, pow_zero, pow_one,
      zero_add] using (Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℤ (m := 2)
        (by decide))
  have hprod := (WithPiTopology.hasProd_one_sub_X_pow ℤ).mul hparts
  rw [qEulerProduct_one, qEulerProduct]
  refine (hprod.congr_fun fun i => ?_).tprod_eq.symm
  rw [mul_comm 2 (i + 1), pow_mul]
  ring

private theorem twoRegularSeries_mod_two :
    lRegularSeries (ZMod 2) 2 = map (Int.castRingHom (ZMod 2)) (qEulerProduct 1) := by
  let φ := map (Int.castRingHom (ZMod 2))
  change lRegularSeries (ZMod 2) 2 = φ (qEulerProduct 1)
  have hEuler : φ (qEulerProduct 1 ^ 2) = φ (qEulerProduct 2) := by
    ext n
    simp only [φ, coeff_map, Int.coe_castRingHom]
    exact (ZMod.intCast_eq_intCast_iff _ _ 2).mpr (by
      simpa using qEulerProduct_iterated_primePower_congruence 2 1 1 1 1
        Nat.prime_two (by decide) (by decide) (by decide) (by decide) n)
  have hparts : φ (lRegularSeries ℤ 2) = lRegularSeries (ZMod 2) 2 := by
    ext n
    simp [φ, lRegularSeries]
  have hunit : IsUnit (qEulerProduct 1) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qEulerProduct (le_refl 1)]
    exact isUnit_one
  apply (hunit.map φ).mul_left_cancel
  rw [← hparts, ← map_mul, qEulerProduct_one_mul_twoRegularSeries, ← hEuler, map_pow, pow_two]

/--
**Parity of triples of 2-regular partitions.** For a natural number $n$, let $T_2(n)$ be the
number of triples of $2$-regular partitions (partitions with no even part) whose sizes add up to
$n$. Then $T_2(n)$ is odd if and only if $n$ is a triangular number, that is, $n = m(m+1)/2$
for some natural number $m$.

Allowing integer $m$ gives no new values, since $m$ and $-m-1$ give the same triangular number.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 8.
-/
public theorem tripleTwo_odd_iff_triangular (n : ℕ) :
    tripleRegularPartitionCount 2 n % 2 = 1 ↔ ∃ m : ℕ, n = m * (m + 1) / 2 := by
  have hseries :
      lRegularSeries (ZMod 2) 2 ^ 3 = map (Int.castRingHom (ZMod 2)) jacobiCubeSeries := by
    rw [twoRegularSeries_mod_two, ← map_pow, qEulerProduct_one, pentagonalSeries_pow_three]
  have hcoeff := congrArg (coeff n) hseries
  rw [coeff_lRegularSeries_pow, coeff_map] at hcoeff
  change (tripleRegularPartitionCount 2 n : ZMod 2) =
    (coeff (R := ℤ) n jacobiCubeSeries : ZMod 2) at hcoeff
  have hcast : (tripleRegularPartitionCount 2 n : ZMod 2) = 1 ↔
      tripleRegularPartitionCount 2 n % 2 = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff' (tripleRegularPartitionCount 2 n) 1 2)
  rw [← hcast, hcoeff]
  suffices h : (coeff (R := ℤ) n jacobiCubeSeries : ZMod 2) = 1 ↔
      ∃ m : ℕ, n = (m + 1).choose 2 by
    simpa only [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm] using h
  constructor
  · intro h
    by_contra! hnone
    rw [coeff_jacobiCubeSeries_eq_zero (fun m hm => hnone m hm.symm), Int.cast_zero] at h
    exact zero_ne_one h
  · rintro ⟨m, rfl⟩
    rw [coeff_jacobiCubeSeries_triangle]
    have hneg : (-1 : ZMod 2) = 1 := by decide
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [hneg, htwo]

end MetaMathlibExt
