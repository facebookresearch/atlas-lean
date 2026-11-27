/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Expand
import MathlibExt.Combinatorics.Enumerative.PentagonalNumber

/-!
# Partition convolution modulo three

The self-convolution of the partition numbers is congruent modulo three to a sum weighted
by Euler's pentagonal coefficients.
-/

namespace MetaMathlibExt

open PowerSeries

namespace partition_convolution_two_modEq_three

/-- In the product with a series in `X³`, only multiples of three contribute from that factor. -/
private theorem coeff_mul_expand_three (A B : ℤ⟦X⟧) (n : ℕ) :
    coeff n (A * expand 3 (by decide) B) =
      ∑ s ∈ Finset.range (n / 3 + 1), coeff (n - 3 * s) A * coeff s B := by
  rw [coeff_mul]
  symm
  apply Finset.sum_of_injOn (fun s : ℕ => (n - 3 * s, 3 * s))
  · intro i _ j _ h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) (congrArg Prod.snd h)
  · intro s hs
    apply Finset.mem_antidiagonal.mpr
    exact Nat.sub_add_cancel (by have := Finset.mem_range.mp hs; omega)
  · rintro ⟨i, j⟩ hij hout
    have hsum : i + j = n := Finset.mem_antidiagonal.mp hij
    have hj : ¬ 3 ∣ j := by
      rintro ⟨s, rfl⟩
      apply hout
      exact ⟨s, Finset.mem_range.mpr (by omega), Prod.ext (show n - 3 * s = i by omega) rfl⟩
    simp [coeff_expand_of_not_dvd 3 (by decide) B hj]
  · intro s _
    simp

end partition_convolution_two_modEq_three

/-- **Partition convolution modulo $3$.** Let $p(a)$ be the number of partitions of $a$, and let
$\omega(t)$ be the coefficient of $q^t$ in Euler's product $\prod_{m \ge 1} (1 - q^m)$. For every
integer $n \ge 0$,
$$\sum_{a + b = n} p(a)\, p(b) \equiv \sum_{0 \le s \le n/3} \omega(n - 3s)\, p(s) \pmod 3,$$
the left sum running over pairs $(a, b)$ of nonnegative integers and the right one over integers
$s$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Corollary 6 (`integers-2024-A39-cor-6`). -/
public theorem partition_convolution_two_modEq_three (n : ℕ) :
    (∑ x ∈ Finset.antidiagonal n,
        (Fintype.card (Nat.Partition x.1) : ℤ) * (Fintype.card (Nat.Partition x.2) : ℤ)) ≡
      ∑ s ∈ Finset.range (n / 3 + 1),
        PowerSeries.coeff (n - 3 * s) (PowerSeries.pentagonalSeries ℤ)
            * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD 3] := by
  let P := PowerSeries.mk (fun i => (partitionFunction i : ℤ))
  let E := pentagonalSeries ℤ
  let f := PowerSeries.map (Int.castRingHom (ZMod 3))
  have hPE : f P * f E = 1 := by
    rw [← map_mul]
    exact (congrArg f mk_partitionFunction_mul_pentagonalSeries).trans (map_one f)
  have hcube : expand 3 (by decide) (f P) = f P ^ 3 := by
    simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card (f P)
  have hseries : f (P * P) = f (E * expand 3 (by decide) P) := by
    rw [map_mul, map_mul, map_expand, hcube]
    calc
      f P * f P = (f P * f E) * (f P * f P) := by rw [hPE, one_mul]
      _ = f E * f P ^ 3 := by ring
  have hc := congrArg (coeff n) hseries
  rw [coeff_map, coeff_map, coeff_mul,
    partition_convolution_two_modEq_three.coeff_mul_expand_three] at hc
  simp only [P, coeff_mk] at hc
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).mp hc

end MetaMathlibExt
