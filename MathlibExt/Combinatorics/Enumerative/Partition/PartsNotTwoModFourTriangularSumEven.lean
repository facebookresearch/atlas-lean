/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.ZMod
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Parity of a triangular sum of partitions with no part congruent to 2 modulo 4

Modulo two, Jacobi's cube identity identifies the triangular series with the cube of Euler's
pentagonal series. Multiplying by the generating function for the counts $P_2(m)$ gives $1$.
Its positive-degree coefficients give `MetaMathlibExt.partsNotTwoModFour_triangular_sum_even`.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

/-- **Partitions with no part congruent to 2 modulo 4.** For a natural number $n$, $P_2(n)$ is
the number of partitions of $n$ none of whose parts is congruent to $2$ modulo $4$.

Its generating function is $\sum_{n \ge 0} P_2(n) q^n = (q^2; q^4)_\infty / (q; q)_\infty$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `P_2(n)` before Theorem 11). -/
@[expose] public def partsNotTwoModFourCount (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n fun i => i % 4 ≠ 2).card

namespace partsNotTwoModFour_triangular_sum_even

private noncomputable abbrev pserZMod : (ZMod 2)⟦X⟧ :=
  PowerSeries.mk fun n => (partsNotTwoModFourCount n : ZMod 2)

private noncomputable abbrev triZMod : (ZMod 2)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 2)) jacobiCubeSeries

private theorem coeff_pserZMod (n : ℕ) :
    pserZMod.coeff n = (partsNotTwoModFourCount n : ZMod 2) :=
  PowerSeries.coeff_mk _ _

private theorem map_pentagonalSeries_zmod2 :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (pentagonalSeries ℤ) =
      pentagonalSeries (ZMod 2) := by
  ext n
  rw [PowerSeries.coeff_map]
  by_cases hn : ∃ k, pentagonal k = n
  · obtain ⟨k, rfl⟩ := hn
    simp [coeff_pentagonalSeries_pentagonal, Int.castRingHom, Int.negOnePow]
  · rw [coeff_pentagonalSeries_eq_zero ℤ (by simpa using hn),
      coeff_pentagonalSeries_eq_zero (ZMod 2) (by simpa using hn), map_zero]

/-- In characteristic two, `1 - F = 1 + F` for a power series `F`. -/
private theorem one_sub_eq_one_add (F : (ZMod 2)⟦X⟧) : 1 - F = 1 + F := by
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_neg, PowerSeries.coeff_one, sub_eq_add_neg, CharTwo.neg_eq]

/-- The geometric series times `1 + X ^ k` is `1` in characteristic two. -/
private theorem geom_mul_one_add {k : ℕ} (hk : k ≠ 0) :
    (∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ (k * j)) * (1 + X ^ k) = 1 := by
  have hconst : PowerSeries.constantCoeff (X ^ k : (ZMod 2)⟦X⟧) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow]
    simp [hk, eq_comm]
  have hgeom := WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hconst
  have hsum : (∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ (k * j)) =
      ∑' j : ℕ, (X ^ k : (ZMod 2)⟦X⟧) ^ j := by
    apply tsum_congr
    intro j
    rw [← pow_mul]
  rw [hsum]
  rw [← one_sub_eq_one_add (X ^ k)]
  exact hgeom

/-- Multiplying the restricted-partition series by the fourth power of Euler's product
cancels the factors at multiples of four, leaving the odd-part generating series. -/
private theorem pserZMod_mul_euler_fourth :
    pserZMod * pentagonalSeries (ZMod 2) ^ 4 = pentagonalSeries (ZMod 2) := by
  have hPser : HasProd
      (fun i => if (i + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j)
        else 1) pserZMod :=
    Nat.Partition.hasProd_powerSeriesMk_card_restricted (ZMod 2) (fun i => i % 4 ≠ 2)
  have hpent : HasProd (fun i => (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1))
      (pentagonalSeries (ZMod 2)) := by
    refine (WithPiTopology.hasProd_one_sub_X_pow (ZMod 2)).congr_fun fun i => ?_
    exact (one_sub_eq_one_add _).symm
  have hfourth : HasProd (fun i => (1 : (ZMod 2)⟦X⟧) + X ^ (4 * (i + 1)))
      (pentagonalSeries (ZMod 2) ^ 4) := by
    let : CharP (ZMod 2)⟦X⟧ 2 := charP_of_injective_ringHom C_injective 2
    refine (hpent.pow 4).congr_fun fun i => ?_
    rw [show 4 = 2 ^ 2 by rfl, add_pow_char_pow, one_pow, ← pow_mul, Nat.mul_comm]
  have hsqprod : HasProd
      (fun i => if 4 ∣ (i + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1) else 1)
      (pentagonalSeries (ZMod 2) ^ 4) := by
    have hinj : Function.Injective (fun n : ℕ => 4 * n + 3) := fun a b h => by
      dsimp only at h; omega
    have hside : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ => 4 * n + 3) →
        (if 4 ∣ (x + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (x + 1) else 1) = 1 := by
      intro x hx
      rw [ite_eq_right]
      intro hdvd
      obtain ⟨t, ht⟩ := hdvd
      apply hx
      refine ⟨t - 1, ?_⟩
      dsimp only
      omega
    have hcomp0 : HasProd (fun n : ℕ =>
        (if 4 ∣ ((4 * n + 3) + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ ((4 * n + 3) + 1)
          else 1)) (pentagonalSeries (ZMod 2) ^ 4) := by
      refine hfourth.congr_fun fun n => ?_
      have h4 : 4 ∣ ((4 * n + 3) + 1) := ⟨n + 1, by ring⟩
      rw [ite_eq_left h4]
      congr 1
    exact (hinj.hasProd_iff hside).mp hcomp0
  have hcomb : HasProd (fun i =>
      (if (i + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1) *
        (if 4 ∣ (i + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1) else 1))
      (pserZMod * pentagonalSeries (ZMod 2) ^ 4) :=
    hPser.mul hsqprod
  have hodd : HasProd (fun i => if ¬ Even (i + 1) then
      ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1)
      (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) :=
    Nat.Partition.hasProd_powerSeriesMk_card_restricted (ZMod 2) (fun i => ¬ Even i)
  have hodd' : HasProd (fun k => ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 1) * j))
      (pentagonalSeries (ZMod 2)) := by
    have hodd2 : HasProd (fun k => ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 1) * j))
        (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) := by
      have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by
        dsimp only at h; omega
      have hside : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ => 2 * n) →
          (if ¬ Even (x + 1) then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((x + 1) * j)
            else 1) = 1 := by
        intro x hx
        rw [ite_eq_right]
        intro hev
        apply hx
        exact ⟨x / 2, by
          change 2 * (x / 2) = x
          have h2 : (x + 1) % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hev)
          omega⟩
      have hcomp := (hinj.hasProd_iff hside).mpr hodd
      refine hcomp.congr_fun fun n => ?_
      simp only [Function.comp_def]
      rw [ite_eq_left (Nat.not_even_iff_odd.mpr ⟨n, rfl⟩ : ¬ Even (2 * n + 1))]
    have hdist : (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) =
        pentagonalSeries (ZMod 2) := by
      have hcard : (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) =
          PowerSeries.mk fun n => ((Nat.Partition.distincts n).card : ZMod 2) := by
        ext n
        simp [Nat.Partition.card_odds_eq_card_distincts]
      have hdistprod : HasProd (fun i => (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1))
          (PowerSeries.mk fun n => ((Nat.Partition.countRestricted n 2).card : ZMod 2)) := by
        refine (Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2)
          (by norm_num : 0 < 2)).congr_fun fun i => ?_
        simp [Finset.sum_range_succ]
      rw [hcard]
      simp only [← Nat.Partition.countRestricted_two]
      exact (hdistprod.tprod_eq.symm.trans hpent.tprod_eq)
    rw [hdist] at hodd2
    exact hodd2
  have heven : HasProd (fun k =>
      (if (2 * k + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 1) * j)
        else 1) *
        (if 4 ∣ (2 * k + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (2 * k + 1) else 1))
      (pentagonalSeries (ZMod 2)) := by
    refine hodd'.congr_fun fun k => ?_
    have hmod : (2 * k + 1) % 4 ≠ 2 := by omega
    have hdiv : ¬ 4 ∣ (2 * k + 1) := by omega
    rw [ite_eq_left hmod, ite_eq_right hdiv, mul_one]
  have hoddsub : HasProd (fun k =>
      (if (2 * k + 2) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 2) * j)
        else 1) *
        (if 4 ∣ (2 * k + 2) then (1 : (ZMod 2)⟦X⟧) + X ^ (2 * k + 2) else 1)) 1 := by
    refine hasProd_one.congr_fun fun k => ?_
    symm
    by_cases h4 : 4 ∣ (2 * k + 2)
    · have hmod : (2 * k + 2) % 4 ≠ 2 := by
        obtain ⟨t, ht⟩ := h4; omega
      rw [ite_eq_left hmod, ite_eq_left h4]
      exact (geom_mul_one_add (k := 2 * k + 2) (by omega)).symm
    · have hmod : (2 * k + 2) % 4 = 2 := by
        have h2 : 2 ∣ 2 * k + 2 := ⟨k + 1, by ring⟩
        omega
      rw [ite_eq_right (by omega : ¬ (2 * k + 2) % 4 ≠ 2), ite_eq_right h4, mul_one]
  have hsplit := HasProd.even_mul_odd (f := fun i =>
      (if (i + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1) *
        (if 4 ∣ (i + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1) else 1)) heven hoddsub
  have hval : (pentagonalSeries (ZMod 2)) * 1 =
      pserZMod * pentagonalSeries (ZMod 2) ^ 4 :=
    hsplit.tprod_eq.symm.trans hcomb.tprod_eq
  exact hval.symm.trans (mul_one _)

/-- The triangular series is the inverse of the restricted-partition series modulo two. -/
private theorem triZMod_mul_pserZMod : triZMod * pserZMod = 1 := by
  rw [triZMod, ← pentagonalSeries_pow_three, map_pow, map_pentagonalSeries_zmod2, mul_comm]
  have hE : pentagonalSeries (ZMod 2) ≠ 0 := by
    intro h
    have hc := congrArg (coeff (pentagonal 0)) h
    rw [coeff_pentagonalSeries_pentagonal, map_zero, Int.negOnePow_zero, Units.val_one] at hc
    exact one_ne_zero hc
  apply mul_right_cancel₀ hE
  simpa only [one_mul, mul_assoc, ← pow_succ] using pserZMod_mul_euler_fourth

private theorem choose_two_eq_triangular (k : ℕ) : (k + 1).choose 2 = k * (k + 1) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

private theorem triangular_strictMono : StrictMono (fun k : ℕ => k * (k + 1) / 2) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [← choose_two_eq_triangular, Nat.choose_succ_succ (k + 1) 1, Nat.choose_one_right]
  exact Nat.lt_add_of_pos_left (Nat.succ_pos k)

private theorem coeff_triZMod_triangle (k : ℕ) : triZMod.coeff (k * (k + 1) / 2) = 1 := by
  rw [← choose_two_eq_triangular, coeff_map, coeff_jacobiCubeSeries_triangle]
  simp [show (-1 : ZMod 2) = 1 by decide, show (2 : ZMod 2) = 0 by decide]

private theorem coeff_triZMod_eq_zero {i : ℕ} (hi : ∀ k : ℕ, k * (k + 1) / 2 ≠ i) :
    triZMod.coeff i = 0 := by
  rw [coeff_map, coeff_jacobiCubeSeries_eq_zero, map_zero]
  simpa only [choose_two_eq_triangular] using hi

end partsNotTwoModFour_triangular_sum_even

open partsNotTwoModFour_triangular_sum_even in
/-- **Parity of a triangular sum of partitions with no part congruent to 2 modulo 4.** Write
$P_2(m)$ for the number of partitions of $m$ with no part congruent to $2$ modulo $4$. For every
positive integer $n$, the sum $\sum_{k \ge 0,\ k(k+1)/2 \le n} P_2(n - k(k+1)/2)$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 3 (`integers-2026-A60-cor-3`). -/
public theorem partsNotTwoModFour_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      partsNotTwoModFourCount (n - k * (k + 1) / 2)) := by
  have h := congrArg (coeff n) triZMod_mul_pserZMod
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_one,
    ite_eq_right hn.ne'] at h
  change ∑ i ∈ Finset.range (n + 1), triZMod.coeff i * pserZMod.coeff (n - i) = 0 at h
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine (Finset.sum_of_injOn _ triangular_strictMono.injective.injOn ?_ ?_ ?_).trans h
  · intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
  · intro i hi hmiss
    rw [coeff_triZMod_eq_zero, zero_mul]
    rintro k rfl
    have hle := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact hmiss ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (triangular_strictMono.le_apply.trans hle)), hle⟩, rfl⟩
  · intro k _
    rw [coeff_triZMod_triangle, one_mul, coeff_pserZMod]

end MetaMathlibExt
