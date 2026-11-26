/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.RegularTripartitionCongruences
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Congruences modulo 3 and 6 for 2-regular tripartitions

Modulo 3, the cube of the single-partition series is supported in degrees divisible by 3.
Modulo 2, the single-partition series is Euler's product, so Jacobi's identity gives the
support of its cube. This proves the congruences without a three-dissection.

## References

* Mohammed L. Nadji and Moussa Ahmia, *Congruences for ℓ-Regular Tripartitions for ℓ ∈ {2, 3}*,
  INTEGERS 24 (2024), Article A86, pp. 1–12, equations (1), (2), (9) and Corollary 1.
* Bruce C. Berndt, *Number Theory in the Spirit of Ramanujan*, American Mathematical Society,
  2006, Theorem 1.3.9 (Jacobi's cube identity, cited in equation (2) above).
* J. W. L. Glaisher, *A theorem in partitions*, Messenger of Mathematics 12 (1883),
  pp. 158–170 (equivalence of parts restricted by divisibility and by multiplicity).
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

private def twoRegularPartitionSeries (R : Type*) [CommSemiring R] : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ ((Nat.Partition.countRestricted n 2).card : R)

private theorem coeff_twoRegularPartitionSeries_cube (R : Type*) [CommSemiring R] (n : ℕ) :
    coeff n (twoRegularPartitionSeries R ^ 3) = (regularTripartitionCount 2 n : R) := by
  rw [pow_succ', pow_two, coeff_mul]
  simp only [twoRegularPartitionSeries, coeff_mk, coeff_mul, Finset.mul_sum, mul_assoc,
    regularTripartitionCount, Nat.cast_sum, Nat.cast_mul,
    Nat.Partition.card_restricted_eq_card_countRestricted _ (by decide : 0 < 2)]

-- Frobenius sends each degree to three times that degree, as in the cyclic rotation of triples.
private theorem three_dvd_twoRegularTripartitionCount {n : ℕ} (hn : ¬ 3 ∣ n) :
    3 ∣ regularTripartitionCount 2 n := by
  apply (ZMod.natCast_eq_zero_iff _ 3).mp
  rw [← coeff_twoRegularPartitionSeries_cube, ← map_frobenius_expand 3 (by decide), coeff_map,
    coeff_expand_of_not_dvd _ _ _ hn, map_zero]

-- Glaisher's product has a factor 1 + X^(i+1) for each part size, equal to 1 - X^(i+1) mod 2.
private theorem twoRegularPartitionSeries_zmod_two :
    twoRegularPartitionSeries (ZMod 2) =
      PowerSeries.map (Int.castRingHom (ZMod 2)) (pentagonalSeries ℤ) := by
  let : TopologicalSpace (ZMod 2) := ⊥
  have : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hφ : Continuous (φ : ℤ⟦X⟧ → (ZMod 2)⟦X⟧) :=
    continuous_pi fun d ↦ (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ZMod 2))).comp
      (continuous_apply d)
  have heuler := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map φ hφ
  have hneg : (-1 : (ZMod 2)⟦X⟧) = 1 := by
    simpa only [map_neg, map_one] using
      congrArg (C (R := ZMod 2)) (show (-1 : ZMod 2) = 1 by decide)
  have hsub (x : (ZMod 2)⟦X⟧) : 1 - x = 1 + x := by
    rw [sub_eq_add_neg, ← neg_one_mul x, hneg, one_mul]
  simp only [Function.comp_def, φ, map_sub, map_one, map_pow, map_X, hsub] at heuler
  have hparts := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2)
    (m := 2) (by decide)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_zero, mul_one, pow_zero,
    zero_add] at hparts
  exact hparts.unique heuler

private theorem two_dvd_twoRegularTripartitionCount (n : ℕ) :
    2 ∣ regularTripartitionCount 2 (3 * n + 2) := by
  have htriangle (t : ℕ) : (t + 1).choose 2 ≠ 3 * n + 2 := by
    intro ht
    have h := two_mul_choose_two_succ t
    rw [ht] at h
    have hm := congrArg (· % 3) h
    rw [Nat.mul_mod t (t + 1), Nat.add_mod t 1] at hm
    have hr : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases hr with hr | hr | hr <;> rw [hr] at hm <;> omega
  apply (ZMod.natCast_eq_zero_iff _ 2).mp
  rw [← coeff_twoRegularPartitionSeries_cube, twoRegularPartitionSeries_zmod_two,
    ← map_pow, pentagonalSeries_pow_three, coeff_map, coeff_jacobiCubeSeries_eq_zero htriangle,
    map_zero]

/-- **Congruences modulo 3 and 6 for 2-regular tripartitions.** Let $T_2(m)$ be the number of
$2$-regular tripartitions of $m$. For every natural number $n$, $3 \mid T_2(3n + 1)$ and
$6 \mid T_2(3n + 2)$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 1. -/
public theorem regularTripartitionCount_two_mod_three_six (n : ℕ) :
    3 ∣ regularTripartitionCount 2 (3 * n + 1) ∧ 6 ∣ regularTripartitionCount 2 (3 * n + 2) := by
  refine ⟨three_dvd_twoRegularTripartitionCount (by omega), ?_⟩
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd
    (two_dvd_twoRegularTripartitionCount n) (three_dvd_twoRegularTripartitionCount (by omega))

end MetaMathlibExt
