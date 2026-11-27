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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Topology.Instances.ZMod
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Parity of the four-regular partition function

Glaisher's theorem allows us to count partitions with every multiplicity below four. Over
`ZMod 2` the generating series for such partitions is the cube of Euler's product, so Jacobi's
cube identity gives the parity of the count.
-/

namespace MetaMathlibExt

open PowerSeries
open scoped PowerSeries.WithPiTopology

private theorem fourRegularCount_cast_eq_coeff (n : ℕ) :
    ((Nat.Partition.restricted n (¬ 4 ∣ ·)).card : ZMod 2) =
      (↑(coeff n jacobiCubeSeries) : ZMod 2) := by
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hφ : Continuous (φ : ℤ⟦X⟧ → (ZMod 2)⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact (continuous_of_discreteTopology (f := Int.castRingHom (ZMod 2))).continuousAt.comp
      ((WithPiTopology.continuous_coeff ℤ k).continuousAt)
  have he := ((WithPiTopology.hasProd_one_sub_X_pow ℤ).pow 3).map φ hφ
  simp only [φ, Function.comp_def, map_pow, map_sub, map_one, map_X,
    pentagonalSeries_pow_three] at he
  have : CharP (ZMod 2)⟦X⟧ 2 := CharP.of_ringHom_of_ne_zero C 2 (by decide)
  -- Multiplying the geometric factor by 1 - X^(i+1) exposes Frobenius at exponent four.
  have geom (i : ℕ) : ∑ j ∈ Finset.range 4, (X ^ (i + 1) : (ZMod 2)⟦X⟧) ^ j =
      (1 - X ^ (i + 1)) ^ 3 := by
    have hne : (1 : (ZMod 2)⟦X⟧) ≠ X ^ (i + 1) := fun h => by
      simpa using congrArg constantCoeff h
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    rw [geom_sum_mul_neg, ← pow_succ]
    have h := (sub_pow_expChar_pow (p := 2) (1 : (ZMod 2)⟦X⟧) (X ^ (i + 1)) 2).symm
    rw [show (2 : ℕ) ^ 2 = 4 by decide, one_pow] at h
    exact h
  have hc := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2) (m := 4) (by decide)
  simp_rw [pow_mul, geom] at hc
  rw [Nat.Partition.card_restricted_eq_card_countRestricted n (by decide : 0 < 4)]
  simpa only [coeff_mk, coeff_map, Int.coe_castRingHom] using congrArg (coeff n) (hc.unique he)

private theorem choose_two_succ_eq_triangle (m : ℕ) : (m + 1).choose 2 = m * (m + 1) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (m + 1) m]

/-- **Parity of the $4$-regular partition function.** For a positive integer $n$, let $R_4(n)$ be
the number of partitions of $n$ with no part divisible by $4$. Then $R_4(n)$ is odd if and only if
$n$ is a triangular number, that is, $n = m(m + 1)/2$ for some integer $m \ge 0$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 3 (`integers-2024-A39-thm-3`). -/
public theorem odd_card_four_regular_iff_triangular (n : ℕ) (hn : 0 < n) :
    Odd (Nat.Partition.restricted n (¬ 4 ∣ ·)).card ↔ ∃ m : ℕ, n = m * (m + 1) / 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [← ZMod.natCast_eq_one_iff_odd, fourRegularCount_cast_eq_coeff]
  constructor
  · intro h
    by_contra htri
    rw [coeff_jacobiCubeSeries_eq_zero (fun m hm =>
      htri ⟨m, hm.symm.trans (choose_two_succ_eq_triangle m)⟩), Int.cast_zero] at h
    exact zero_ne_one h
  · rintro ⟨m, hm⟩
    rw [hm, ← choose_two_succ_eq_triangle, coeff_jacobiCubeSeries_triangle]
    have hneg : (-1 : ZMod 2) = 1 := by decide
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [hneg, htwo]

end MetaMathlibExt
