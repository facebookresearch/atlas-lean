/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-!
# Lit cells and lit nodes of weakly increasing diagrams

`litCellsIncreasing_generatingFunction` gives two Lambert series formulas for the
total number of lit cells over the partitions of each size.
`litNodesIncreasing_generatingFunction` gives the corresponding formula for lit nodes in
Ferrers diagrams.

## References

* Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*,
  INTEGERS 24 (2024), Article A56, pp. 1–14, Section 2, equation (2), and Section 3,
  Proposition 1, equation (5), and Proposition 2, equation (7).

The lit-node proof reuses the coefficient count `coeff_total_parts` and the conjugation
argument from `total_lit_cells`, both in this module.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Lit cells of a weakly increasing bargraph.** For a partition $p$ of $n$, the number of lit
cells of $p$, drawn as a weakly increasing bargraph, is defined as the largest part of $p$ plus the
number of parts of $p$ minus the number of distinct parts of $p$ (the largest part of the empty
partition is $0$).

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 1. -/
public def litCellsIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - p.parts.dedup.card

/-- **Lit nodes of a partition.** The number of lit nodes of a partition $p$, drawn as a weakly
increasing Ferrers diagram of nodes, is defined as the largest part of $p$ plus the number of
parts of $p$ minus one; for the empty partition it is $0$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3, proof of Proposition 2. -/
public def litNodesIncreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.sup + p.parts.card - 1

/-- **Lit cells of a one-part increasing bargraph.** For every natural number $n \ge 1$, the
partition $(n)$ of $n$ with a single part has $n$ lit cells as a weakly increasing bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 3 (definition of lit cells). -/
public theorem litCellsIncreasing_indiscrete {n : ℕ} (hn : n ≠ 0) :
    litCellsIncreasing (Nat.Partition.indiscrete n) = n := by
  simp [litCellsIncreasing, hn]

namespace litCellsIncreasing_generatingFunction

open Finset PowerSeries.WithPiTopology

private abbrev P : ℤ⟦X⟧ := mk fun n => (Fintype.card (Nat.Partition n) : ℤ)

-- Transposing the diagram exchanges the largest part and the number of parts.
private theorem card_conjugate {n : ℕ} (p : Nat.Partition n) :
    p.conjugate.parts.card = p.parts.sup := by
  let μ := YoungDiagram.ofPartition p
  have hparts : (μ.rowLens : Multiset ℕ) = p.parts := by simp [μ]
  change ((μ.transpose.rowLens : Multiset ℕ).card) = _
  rw [Multiset.coe_card, YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose, ← hparts]
  apply le_antisymm
  · by_cases h : 0 < μ.rowLen 0
    · apply Multiset.le_sup
      have hcol := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr hcol, rfl⟩
    · omega
  · apply Multiset.sup_le.mpr
    intro b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (show b ∈ μ.rowLens from hb)
    exact μ.rowLen_anti 0 i (Nat.zero_le i)

-- Removing a rectangle of k rows of length v shifts the generating function by k*v.
private theorem coeff_shift (n v k : ℕ) (hv : 0 < v) :
    coeff n (P * X ^ (k * v)) =
      ∑ p : Nat.Partition n, if k ≤ p.parts.count v then (1 : ℤ) else 0 := by
  rw [coeff_mul_X_pow']
  by_cases h : k * v ≤ n
  · rw [ite_eq_left h, ← sum_filter]
    simp [P, ← Fintype.card_subtype, Nat.Partition.card_count_ge hv h]
  · rw [ite_eq_right h]
    symm
    apply sum_eq_zero
    intro p _
    apply ite_eq_right
    intro hk
    have hle := Multiset.le_count_iff_replicate_le.mp hk
    have hs := congrArg Multiset.sum (Multiset.sub_add_cancel hle)
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, p.parts_sum] at hs
    omega

private theorem hasSum_geometric (v : ℕ) :
    HasSum (fun k : ℕ => (X ^ (v + 1) : ℤ⟦X⟧) ^ k)
      (invOfUnit (1 - X ^ (v + 1)) 1) := by
  have h : constantCoeff (X ^ (v + 1) : ℤ⟦X⟧) = 0 := by simp
  have hs := (summable_pow_of_constantCoeff_eq_zero h).hasSum
  convert hs using 1
  have hinv := mul_invOfUnit (1 - X ^ (v + 1) : ℤ⟦X⟧) 1 (by simp [h])
  calc
    _ = ((∑' k : ℕ, (X ^ (v + 1) : ℤ⟦X⟧) ^ k) * (1 - X ^ (v + 1))) *
        invOfUnit (1 - X ^ (v + 1)) 1 := by rw [tsum_pow_mul_one_sub_of_constantCoeff_eq_zero h,
          one_mul]
    _ = _ := by rw [mul_assoc, hinv, mul_one]

private theorem hasSum_thresholds (m : ℕ) :
    HasSum (fun k : ℕ => if k + 1 ≤ m then (1 : ℤ) else 0) (m : ℤ) := by
  have h := hasSum_sum_of_ne_finset_zero (L := .unconditional _) (s := range m)
    (f := fun k : ℕ => if k + 1 ≤ m then (1 : ℤ) else 0)
    (fun k hk => ite_eq_right (by simpa [Nat.succ_le_iff] using hk))
  simpa [Nat.succ_le_iff, ← mem_range] using h

private theorem coeff_multiplicity (n v : ℕ) :
    coeff n (P * (X ^ (v + 1) * invOfUnit (1 - X ^ (v + 1)) 1)) =
      ∑ p : Nat.Partition n, (p.parts.count (v + 1) : ℤ) := by
  have hs := (hasSum_geometric v).mul_left (P * X ^ (v + 1))
  rw [mul_assoc] at hs
  have hc := (hasSum_iff_hasSum_coeff ℤ).mp hs n
  simp_rw [mul_assoc P, ← pow_succ', ← pow_mul, Nat.mul_comm (v + 1),
    coeff_shift _ _ _ (Nat.succ_pos v)] at hc
  exact hc.unique (hasSum_sum fun (p : Nat.Partition n) _ => hasSum_thresholds _)

private theorem hasSum_counts (m : Multiset ℕ) (h0 : 0 ∉ m) :
    HasSum (fun v : ℕ => (m.count (v + 1) : ℤ)) (m.card : ℤ) := by
  have h : HasSum (fun v => (m.count v : ℤ)) (m.card : ℤ) := by
    rw [← m.toFinset_sum_count_eq, Nat.cast_sum]
    exact hasSum_sum_of_ne_finset_zero fun v hv => by simpa using hv
  simpa [Multiset.count_eq_zero.mpr h0] using (hasSum_nat_add_iff' 1).mpr h

private noncomputable abbrev lambert (v : ℕ) : ℤ⟦X⟧ :=
  X ^ (v + 1) * invOfUnit (1 - X ^ (v + 1)) 1

private theorem summable_lambert : Summable lambert := by
  apply (summable_iff_summable_coeff ℤ).mpr
  intro n
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Iic n).subset
  intro i hi
  change coeff n (lambert i) ≠ 0 at hi
  change i ≤ n
  by_contra h
  exact hi (by rw [lambert, coeff_X_pow_mul', ite_eq_right (by omega)])

private theorem hasSum_positive_powers :
    HasSum (fun i : ℕ => (X ^ (i + 1) : ℤ⟦X⟧)) (X * invOfUnit (1 - X) 1) := by
  simpa [pow_succ'] using (hasSum_geometric 0).mul_left X

-- Summing multiplicities gives the number of parts. Counting each size only once
-- gives the number of distinct parts, so only the first removal contributes.
private theorem coeff_total_parts (n : ℕ) :
    coeff n (P * ∑' v, lambert v) = ∑ p : Nat.Partition n, (p.parts.card : ℤ) := by
  have h := (hasSum_iff_hasSum_coeff ℤ).mp (summable_lambert.hasSum.mul_left P) n
  simp_rw [lambert, coeff_multiplicity] at h
  exact h.unique (hasSum_sum fun p _ => hasSum_counts p.parts (fun hp => (p.parts_pos hp).false))

private theorem coeff_distinct_parts (n : ℕ) :
    coeff n (P * (X * invOfUnit (1 - X) 1)) =
      ∑ p : Nat.Partition n, (p.parts.dedup.card : ℤ) := by
  have h := (hasSum_iff_hasSum_coeff ℤ).mp (hasSum_positive_powers.mul_left P) n
  have hcoeff (v : ℕ) : coeff n (P * X ^ (v + 1)) =
      ∑ p : Nat.Partition n, (p.parts.dedup.count (v + 1) : ℤ) := by
    simpa [Multiset.count_dedup, Nat.one_le_iff_ne_zero, Multiset.count_eq_zero,
      apply_ite Nat.cast] using coeff_shift n (v + 1) 1 (Nat.succ_pos v)
  simp_rw [hcoeff] at h
  exact h.unique (hasSum_sum fun p _ => hasSum_counts p.parts.dedup
    (fun hp => (p.parts_pos (Multiset.mem_dedup.mp hp)).false))

private theorem sum_largest_parts_eq_sum_card (n : ℕ) :
    ∑ p : Nat.Partition n, (p.parts.sup : ℤ) =
      ∑ p : Nat.Partition n, (p.parts.card : ℤ) := by
  simp_rw [← card_conjugate]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ Nat.Partition.conjugate_conjugate)
    (fun p : Nat.Partition n => (p.parts.card : ℤ))

private theorem total_lit_cells :
    mk (fun n => ∑ p : Nat.Partition n, (litCellsIncreasing p : ℤ)) =
      2 * (P * ∑' v, lambert v) - P * (X * invOfUnit (1 - X) 1) := by
  ext n
  rw [coeff_mk, map_sub, two_mul, map_add, coeff_total_parts, coeff_distinct_parts]
  nth_rw 1 [← sum_largest_parts_eq_sum_card n]
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  have h := Multiset.card_le_card (Multiset.dedup_le p.parts)
  rw [litCellsIncreasing, Nat.cast_sub (by omega), Nat.cast_add]

private theorem hasSum_weighted_lambert :
    HasSum (fun v : ℕ => (X ^ (v + 1) : ℤ⟦X⟧) * (1 + X ^ (v + 1)) *
      invOfUnit (1 - X ^ (v + 1)) 1)
      (2 * ∑' v, lambert v - X * invOfUnit (1 - X) 1) := by
  apply ((summable_lambert.hasSum.mul_left 2).sub hasSum_positive_powers).congr_fun
  intro v
  unfold lambert
  have h := mul_invOfUnit (1 - X ^ (v + 1) : ℤ⟦X⟧) 1 (by simp)
  linear_combination -X ^ (v + 1) * h

end litCellsIncreasing_generatingFunction

open litCellsIncreasing_generatingFunction in
/-- **Generating function for lit cells of weakly increasing bargraphs.** Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, and let
$L(q) \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the total number of
lit cells over all partitions of $n$ drawn as weakly increasing bargraphs. Then
$$L(q) = 2P(q) \sum_{i \ge 1} \frac{q^i}{1 - q^i} - P(q) \frac{q}{1 - q}$$
and
$$L(q) = P(q) \sum_{i \ge 1} \frac{q^i (1 + q^i)}{1 - q^i},$$
where the sums converge coefficientwise.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 1, eq. (5)
(`integers-2024-A56-prop-1`). -/
public theorem litCellsIncreasing_generatingFunction :
    let P : ℤ⟦X⟧ := mk fun n => (Fintype.card (Nat.Partition n) : ℤ)
    mk (fun n => ∑ p : Nat.Partition n, (litCellsIncreasing p : ℤ)) =
        2 * P * ∑' i : ℕ, X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 -
          P * X * invOfUnit (1 - X) 1 ∧
      mk (fun n => ∑ p : Nat.Partition n, (litCellsIncreasing p : ℤ)) =
        P * ∑' i : ℕ, X ^ (i + 1) * (1 + X ^ (i + 1)) * invOfUnit (1 - X ^ (i + 1)) 1 := by
  dsimp only
  constructor
  · rw [total_lit_cells]
    unfold lambert P
    ring
  · rw [hasSum_weighted_lambert.tsum_eq, total_lit_cells]
    unfold P
    ring

open Finset litCellsIncreasing_generatingFunction in
/-- **Generating function for lit nodes of weakly increasing diagrams.** Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, and let
$N(q) \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the total number of
lit nodes over all partitions of $n$ drawn as weakly increasing Ferrers diagrams of nodes. Then
$$N(q) = 1 + P(q) \Bigl(\sum_{i \ge 1} \frac{2q^i}{1 - q^i} - 1\Bigr),$$
where the sum converges coefficientwise.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 2, eq. (7)
(`integers-2024-A56-prop-2`). -/
public theorem litNodesIncreasing_generatingFunction :
    mk (fun n => ∑ p : Nat.Partition n, (litNodesIncreasing p : ℤ)) =
      1 + (mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) *
        (∑' i : ℕ, 2 * X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 - 1) := by
  have htwo :
      (∑' i : ℕ, 2 * X ^ (i + 1) * invOfUnit (1 - X ^ (i + 1)) 1 : ℤ⟦X⟧) =
        2 * ∑' i, lambert i := by
    simpa only [lambert, mul_assoc] using (summable_lambert.hasSum.mul_left 2).tsum_eq
  rw [htwo]
  change _ = 1 + P * (2 * (∑' i, lambert i) - 1)
  rw [mul_sub, mul_one, two_mul, mul_add]
  ext n
  rw [coeff_mk, map_add, map_sub, map_add, coeff_total_parts, P, coeff_mk, coeff_one]
  by_cases hn : n = 0
  · subst n
    simp [litNodesIncreasing]
  rw [ite_eq_right hn, zero_add]
  calc
    _ = ∑ p : Nat.Partition n, ((p.parts.sup : ℤ) + p.parts.card - 1) := by
      refine sum_congr rfl fun p _ => ?_
      have hp : p.parts ≠ 0 := fun h => hn (by simpa [h] using p.parts_sum.symm)
      have hcard := Multiset.card_pos.mpr hp
      rw [litNodesIncreasing, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    _ = _ := by
      simp [sum_sub_distrib, sum_add_distrib, sum_largest_parts_eq_sum_card]

end

end MetaMathlibExt
