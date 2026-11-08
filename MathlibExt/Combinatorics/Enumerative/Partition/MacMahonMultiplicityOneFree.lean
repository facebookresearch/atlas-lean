/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas

@[expose] public section

namespace MetaMathlibExt

open scoped PowerSeries.WithPiTopology

private theorem multiplicityOneFree_genFun :
    PowerSeries.mk (fun n => ((Finset.univ.filter (fun p : Nat.Partition n =>
      ∀ m ∈ p.parts, Multiset.count m p.parts ≠ 1)).card : ℤ)) =
    Nat.Partition.genFun (fun _ c => if c ≠ 1 then (1 : ℤ) else 0) := by
  ext n
  simp_rw [Nat.Partition.genFun, Finset.card_filter, Finsupp.prod, Finset.prod_boole]
  simp

private theorem multiplicityOneFree_factor (i : ℕ) :
    (1 + ∑' j, (if j + 1 ≠ 1 then (1 : ℤ) else 0) •
      (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) =
    (∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (2 * (i + 1) * j)) *
      (1 + (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1))) := by
  let y : PowerSeries ℤ := PowerSeries.X ^ (i + 1)
  have hy : y.constantCoeff = 0 := by simp [y]
  have hs : Summable (fun j : ℕ => y ^ j) :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hy
  let f : ℕ → PowerSeries ℤ := fun j =>
    (if j + 1 ≠ 1 then (1 : ℤ) else 0) •
      (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))
  have hsum : Summable f :=
    Nat.Partition.summable_genFun_term
      (fun _ c => if c ≠ 1 then (1 : ℤ) else 0) i
  have hseries :
      (∑' j, (if j + 1 ≠ 1 then (1 : ℤ) else 0) •
        (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) =
      y ^ 2 * ∑' j, y ^ j := by
    change ∑' j, f j = _
    calc
      _ = f 0 + ∑' j, f (j + 1) :=
        tsum_eq_zero_add' (hsum.comp_injective Nat.succ_injective)
      _ = ∑' j, f (j + 1) := by rw [show f 0 = 0 by simp [f], zero_add]
      _ = ∑' j, y ^ 2 * y ^ j := by
        apply tsum_congr
        intro j
        simp only [f]
        split_ifs
        · simp only [one_smul]
          ring
        · omega
      _ = y ^ 2 * ∑' j, y ^ j := hs.tsum_mul_left (y ^ 2)
  have hright :
      (∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (2 * (i + 1) * j)) =
      ∑' j, (y ^ 2) ^ j := by
    apply tsum_congr
    intro j
    simp only [y]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hseries, hright]
  apply mul_right_cancel₀ (b := 1 - y ^ 2) (by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hy] at h')
  have hgeom :=
    PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hy
  have hy2 : (y ^ 2).constantCoeff = 0 := by simp [hy]
  have hgeom2 :=
    PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hy2
  calc
    (1 + y ^ 2 * ∑' j, y ^ j) * (1 - y ^ 2) =
        (1 - y ^ 2) + y ^ 2 * ((∑' j, y ^ j) * (1 - y)) * (1 + y) := by ring
    _ = 1 + y ^ 3 := by rw [hgeom]; ring
    _ = ((∑' j, (y ^ 2) ^ j) * (1 + y ^ 3)) * (1 - y ^ 2) := by
      rw [show ((∑' j, (y ^ 2) ^ j) * (1 + y ^ 3)) * (1 - y ^ 2) =
        ((∑' j, (y ^ 2) ^ j) * (1 - y ^ 2)) * (1 + y ^ 3) by ring, hgeom2]
      ring
    _ = ((∑' j, (y ^ 2) ^ j) *
        (1 + PowerSeries.X ^ (3 * (i + 1)))) * (1 - y ^ 2) := by
      simp [y, pow_mul, mul_comm]

private theorem multipliable_geometric_mul_index (k : ℕ) (hk : k ≠ 0) :
    Multipliable (fun i => ∑' j,
      (PowerSeries.X : PowerSeries ℤ) ^ (k * (i + 1) * j)) := by
  have hx : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℤ) ^ k) :=
    PowerSeries.HasSubst.X_pow hk
  have hcont : Continuous ⇑(PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx) := by
    rw [PowerSeries.substAlgHom_eq_aeval hx]
    exact MvPowerSeries.continuous_aeval _
  have hbase := Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (fun _ => True)
  apply (hbase.map (PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx) hcont).congr
  intro i
  simp only [Function.comp_apply, ite_true]
  have hsum := PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
    (by simp : ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)).constantCoeff = 0)
  have hsum' : Summable (fun j =>
      (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) := by
    simpa [pow_mul] using hsum
  rw [hsum'.map_tsum _ hcont]
  apply tsum_congr
  intro j
  simp [PowerSeries.substAlgHom_X, ← pow_mul]
  congr 1
  ring

private theorem multipliable_distinct_mul_index (k : ℕ) (hk : k ≠ 0) :
    Multipliable (fun i =>
      1 + (PowerSeries.X : PowerSeries ℤ) ^ (k * (i + 1))) := by
  have hx : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℤ) ^ k) :=
    PowerSeries.HasSubst.X_pow hk
  have hcont : Continuous ⇑(PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx) := by
    rw [PowerSeries.substAlgHom_eq_aeval hx]
    exact MvPowerSeries.continuous_aeval _
  have hbase := Nat.Partition.multipliable_powerSeriesMk_card_countRestricted ℤ 2
  apply (hbase.map (PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx) hcont).congr
  intro i
  simp only [Function.comp_apply]
  norm_num [Finset.sum_range_succ, PowerSeries.substAlgHom_X, ← pow_mul]

private theorem euler_scaled_three :
    (∏' i, (1 + (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1)))) =
    ∏' i, if ¬2 ∣ i + 1 then
      ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1) * j) else 1 := by
  have heuler :
      (∏' i, ∑ j ∈ Finset.range 2,
        (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) =
      ∏' i, if ¬2 ∣ i + 1 then
        ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1 := by
    rw [← Nat.Partition.powerSeriesMk_card_countRestricted_eq_tprod ℤ (by norm_num : 0 < 2)]
    rw [← Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (¬2 ∣ ·)]
    exact (Nat.Partition.powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted
      ℤ (by norm_num : 0 < 2)).symm
  have hx3 : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℤ) ^ 3) :=
    PowerSeries.HasSubst.X_pow (by norm_num)
  have hcont : Continuous ⇑(PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3) := by
    rw [PowerSeries.substAlgHom_eq_aeval hx3]
    exact MvPowerSeries.continuous_aeval _
  have hcount := Nat.Partition.multipliable_powerSeriesMk_card_countRestricted ℤ 2
  have hrestricted :=
    Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (¬2 ∣ ·)
  calc
    _ = ∏' i, PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3
        (∑ j ∈ Finset.range 2,
          (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) := by
      apply tprod_congr
      intro i
      norm_num [Finset.sum_range_succ, PowerSeries.substAlgHom_X, ← pow_mul]
    _ = PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3
        (∏' i, ∑ j ∈ Finset.range 2,
          (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) :=
      (hcount.map_tprod (PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3) hcont).symm
    _ = PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3
        (∏' i, if ¬2 ∣ i + 1 then
          ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) := by rw [heuler]
    _ = ∏' i, PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3
        (if ¬2 ∣ i + 1 then
          ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) :=
      hrestricted.map_tprod (PowerSeries.substAlgHom (R := ℤ) (S := ℤ) hx3) hcont
    _ = _ := by
      apply tprod_congr
      intro i
      split_ifs
      · exact map_one _
      · have hsum := PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
          (by simp : (PowerSeries.X ^ (i + 1) : PowerSeries ℤ).constantCoeff = 0)
        have hsum' : Summable (fun j =>
            (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) := by
          simpa [pow_mul] using hsum
        rw [hsum'.map_tsum _ hcont]
        apply tsum_congr
        intro j
        simp [PowerSeries.substAlgHom_X, ← pow_mul]
        congr 1
        ring

private theorem geometricSeries_ne_one (a : ℕ) (ha : 0 < a) :
    (∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (a * j)) ≠ 1 := by
  have hgeom := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
    (by simp [ha.ne'] : ((PowerSeries.X : PowerSeries ℤ) ^ a).constantCoeff = 0)
  intro h
  have h' : (∑' j, ((PowerSeries.X : PowerSeries ℤ) ^ a) ^ j) = 1 := by
    simpa [pow_mul] using h
  rw [h', one_mul] at hgeom
  have hc := congrArg (PowerSeries.coeff a) hgeom
  simp [PowerSeries.coeff_one, PowerSeries.coeff_X_pow, ha.ne'] at hc

private theorem tprod_geometric_mul_index (k : ℕ) (hk : 0 < k) :
    (∏' i, ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (k * (i + 1) * j)) =
    ∏' i, if k ∣ i + 1 then
      ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1 := by
  symm
  refine tprod_eq_tprod_of_ne_one_bij (fun i => (i.val + 1) * k - 1) ?_ ?_ ?_
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith),
      mul_left_inj' (hk.ne.symm), add_left_inj] at h
    exact SetCoe.ext h
  · intro i hi
    have hki : k ∣ i + 1 := by
      by_contra h
      simp [h] at hi
    obtain ⟨j, hj⟩ := dvd_def.mp hki
    have hj0 : j ≠ 0 := by grind
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    let a : ℕ := j - 1
    have ha : a + 1 = j := by simp [a, Nat.sub_add_cancel hjpos]
    refine ⟨⟨a, ?_⟩, ?_⟩
    · exact geometricSeries_ne_one (k * (a + 1)) (Nat.mul_pos hk (by simp [ha, hjpos]))
    · dsimp only
      rw [ha]
      apply Nat.sub_eq_of_eq_add
      calc
        j * k = k * j := by rw [mul_comm]
        _ = i + 1 := hj.symm
  · intro i
    have hidx : (i.val + 1) * k - 1 + 1 = (i.val + 1) * k := by
      exact Nat.sub_add_cancel (Nat.mul_pos (by positivity) hk)
    have hdiv : k ∣ (i.val + 1) * k - 1 + 1 := by
      rw [hidx]
      exact dvd_mul_left k (i.val + 1)
    simp only [hdiv, ↓reduceIte]
    change (∑' j, (PowerSeries.X : PowerSeries ℤ) ^
      (((i.val + 1) * k - 1 + 1) * j)) = _
    rw [hidx]
    apply tsum_congr
    intro j
    congr 1
    ring

private theorem tprod_odd_triples :
    (∏' i, if ¬2 ∣ i + 1 then
      ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1) * j) else 1) =
    ∏' i, if (i + 1) % 6 = 3 then
      ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1 := by
  symm
  refine tprod_eq_tprod_of_ne_one_bij (fun i => (i.val + 1) * 3 - 1) ?_ ?_ ?_
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith),
      mul_left_inj' (by norm_num : (3 : ℕ) ≠ 0), add_left_inj] at h
    exact SetCoe.ext h
  · intro i hi
    have hmod : (i + 1) % 6 = 3 := by
      by_contra h
      simp [h] at hi
    let q := (i + 1) / 3
    have hqpos : 0 < q := by omega
    have hqodd : ¬2 ∣ q := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    let a := q - 1
    have ha : a + 1 = q := by simp [a, Nat.sub_add_cancel hqpos]
    have haodd : ¬2 ∣ a + 1 := by simpa [ha] using hqodd
    refine ⟨⟨a, ?_⟩, ?_⟩
    · rw [Function.mem_mulSupport]
      simp only [haodd]
      exact geometricSeries_ne_one (3 * (a + 1)) (by positivity)
    · dsimp only
      rw [ha]
      omega
  · intro i
    have hodd : ¬2 ∣ i.val + 1 := by
      by_contra h
      have hi := i.property
      simp at hi
      rw [Nat.dvd_iff_mod_eq_zero] at h
      omega
    have hidx : (i.val + 1) * 3 - 1 + 1 = (i.val + 1) * 3 := by omega
    have hmod : ((i.val + 1) * 3) % 6 = 3 := by
      rw [Nat.dvd_iff_mod_eq_zero] at hodd
      omega
    rw [hidx]
    simp only [hmod, hodd, ↓reduceIte]
    change (∑' j, (PowerSeries.X : PowerSeries ℤ) ^
      (((i.val + 1) * 3) * j)) = _
    apply tsum_congr
    intro j
    congr 1
    ring

/-- MacMahon's partition theorem: for every `n`, the number of partitions of `n`
with no part occurring exactly once equals the number of partitions of `n` all of
whose parts are even or congruent to `3` modulo `6`.

The left side counts `p : Nat.Partition n` satisfying
`Multiset.count m p.parts ≠ 1` for every part `m ∈ p.parts`. The right side is
the existing `Nat.Partition.restricted` finset for the per-part predicate
`m % 2 = 0 ∨ m % 6 = 3`.

Provenance: Beaullah Mugwangwavari and Darlison Nyirenda, "A Note on the
Andrews-Ericksson-Petrov-Romick Bijection for MacMahon's Partition Theorem",
Journal of Integer Sequences 24 (2021), Article 21.5.6, Theorem `MacMahon`,
source lines 88–97 with the displayed statement at lines 91–93,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Nyirenda/nyir26.tex>.
The paper attributes the theorem to P. A. MacMahon, *Combinatory Analysis*,
Vol. 2 (1916).

Scope: the source fixes `n ≥ 1`. The statement here is over all `n : ℕ`; at
`n = 0` both filtered sets consist solely of the empty partition, so including
`n = 0` is a proved-by-definition endpoint extension rather than a claim copied
from the source.

Proves `Wanted` entry `macmahon_multiplicity_one_free`.
-/
theorem macmahon_multiplicity_one_free (n : ℕ) :
    (Finset.univ.filter (fun p : Nat.Partition n =>
      ∀ m ∈ p.parts, Multiset.count m p.parts ≠ 1)).card =
    (Nat.Partition.restricted n (fun m => m % 2 = 0 ∨ m % 6 = 3)).card := by
  have hEven := multipliable_geometric_mul_index 2 (by norm_num)
  have hTripleDistinct := multipliable_distinct_mul_index 3 (by norm_num)
  have hEvenRestricted :=
    Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (2 ∣ ·)
  have hOddTripleRestricted :=
    Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (fun m => m % 6 = 3)
  have hseries :
      PowerSeries.mk (fun n => ((Finset.univ.filter (fun p : Nat.Partition n =>
        ∀ m ∈ p.parts, Multiset.count m p.parts ≠ 1)).card : ℤ)) =
      PowerSeries.mk (fun n =>
        ((Nat.Partition.restricted n (fun m => m % 2 = 0 ∨ m % 6 = 3)).card : ℤ)) := by
    calc
      _ = Nat.Partition.genFun (fun _ c => if c ≠ 1 then (1 : ℤ) else 0) :=
        multiplicityOneFree_genFun
      _ = ∏' i, (1 + ∑' j, (if j + 1 ≠ 1 then (1 : ℤ) else 0) •
          (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) :=
        Nat.Partition.genFun_eq_tprod _
      _ = ∏' i, (∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (2 * (i + 1) * j)) *
          (1 + (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1))) := by
        apply tprod_congr
        exact multiplicityOneFree_factor
      _ = (∏' i, ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (2 * (i + 1) * j)) *
          ∏' i, (1 + (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1))) :=
        hEven.tprod_mul hTripleDistinct
      _ = (∏' i, if 2 ∣ i + 1 then
            ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) *
          ∏' i, if ¬2 ∣ i + 1 then
            ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ (3 * (i + 1) * j) else 1 := by
        rw [tprod_geometric_mul_index 2 (by norm_num), euler_scaled_three]
      _ = (∏' i, if 2 ∣ i + 1 then
            ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) *
          ∏' i, if (i + 1) % 6 = 3 then
            ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1 := by
        rw [tprod_odd_triples]
      _ = ∏' i, (if 2 ∣ i + 1 then
            ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) *
          (if (i + 1) % 6 = 3 then
            ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1) :=
        (hEvenRestricted.tprod_mul hOddTripleRestricted).symm
      _ = ∏' i, if (i + 1) % 2 = 0 ∨ (i + 1) % 6 = 3 then
          ∑' j, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) else 1 := by
        apply tprod_congr
        intro i
        by_cases he : 2 ∣ i + 1
        · have hemod : (i + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp he
          by_cases ho : (i + 1) % 6 = 3
          · rw [Nat.dvd_iff_mod_eq_zero] at he
            omega
          · simp [he, hemod, ho]
        · have hemod : (i + 1) % 2 ≠ 0 := by
            simpa [Nat.dvd_iff_mod_eq_zero] using he
          by_cases ho : (i + 1) % 6 = 3 <;> simp [he, hemod, ho]
      _ = PowerSeries.mk (fun n =>
          ((Nat.Partition.restricted n (fun m => m % 2 = 0 ∨ m % 6 = 3)).card : ℤ)) :=
        (Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ
          (fun m => m % 2 = 0 ∨ m % 6 = 3)).symm
  have hc := PowerSeries.ext_iff.mp hseries n
  have hc' :
      ((Finset.univ.filter (fun p : Nat.Partition n =>
        ∀ m ∈ p.parts, Multiset.count m p.parts ≠ 1)).card : ℤ) =
      ((Nat.Partition.restricted n (fun m => m % 2 = 0 ∨ m % 6 = 3)).card : ℤ) := by
    simpa using hc
  exact_mod_cast hc'

end MetaMathlibExt
