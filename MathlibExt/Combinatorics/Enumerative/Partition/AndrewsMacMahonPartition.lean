/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Set.Card

import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Andrews generalization of the MacMahon partition identity

This file proves Andrews' equinumerosity theorem for partitions with restricted odd
multiplicities and partitions with restricted odd parts.
-/

@[expose] public section

namespace MetaMathlibExt

open PowerSeries
open scoped PowerSeries.WithPiTopology

private theorem amp_coeff_genFun_indicator (q : ℕ → ℕ → Prop) [DecidableRel q] (n : ℕ) :
    (Nat.Partition.genFun (fun i c ↦ if q i c then (1 : ℤ) else 0)).coeff n =
      ((Finset.univ.filter fun p : Nat.Partition n ↦
        ∀ i ∈ p.parts, q i (p.parts.count i)).card : ℤ) := by
  simp_rw [Nat.Partition.coeff_genFun, Finsupp.prod, Finset.prod_boole]
  simp

private theorem amp_ncard_setOf_eq_card_filter (n : ℕ) (P : Nat.Partition n → Prop)
    [DecidablePred P] :
    Set.ncard {p : Nat.Partition n | P p} = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext p
  simp

private theorem amp_odd_imp_iff_even_or (s c : ℕ) :
    (Odd c → s ≤ c) ↔ Even c ∨ s ≤ c := by
  constructor
  · intro h
    rcases Nat.even_or_odd c with heven | hodd
    · exact Or.inl heven
    · exact Or.inr (h hodd)
  · rintro (heven | hle) hodd
    · exact (Nat.not_even_iff_odd.mpr hodd heven).elim
    · exact hle

private theorem amp_geom_ne_one (d : ℕ) (hd : d ≠ 0) :
    (∑' j : ℕ, (X : ℤ⟦X⟧) ^ (d * j)) ≠ 1 := by
  intro h
  have hsum : Summable (fun j : ℕ ↦ (X : ℤ⟦X⟧) ^ (d * j)) := by
    simpa only [pow_mul] using
      (PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
        (f := (X : ℤ⟦X⟧) ^ d) (by simp [hd]))
  have hc := congrArg (PowerSeries.coeff d) h
  rw [hsum.map_tsum (PowerSeries.coeff d)
    (PowerSeries.WithPiTopology.continuous_coeff ℤ d)] at hc
  simp [PowerSeries.coeff_X_pow, hd] at hc

private theorem amp_hasProd_even_counts : HasProd
    (fun i : ℕ ↦ ∑' j : ℕ, (X : ℤ⟦X⟧) ^ (((i + 1) * 2) * j))
    (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n Even).card : ℤ)) := by
  let f : ℕ → ℤ⟦X⟧ := fun i ↦
    if Even (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1
  let g : ℕ → ℤ⟦X⟧ := fun i ↦
    ∑' j : ℕ, X ^ (((i + 1) * 2) * j)
  apply (hasProd_iff_hasProd_of_ne_one_bij (f := f) (g := g)
    (fun i ↦ 2 * (i.val + 1) - 1) (by
      intro a b h
      apply Subtype.ext
      change 2 * (a.val + 1) - 1 = 2 * (b.val + 1) - 1 at h
      omega) (by
      intro x hx
      have hev : Even (x + 1) := by
        contrapose! hx
        simp [f, hx]
      obtain ⟨k, hk⟩ := hev.two_dvd
      have hk0 : k ≠ 0 := by omega
      have hgne : g (k - 1) ≠ 1 := by
        simpa [g, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] using
          amp_geom_ne_one (k * 2) (by omega)
      refine ⟨⟨k - 1, hgne⟩, ?_⟩
      change 2 * ((k - 1) + 1) - 1 = x
      omega) (by
      intro x
      have hx : 2 * (x.val + 1) - 1 + 1 = 2 * (x.val + 1) := by omega
      simp only [f, g]
      rw [ite_eq_left (by rw [hx]; exact even_two_mul _)]
      simp_rw [hx]
      apply tsum_congr
      intro j
      congr 1
      ring)).mp
  simpa [f] using Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ Even

private theorem amp_lhs_factor (s i : ℕ) (hs : Odd s) (hi : i ≠ 0) :
    (1 + ∑' j : ℕ, (if Even (j + 1) ∨ s ≤ j + 1 then (1 : ℤ) else 0) •
      (X : ℤ⟦X⟧) ^ (i * (j + 1))) =
      (∑' j : ℕ, (X : ℤ⟦X⟧) ^ (i * (2 * j))) * (1 + X ^ (i * s)) := by
  obtain ⟨a, rfl⟩ := hs.exists_bit1
  let Y : ℤ⟦X⟧ := X ^ i
  let F : ℕ → ℤ⟦X⟧ := fun c ↦
    if Even c ∨ 2 * a + 1 ≤ c then Y ^ c else 0
  let Z : ℤ⟦X⟧ := Y ^ 2
  have hZ0 : Z.constantCoeff = 0 := by
    simp [Z, Y, hi]
  have hZ : Summable (Z ^ ·) :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hZ0
  have heY : Summable (fun k ↦ Y ^ (2 * k)) := by
    simpa [Z, pow_mul] using hZ
  have he : Summable (fun k ↦ F (2 * k)) := by
    simpa [F, Z, pow_mul] using hZ
  have ho : Summable (fun k ↦ F (2 * k + 1)) := by
    apply (summable_nat_add_iff a).mp
    refine (hZ.mul_right (Y ^ (2 * a + 1))).congr fun k ↦ ?_
    rw [show F (2 * (k + a) + 1) = Y ^ (2 * (k + a) + 1) by simp [F]]
    rw [show 2 * (k + a) + 1 = 2 * k + (2 * a + 1) by omega, pow_add]
    simp only [Z, ← pow_mul, pow_one]
    rw [← pow_succ, ← pow_add]
  have hF : Summable F := he.even_add_odd ho
  simp only [ite_smul, one_smul, zero_smul]
  simp_rw [pow_mul]
  change 1 + ∑' j : ℕ, F (j + 1) =
    (∑' j : ℕ, Z ^ j) * (1 + Y ^ (2 * a + 1))
  rw [← show F 0 = 1 by simp [F]]
  rw [← tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hF)]
  rw [← tsum_even_add_odd he ho]
  have htail : (∑' k : ℕ, F (2 * k + 1)) = ∑' k : ℕ, Y ^ (2 * (k + a) + 1) := by
    have hprefix : ∑ k ∈ Finset.range a, F (2 * k + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [F]
      omega
    rw [← ho.sum_add_tsum_nat_add a, hprefix, zero_add]
    apply tsum_congr
    intro k
    simp [F]
  rw [htail]
  have hshift (k : ℕ) : 2 * (k + a) + 1 = 2 * k + (2 * a + 1) := by omega
  simp_rw [hshift, pow_add]
  rw [heY.tsum_mul_right]
  have hevenF : (∑' k : ℕ, F (2 * k)) = ∑' k : ℕ, Z ^ k := by
    apply tsum_congr
    intro k
    simp [F, Z, pow_mul]
  have hevenY : (∑' k : ℕ, Y ^ (2 * k)) = ∑' k : ℕ, Z ^ k := by
    apply tsum_congr
    intro k
    simp [Z, pow_mul]
  rw [hevenF, hevenY, show F 0 = 1 by simp [F]]
  ring

private theorem amp_continuous_expand (s : ℕ) (hs : s ≠ 0) :
    Continuous (PowerSeries.expand s hs : ℤ⟦X⟧ → ℤ⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  by_cases h : s ∣ n
  · simpa [PowerSeries.coeff_expand, h] using
      (PowerSeries.WithPiTopology.continuous_coeff ℤ (n / s)).tendsto f
  · simp [PowerSeries.coeff_expand, h]

private theorem amp_hasProd_scaled_distinct (s : ℕ) (hs : s ≠ 0) :
    HasProd (fun i : ℕ ↦ (1 : ℤ⟦X⟧) + X ^ ((i + 1) * s))
      (PowerSeries.expand s hs
        (PowerSeries.mk fun n ↦ ((Nat.Partition.countRestricted n 2).card : ℤ))) := by
  have h := (Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℤ
    (by norm_num : 0 < 2)).map (PowerSeries.expand s hs) (amp_continuous_expand s hs)
  convert h using 1
  funext i
  simp only [Function.comp_apply]
  rw [show (∑ j ∈ Finset.range 2, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) = 1 + X ^ (i + 1) by
    norm_num [Finset.sum_range_succ]]
  rw [map_add, map_one, map_pow, PowerSeries.expand_X]
  rw [mul_comm (i + 1) s]
  rw [pow_mul]

private theorem amp_hasProd_scaled_odds (s : ℕ) (hs : s ≠ 0) :
    HasProd (fun i : ℕ ↦ if ¬Even (i + 1) then
      ∑' j : ℕ, (X : ℤ⟦X⟧) ^ (((i + 1) * s) * j) else 1)
      (PowerSeries.expand s hs
        (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (¬Even ·)).card : ℤ))) := by
  have h := (Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (¬Even ·)).map
    (PowerSeries.expand s hs) (amp_continuous_expand s hs)
  convert h using 1
  funext i
  simp only [Function.comp_apply]
  split_ifs with hi
  · rw [map_one]
  · have hsum : Summable (fun j : ℕ ↦ (X : ℤ⟦X⟧) ^ ((i + 1) * j)) := by
      simpa only [pow_mul] using
        (PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
          (f := (X : ℤ⟦X⟧) ^ (i + 1)) (by simp))
    rw [hsum.map_tsum (PowerSeries.expand s hs) (amp_continuous_expand s hs)]
    apply tsum_congr
    intro j
    rw [map_pow, PowerSeries.expand_X, ← pow_mul]
    congr 1
    ring

private theorem amp_hasProd_odd_multiples (s : ℕ) (hs : Odd s) : HasProd
    (fun i : ℕ ↦ if s ∣ i + 1 ∧ Odd ((i + 1) / s) then
      ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1)
    (PowerSeries.expand s (by obtain ⟨a, ha⟩ := hs; omega)
      (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (¬Even ·)).card : ℤ))) := by
  classical
  have hs0 : s ≠ 0 := by
    obtain ⟨a, ha⟩ := hs
    omega
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  let f : ℕ → ℤ⟦X⟧ := fun i ↦ if s ∣ i + 1 ∧ Odd ((i + 1) / s) then
    ∑' j : ℕ, X ^ ((i + 1) * j) else 1
  let g : ℕ → ℤ⟦X⟧ := fun i ↦ if ¬Even (i + 1) then
    ∑' j : ℕ, X ^ (((i + 1) * s) * j) else 1
  apply (hasProd_iff_hasProd_of_ne_one_bij (f := f) (g := g)
    (fun i ↦ (i.val + 1) * s - 1) (by
      intro a b h
      apply Subtype.ext
      change (a.val + 1) * s - 1 = (b.val + 1) * s - 1 at h
      rw [tsub_left_inj (by nlinarith [hspos]) (by nlinarith [hspos])] at h
      have hab := Nat.eq_of_mul_eq_mul_right hspos h
      omega) (by
      intro x hx
      have hp : s ∣ x + 1 ∧ Odd ((x + 1) / s) := by
        by_contra h
        exact hx (by simp [f, h])
      let k := (x + 1) / s
      have hkodd : Odd k := hp.2
      have hk : x + 1 = k * s := (Nat.div_mul_cancel hp.1).symm
      have hk0 : k ≠ 0 := by
        obtain ⟨a, ha⟩ := hkodd
        omega
      have hgne : g (k - 1) ≠ 1 := by
        simp only [g, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
        rw [ite_eq_left (Nat.not_even_iff_odd.mpr hkodd)]
        exact amp_geom_ne_one (k * s) (mul_ne_zero hk0 hs0)
      refine ⟨⟨k - 1, hgne⟩, ?_⟩
      change ((k - 1) + 1) * s - 1 = x
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
      omega) (by
      intro x
      have hodd : ¬Even (x.val + 1) := by
        intro he
        apply x.property
        simp [g, he]
      have hprod : 0 < (x.val + 1) * s := Nat.mul_pos (by omega) hspos
      have hidx : (x.val + 1) * s - 1 + 1 = (x.val + 1) * s := by omega
      simp only [f, g]
      rw [ite_eq_left (by
        rw [hidx]
        constructor
        · exact dvd_mul_left s (x.val + 1)
        · simpa [hs0] using Nat.not_even_iff_odd.mp hodd)]
      rw [ite_eq_left hodd]
      apply tsum_congr
      intro j
      rw [hidx])).mpr
  simpa [g] using amp_hasProd_scaled_odds s hs0

private theorem amp_oddMultiple_iff_mod (s m : ℕ) (hs : Odd s) :
    (s ∣ m ∧ Odd (m / s)) ↔ m % (2 * s) = s := by
  have hs0 : s ≠ 0 := by
    obtain ⟨a, ha⟩ := hs
    omega
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  constructor
  · rintro ⟨hdiv, hodd⟩
    obtain ⟨k, hk⟩ := hodd
    rw [← Nat.div_mul_cancel hdiv, hk]
    rw [show (2 * k + 1) * s = (2 * s) * k + s by ring]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · intro hmod
    have hm : m = (2 * (m / (2 * s)) + 1) * s := by
      calc
        m = (2 * s) * (m / (2 * s)) + m % (2 * s) :=
          (Nat.div_add_mod m (2 * s)).symm
        _ = (2 * (m / (2 * s)) + 1) * s := by rw [hmod]; ring
    constructor
    · rw [hm]
      exact dvd_mul_left s _
    · rw [hm]
      simp [hs0]

private theorem amp_odd_imp_mod_iff_even_or (s m : ℕ) (hs : Odd s) :
    (Odd m → m % (2 * s) = s) ↔ Even m ∨ (s ∣ m ∧ Odd (m / s)) := by
  constructor
  · intro h
    rcases Nat.even_or_odd m with heven | hodd
    · exact Or.inl heven
    · exact Or.inr ((amp_oddMultiple_iff_mod s m hs).mpr (h hodd))
  · rintro (heven | hmultiple) hodd
    · exact (Nat.not_even_iff_odd.mpr hodd heven).elim
    · exact (amp_oddMultiple_iff_mod s m hs).mp hmultiple

private theorem amp_scaled_euler (s : ℕ) (hs : s ≠ 0) :
    PowerSeries.expand s hs
        (PowerSeries.mk fun n ↦ ((Nat.Partition.countRestricted n 2).card : ℤ)) =
      PowerSeries.expand s hs
        (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (¬Even ·)).card : ℤ)) := by
  apply congrArg (PowerSeries.expand s hs)
  simpa [even_iff_two_dvd] using
    (Nat.Partition.powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted ℤ
      (by norm_num : 0 < 2)).symm

private theorem amp_genFun_eq_restricted (s : ℕ) (hs : Odd s) :
    Nat.Partition.genFun (fun _ c ↦ if Even c ∨ s ≤ c then (1 : ℤ) else 0) =
      PowerSeries.mk fun n ↦
        ((Nat.Partition.restricted n fun m ↦ Even m ∨ (s ∣ m ∧ Odd (m / s))).card : ℤ) := by
  have hs0 : s ≠ 0 := by
    obtain ⟨a, ha⟩ := hs
    omega
  let E : ℤ⟦X⟧ :=
    PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n Even).card : ℤ)
  let D : ℤ⟦X⟧ := PowerSeries.expand s hs0 <|
    PowerSeries.mk fun n ↦ ((Nat.Partition.countRestricted n 2).card : ℤ)
  let O : ℤ⟦X⟧ := PowerSeries.expand s hs0 <|
    PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (¬Even ·)).card : ℤ)
  have hED : HasProd
      (fun i : ℕ ↦ (∑' j : ℕ, (X : ℤ⟦X⟧) ^ (((i + 1) * 2) * j)) *
        (1 + X ^ ((i + 1) * s))) (E * D) := by
    simpa [E, D] using amp_hasProd_even_counts.mul (amp_hasProd_scaled_distinct s hs0)
  have hLprod : HasProd
      (fun i : ℕ ↦ 1 + ∑' j : ℕ,
        (if Even (j + 1) ∨ s ≤ j + 1 then (1 : ℤ) else 0) •
          (X : ℤ⟦X⟧) ^ ((i + 1) * (j + 1))) (E * D) := by
    convert hED using 1
    funext i
    rw [amp_lhs_factor s (i + 1) hs (by omega)]
    congr 2
    funext j
    congr 1
    ring
  have hLseries :
      Nat.Partition.genFun (fun _ c ↦ if Even c ∨ s ≤ c then (1 : ℤ) else 0) = E * D :=
    (Nat.Partition.hasProd_genFun
      (fun _ c ↦ if Even c ∨ s ≤ c then (1 : ℤ) else 0)).unique hLprod
  have hEO : HasProd
      (fun i : ℕ ↦
        (if Even (i + 1) then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1) *
        (if s ∣ i + 1 ∧ Odd ((i + 1) / s) then
          ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1)) (E * O) := by
    simpa [E, O] using
      (Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ Even).mul
        (amp_hasProd_odd_multiples s hs)
  have hPprod : HasProd
      (fun i : ℕ ↦ if Even (i + 1) ∨ (s ∣ i + 1 ∧ Odd ((i + 1) / s)) then
        ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1) (E * O) := by
    convert hEO using 1
    funext i
    by_cases he : Even (i + 1)
    · have hnq : ¬(s ∣ i + 1 ∧ Odd ((i + 1) / s)) := by
        rintro ⟨hdiv, hodd⟩
        apply Nat.not_even_iff_odd.mpr ?_ he
        rw [← Nat.div_mul_cancel hdiv]
        exact hodd.mul hs
      simp [he, hnq]
    · by_cases hq : s ∣ i + 1 ∧ Odd ((i + 1) / s)
      · simp [he, hq]
      · simp [he, hq]
  have hRseries :
      (PowerSeries.mk fun n ↦
        ((Nat.Partition.restricted n fun m ↦ Even m ∨ (s ∣ m ∧ Odd (m / s))).card : ℤ)) =
        E * O :=
    (Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ
      (fun m ↦ Even m ∨ (s ∣ m ∧ Odd (m / s)))).unique hPprod
  calc
    Nat.Partition.genFun (fun _ c ↦ if Even c ∨ s ≤ c then (1 : ℤ) else 0) = E * D :=
      hLseries
    _ = E * O := congrArg (E * ·) (by simpa [D, O] using amp_scaled_euler s hs0)
    _ = PowerSeries.mk fun n ↦
        ((Nat.Partition.restricted n fun m ↦ Even m ∨ (s ∣ m ∧ Odd (m / s))).card : ℤ) :=
      hRseries.symm

/--
**Andrews' generalization of MacMahon's partition theorem.** For all natural numbers $r$ and
$n$, the number of partitions of $n$ in which every part occurring an odd number of times occurs
at least $2r + 1$ times equals the number of partitions of $n$ in which every odd part is
congruent to $2r + 1$ modulo $4r + 2$.

For $r = 1$ this is MacMahon's partition theorem: the first condition says that no part occurs
exactly once, and the second that every part is even or congruent to $3$ modulo $6$.

The proof compares generating functions in $q$. Both sides factor through the product over the
even parts, and the remaining factors agree by Euler's theorem that partitions into odd parts and
partitions into distinct parts are equinumerous, applied with $q$ replaced by $q^{2r+1}$.

Proves `Wanted` entry `andrews_macmahon_partition_identity`.

Source: Beaullah Mugwangwavari and Darlison Nyirenda, "A Note on the
Andrews-Ericksson-Petrov-Romick Bijection for MacMahon's Partition Theorem",
Journal of Integer Sequences 24 (2021), Article 21.5.6, Theorem `andthm`
(Andrews' generalization), source lines 113–115,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Nyirenda/nyir26.tex>.
The paper attributes the result to Andrews.
-/
public theorem andrews_macmahon_partition_identity
    (r n : ℕ) :
    Set.ncard { p : Nat.Partition n |
      ∀ m ∈ p.parts, Odd (p.parts.count m) → 2 * r + 1 ≤ p.parts.count m } =
    Set.ncard { p : Nat.Partition n |
      ∀ m ∈ p.parts, Odd m → m % (4 * r + 2) = 2 * r + 1 } := by
  let s := 2 * r + 1
  have hs : Odd s := odd_two_mul_add_one r
  have hmodulus : 4 * r + 2 = 2 * s := by
    simp [s]
    ring
  have hseries := congrArg (PowerSeries.coeff n) (amp_genFun_eq_restricted s hs)
  rw [amp_coeff_genFun_indicator, PowerSeries.coeff_mk] at hseries
  have hcard :
      (Finset.univ.filter fun p : Nat.Partition n ↦
        ∀ m ∈ p.parts, Even (p.parts.count m) ∨ s ≤ p.parts.count m).card =
      (Nat.Partition.restricted n fun m ↦ Even m ∨ (s ∣ m ∧ Odd (m / s))).card := by
    exact_mod_cast hseries
  calc
    Set.ncard { p : Nat.Partition n |
        ∀ m ∈ p.parts, Odd (p.parts.count m) → 2 * r + 1 ≤ p.parts.count m } =
        (Finset.univ.filter fun p : Nat.Partition n ↦
          ∀ m ∈ p.parts, Odd (p.parts.count m) →
            2 * r + 1 ≤ p.parts.count m).card :=
      amp_ncard_setOf_eq_card_filter n _
    _ = (Finset.univ.filter fun p : Nat.Partition n ↦
          ∀ m ∈ p.parts, Even (p.parts.count m) ∨ s ≤ p.parts.count m).card := by
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, s]
      simp_rw [amp_odd_imp_iff_even_or]
    _ = (Nat.Partition.restricted n fun m ↦
          Even m ∨ (s ∣ m ∧ Odd (m / s))).card := hcard
    _ = (Finset.univ.filter fun p : Nat.Partition n ↦
          ∀ m ∈ p.parts, Odd m → m % (4 * r + 2) = 2 * r + 1).card := by
      rw [Nat.Partition.restricted]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hmodulus]
      simp only [s]
      simp_rw [← amp_odd_imp_mod_iff_even_or (2 * r + 1) _ hs]
    _ = Set.ncard { p : Nat.Partition n |
          ∀ m ∈ p.parts, Odd m → m % (4 * r + 2) = 2 * r + 1 } :=
      (amp_ncard_setOf_eq_card_filter n _).symm

end MetaMathlibExt
