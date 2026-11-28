/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MonochromaticLinearEquations
import all MathlibExt.Combinatorics.MonochromaticLinearEquations.Recolouring
import all MathlibExt.Combinatorics.MonochromaticLinearEquations.NoCancelingPartition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uncommonness of odd-length equations over the integers

We transfer a fractional colouring from a prime modulus. Differences of modular solutions
lift to integer kernel vectors: choose a pivot coefficient invertible modulo the prime, and
use it as a common denominator for the other coordinates. Adding a multiple of a positive
solution makes each translation nonnegative. A bounded enlargement of the box can therefore
receive any residue fibre into any other. Polynomial upper and lower bounds give arbitrarily
large boxes for which this enlargement changes the total count by an arbitrarily small
proportion. We round the transferred weights independently, budgeting repeated entries
separately.

## References

* K. P. Costello and G. Elvin, *Avoiding monochromatic solutions to 3-term equations*,
  J. Comb. 14(3) (2023), 281–304, Lemma 2.1. We adapt their transference from cyclic
  groups to integer intervals to fractional colourings and a prime modulus.
* L. P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least Three Colors*,
  INTEGERS 25 (2025), Article A88, Section 3, states the transference result as Lemma 1,
  credits Costello and Elvin, and uses it to deduce Corollary 1 from Theorem 1.
-/

namespace MetaMathlibExt
namespace isUncommonOverIntegers_of_odd

open Finset Filter
open isUncommonOverIntegers_of_two isUncommonOverIntegers_of_not_hasCancelingPartition

private def residues {k p : ℕ} (x : Fin k → ℤ) : Fin k → ZMod p := fun i => x i

private def modularSolutions {k : ℕ} (a : Fin k → ℤ) (p : ℕ) [NeZero p] :
    Finset (Fin k → ZMod p) := univ.filter fun u => ∑ i, a i • u i = 0

private lemma mem_modularSolutions {k p : ℕ} [NeZero p] {a : Fin k → ℤ}
    {u : Fin k → ZMod p} : u ∈ modularSolutions a p ↔ ∑ i, (a i : ZMod p) * u i = 0 := by
  simp [modularSolutions, zsmul_eq_mul]

private lemma cast_dot {k p : ℕ} (a x : Fin k → ℤ) :
    (dot a x : ZMod p) = ∑ i, (a i : ZMod p) * residues x i := by
  simp [dot, residues]

private lemma residues_mem {k p : ℕ} [NeZero p] {a x : Fin k → ℤ} {n : ℕ}
    (hx : x ∈ solutions a n) : residues x ∈ modularSolutions a p := by
  rw [mem_modularSolutions, ← cast_dot]
  have he : dot a x = 0 := (mem_solutions.mp hx).2
  rw [he, Int.cast_zero]

-- Lift the nonpivot entries after division by the pivot coefficient in the field.
private lemma lift_kernel {d p : ℕ} [Fact p.Prime] (a : Fin (d + 1) → ℤ)
    (h₀ : (a 0 : ZMod p) ≠ 0) (u : Fin (d + 1) → ZMod p)
    (hu : u ∈ modularSolutions a p) :
    ∃ z : Fin (d + 1) → ℤ, dot a z = 0 ∧ residues z = u := by
  let y (i : Fin d) : ℤ := (((a 0 : ZMod p)⁻¹ * u i.succ).val : ℤ)
  let z : Fin (d + 1) → ℤ := Fin.cons (-∑ i, a i.succ * y i) (fun i => a 0 * y i)
  have hz : dot a z = 0 := by
    simp only [dot, Fin.sum_univ_succ, z, Fin.cons_zero, Fin.cons_succ, mul_neg]
    simp_rw [show ∀ i : Fin d, a i.succ * (a 0 * y i) = a 0 * (a i.succ * y i) by
      intro i; ring]
    rw [← mul_sum, neg_add_cancel]
  have tail (i : Fin d) : residues z i.succ = u i.succ := by
    simp [residues, z, y, h₀]
  have hcast := cast_dot (p := p) a z
  rw [hz, Int.cast_zero] at hcast
  have he := hcast.symm.trans (mem_modularSolutions.mp hu).symm
  simp only [Fin.sum_univ_succ, tail] at he
  have head : residues z 0 = u 0 := mul_left_cancel₀ h₀ (add_right_cancel he)
  exact ⟨z, hz, funext (Fin.cases head tail)⟩

private lemma lift_nonneg {d p : ℕ} [Fact p.Prime] (a b : Fin (d + 1) → ℤ)
    (h₀ : (a 0 : ZMod p) ≠ 0) (hb : ∀ i, 0 < b i) (he : dot a b = 0)
    (u : Fin (d + 1) → ZMod p) (hu : u ∈ modularSolutions a p) :
    ∃ z : Fin (d + 1) → ℤ, dot a z = 0 ∧ (∀ i, 0 ≤ z i) ∧ residues z = u := by
  obtain ⟨z, hz, hres⟩ := lift_kernel a h₀ u hu
  let M := ∑ i, |z i|
  let v (i : Fin (d + 1)) : ℤ := z i + (p : ℤ) * M * b i
  have hM : 0 ≤ M := sum_nonneg fun i _ => abs_nonneg (z i)
  have hp : (1 : ℤ) ≤ p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  refine ⟨v, ?_, ?_, ?_⟩
  · change (∑ i, a i * b i) = 0 at he
    simp only [dot, v, mul_add, sum_add_distrib, hz, zero_add]
    simp_rw [show ∀ i, a i * ((p : ℤ) * M * b i) = ((p : ℤ) * M) * (a i * b i) by
      intro i; ring]
    rw [← mul_sum, he, mul_zero]
  · intro i
    have hzi : |z i| ≤ M := single_le_sum (fun j _ => abs_nonneg (z j)) (mem_univ i)
    have hb' : 1 ≤ b i := hb i
    have hle : M ≤ (p : ℤ) * M * b i := calc
      M ≤ (p : ℤ) * M := le_mul_of_one_le_left hM hp
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hb'
    have := neg_abs_le (z i)
    dsimp [v]
    omega
  · ext i
    simpa [residues, v] using congrFun hres i

private def fibre {k p : ℕ} [NeZero p] (a : Fin k → ℤ) (n : ℕ)
    (u : Fin k → ZMod p) : Finset (Fin k → ℤ) := (solutions a n).filter fun x => residues x = u

-- The translates are bounded simultaneously because there are finitely many residue patterns.
private lemma fibre_le {d p : ℕ} [Fact p.Prime] (a b : Fin (d + 1) → ℤ)
    (h₀ : (a 0 : ZMod p) ≠ 0) (hb : ∀ i, 0 < b i) (he : dot a b = 0) :
    ∃ D : ℕ, ∀ n u v, u ∈ modularSolutions a p → v ∈ modularSolutions a p →
      (fibre a n u).card ≤ (fibre a (n + D) v).card := by
  classical
  let T := modularSolutions a p
  have lift (u : ↥T) := lift_nonneg a b h₀ hb he u.val u.property
  choose z hz hnonneg hres using lift
  let D := ∑ u : ↥T, ∑ i, (z u i).natAbs
  refine ⟨D, fun n u v hu hv => ?_⟩
  have hdiff : v - u ∈ T := by
    rw [show T = modularSolutions a p from rfl, mem_modularSolutions]
    simp only [Pi.sub_apply, mul_sub, sum_sub_distrib, mem_modularSolutions.mp hu,
      mem_modularSolutions.mp hv, sub_self]
  let w : ↥T := ⟨v - u, hdiff⟩
  have hD (i) : z w i ≤ (D : ℤ) := by
    have hle : (z w i).natAbs ≤ D :=
      (single_le_sum (f := fun j => (z w j).natAbs)
        (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
          (single_le_sum (f := fun t => ∑ j, (z t j).natAbs)
            (fun _ _ => Nat.zero_le _) (mem_univ w))
    have hcast : ((z w i).natAbs : ℤ) ≤ (D : ℤ) := by exact_mod_cast hle
    simpa only [Int.natCast_natAbs, abs_of_nonneg (hnonneg w i)] using hcast
  apply card_le_card_of_injOn (fun x : Fin (d + 1) → ℤ => x + z w)
  · intro x hx
    obtain ⟨hx, hr⟩ := mem_filter.mp hx
    obtain ⟨hbox, hdot⟩ := mem_solutions.mp hx
    apply mem_filter.mpr
    refine ⟨mem_solutions.mpr ⟨fun i => ?_, ?_⟩, ?_⟩
    · have := hbox i
      have := hnonneg w i
      have := hD i
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · simp only [Pi.add_apply, mul_add, sum_add_distrib, hdot, hz w, add_zero]
    · have hadd : residues (p := p) (x + z w) = residues x + residues (z w) := by
        ext i
        simp [residues]
      rw [hadd, hr, hres w]
      change u + (v - u) = v
      exact (add_comm u (v - u)).trans (sub_add_cancel v u)
  · intro x _ y _ h
    exact add_right_cancel h

private lemma solutions_mono {k : ℕ} (a : Fin k → ℤ) {n N : ℕ} (hn : n ≤ N) :
    solutions a n ⊆ solutions a N := by
  intro x hx
  obtain ⟨hx, he⟩ := mem_solutions.mp hx
  exact mem_solutions.mpr ⟨fun i => ⟨(hx i).1, (hx i).2.trans (by exact_mod_cast hn)⟩, he⟩

-- The coordinates other than the pivot determine a solution uniquely.
private lemma solutions_le {d : ℕ} (a : Fin (d + 1) → ℤ) (ha : a 0 ≠ 0) (n : ℕ) :
    (solutions a n).card ≤ n ^ d := by
  let box := Fintype.piFinset fun _ : Fin d => Icc (1 : ℤ) n
  have hc : box.card = n ^ d := by simp [box, Fintype.card_piFinset, Int.card_Icc]
  rw [← hc]
  apply card_le_card_of_injOn (fun (x : Fin (d + 1) → ℤ) (i : Fin d) => x i.succ)
  · intro x hx
    exact Fintype.mem_piFinset.mpr fun i => mem_Icc.mpr ((mem_solutions.mp hx).1 i.succ)
  · intro x hx y hy h
    have tail (i : Fin d) : x i.succ = y i.succ := congrFun h i
    have he := (mem_solutions.mp hx).2.trans (mem_solutions.mp hy).2.symm
    simp only [Fin.sum_univ_succ, tail] at he
    exact funext (Fin.cases (mul_left_cancel₀ ha (add_right_cancel he)) tail)

-- Polynomial growth forces some small relative increment in a fixed-length chain of boxes.
private lemma frequently_small_growth {d : ℕ} (a b : Fin (d + 1) → ℤ) (hd : 0 < d)
    (ha : a 0 ≠ 0) (hb : ∀ i, 0 < b i) (he : dot a b = 0) (D Q : ℕ) :
    ∃ᶠ n : ℕ in atTop, 0 < (solutions a n).card ∧
      Q * (solutions a (n + D)).card ≤ (Q + 1) * (solutions a n).card := by
  obtain ⟨C, hC, hmany⟩ := many_solutions a b hd ha hb he
  apply frequently_atTop.mpr
  intro n₀
  let L := Q * (2 * C) ^ d + 1
  let m := max n₀ (L * D) + 1
  let N := C * m
  have hm : 0 < m := Nat.succ_pos _
  have hmN : m ≤ N := Nat.le_mul_of_pos_left _ hC
  have hn₀ : n₀ ≤ N := (le_max_left n₀ (L * D)).trans (Nat.le_succ _ |>.trans hmN)
  have hlo (t : ℕ) : m ^ d ≤ (solutions a (N + t * D)).card :=
    (hmany m).trans (card_le_card (solutions_mono a (Nat.le_add_right ..)))
  by_contra! hf
  have step (t : ℕ) :
      Q * (solutions a (N + t * D)).card + m ^ d ≤
        Q * (solutions a (N + (t + 1) * D)).card := by
    have ht : (Q + 1) * (solutions a (N + t * D)).card <
        Q * (solutions a (N + (t + 1) * D)).card := by
      simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using
        hf (N + t * D) (hn₀.trans (Nat.le_add_right ..)) ((pow_pos hm d).trans_le (hlo t))
    rw [Nat.add_mul, one_mul] at ht
    exact (Nat.add_le_add_left (hlo t) _).trans ht.le
  have grow (t : ℕ) : t * m ^ d ≤ Q * (solutions a (N + t * D)).card := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul]
      exact (Nat.add_le_add_right ih _).trans (step t)
  have htop : N + L * D ≤ 2 * C * m := by
    rw [Nat.mul_assoc, two_mul]
    exact Nat.add_le_add_left ((le_max_right n₀ (L * D)).trans (Nat.le_succ _ |>.trans hmN)) N
  have h := (grow L).trans
    (Nat.mul_le_mul_left Q ((solutions_le a ha _).trans (Nat.pow_le_pow_left htop d)))
  rw [mul_pow, ← mul_assoc] at h
  dsimp only [L] at h
  rw [Nat.add_mul, one_mul] at h
  have : 0 < m ^ d := pow_pos hm _
  omega

-- Averaging the injection bound over all target fibres bounds each source fibre.
private lemma transfer_weight {k p : ℕ} [NeZero p] (a : Fin k → ℤ) (n D : ℕ)
    (hD : ∀ u v, u ∈ modularSolutions a p → v ∈ modularSolutions a p →
      (fibre a n u).card ≤ (fibre a (n + D) v).card)
    (W : (Fin k → ZMod p) → ℝ) (hW : ∀ u, 0 ≤ W u) :
    (∑ x ∈ solutions a n, W (residues x)) ≤
      (∑ u ∈ modularSolutions a p, W u) / (modularSolutions a p).card *
        (solutions a (n + D)).card := by
  let T := modularSolutions a p
  have ht : 0 < (T.card : ℝ) := by
    have hmem : (0 : Fin k → ZMod p) ∈ T := by
      change _ ∈ modularSolutions a p
      simp [mem_modularSolutions]
    exact_mod_cast card_pos.mpr ⟨0, hmem⟩
  have maps {N : ℕ} (x) (hx : x ∈ solutions a N) : residues x ∈ T := residues_mem hx
  have hcard : (solutions a (n + D)).card = ∑ u ∈ T, (fibre a (n + D) u).card :=
    card_eq_sum_card_fiberwise (fun x hx => maps x hx)
  have hf (u) (hu : u ∈ T) : ((fibre a n u).card : ℝ) ≤
      (solutions a (n + D)).card / T.card := by
    apply (le_div_iff₀ ht).mpr
    have hle := sum_le_sum (s := T) fun v hv => hD u v hu hv
    simp only [sum_const, Nat.nsmul_eq_mul, ← hcard] at hle
    rw [mul_comm]
    exact_mod_cast hle
  rw [← sum_fiberwise_of_maps_to' (fun x hx => maps x hx) W]
  change (∑ u ∈ T, ∑ _x ∈ fibre a n u, W u) ≤ _
  simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ∑ u ∈ T, ((solutions a (n + D)).card / T.card : ℝ) * W u :=
      sum_le_sum fun u hu => mul_le_mul_of_nonneg_right (hf u hu) (hW u)
    _ = _ := by rw [← mul_sum]; change _ = (∑ u ∈ T, W u) / T.card * _; ring

-- Use the existing independent rounding on distinct tuples, then add all repeated tuples.
private lemma round_solutions {k r : ℕ} [Nonempty (Fin k)] [NeZero r]
    (a : Fin k → ℤ) (n : ℕ) (w : ℤ → Fin r → ℝ)
    (hw : ∀ z c, 0 ≤ w z c) (hs : ∀ z, ∑ c, w z c = 1) :
    ∃ χ : ℤ → Fin r, (((solutions a n).filter (mono χ)).card : ℝ) ≤
      (∑ x ∈ solutions a n, ∑ c, ∏ i, w (x i) c) + (repeats (solutions a n)).card := by
  classical
  let S := solutions a n
  let B := repeats S
  let G := S \ B
  obtain ⟨χ, hχ⟩ := round_good n G (fun x hx i =>
    mem_Icc.mpr ((mem_solutions.mp (mem_sdiff.mp hx).1).1 i)) (fun x hx => by
      by_contra hi
      exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1, hi⟩)) w hw hs
  have cover : S.filter (mono χ) ⊆ G.filter (mono χ) ∪ B := by
    intro x hx
    obtain ⟨hx, hm⟩ := mem_filter.mp hx
    by_cases hb : x ∈ B
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hx, hb⟩, hm⟩)
  refine ⟨χ, ?_⟩
  calc
    _ ≤ ((G.filter (mono χ)).card : ℝ) + B.card := by
      exact_mod_cast (card_le_card cover).trans (card_union_le ..)
    _ ≤ _ := add_le_add_left (hχ.trans (sum_le_sum_of_subset_of_nonneg sdiff_subset
      (fun x _ _ => sum_nonneg fun c _ => prod_nonneg fun i _ => hw (x i) c))) _

end isUncommonOverIntegers_of_odd

open Finset Filter isUncommonOverIntegers_of_odd isUncommonOverIntegers_of_two
  isUncommonOverIntegers_of_not_hasCancelingPartition in
/-- **Uncommonness of odd-length equations over the integers.** Let $m \ge 1$ and let
$a_1, \dots, a_{2m+1}$ be nonzero integers, at least one negative and at least one positive.
Then for every $r \ge 3$ the equation $a_1x_1 + \cdots + a_{2m+1}x_{2m+1} = 0$ is
$r$-uncommon over the integers.

The sign condition excludes equations such as $x_1 + x_2 + x_3 = 0$, which have no solutions
in positive integers and for which the proportion of monochromatic solutions is undefined.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 1 (`integers-2025-A88-cor-1`). -/
public theorem isUncommonOverIntegers_of_odd (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ) (ha : ∀ i, a i ≠ 0) (hsign : ∃ i j, a i < 0 ∧ 0 < a j)
    (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r := by
  classical
  let k := 2 * m + 1
  have hk : 3 ≤ k := by dsimp [k]; omega
  let : NeZero r := ⟨by omega⟩
  obtain ⟨b, hb, he⟩ := positive_solution a hsign
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes ((∑ i, (a i).natAbs) + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hlt (i) : (a i).natAbs < p := lt_of_lt_of_le
    (Nat.lt_succ_of_le (single_le_sum (fun j _ => Nat.zero_le (a j).natAbs) (mem_univ i))) hp
  have hcop (i) : (a i).natAbs.Coprime (Fintype.card (ZMod p)) := by
    rw [ZMod.card, Nat.coprime_comm, hprime.coprime_iff_not_dvd]
    exact fun hd => (not_le_of_gt (hlt i)) (Nat.le_of_dvd (Int.natAbs_pos.mpr (ha i)) hd)
  have h₀ : (a 0 : ZMod p) ≠ 0 := by
    intro hz
    exact ha 0 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz) (by simpa using hlt 0))
  obtain ⟨w, hw, hsum, hdeficit⟩ := isUncommonOverFiniteGroup_of_odd (ZMod p) m hm a hcop r hr
  let T := modularSolutions a p
  let R : ℝ := (r : ℝ) ^ (k - 1)
  let W (u : Fin k → ZMod p) := ∑ c, ∏ i, w c (u i)
  let μ : ℝ := R * (∑ u ∈ T, W u) / T.card
  have hR : 0 < R := by dsimp [R]; positivity
  have hW (u) : 0 ≤ W u := sum_nonneg fun c _ => prod_nonneg fun i _ => hw c (u i)
  have hT : 0 < (T.card : ℝ) := by
    have hmem : (0 : Fin k → ZMod p) ∈ T := by
      change _ ∈ modularSolutions a p
      simp [mem_modularSolutions]
    exact_mod_cast card_pos.mpr ⟨0, hmem⟩
  have hμ₀ : 0 ≤ μ := div_nonneg (mul_nonneg hR.le (sum_nonneg fun u _ => hW u)) hT.le
  have hμ₁ : μ < 1 := by
    apply (div_lt_one hT).mpr
    change R * (∑ c, ∑ u ∈ T, ∏ i, w c (u i)) < T.card at hdeficit
    rw [sum_comm] at hdeficit
    exact hdeficit
  let δ : ℝ := (1 - μ) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Q, hQ⟩ := exists_nat_ge ((1 + R) / δ)
  have hQδ : 1 + R ≤ (Q : ℝ) * δ := (div_le_iff₀ hδ).mp hQ
  have hQpos : (0 : ℝ) < Q := by
    by_contra! h
    linarith [mul_nonpos_of_nonpos_of_nonneg h hδ.le]
  obtain ⟨D, hD⟩ := fibre_le a b h₀ hb he
  apply (uncommon_iff a).mpr
  refine ⟨δ / 2, by positivity, ?_⟩
  apply ((frequently_small_growth a b (by omega) (ha 0) hb he D Q).and_eventually
    (sparse_repeats hk a b ha hb he Q)).mono
  rintro n ⟨⟨hn, hslow⟩, hrep⟩
  let S : ℝ := (solutions a n).card
  let Slarge : ℝ := (solutions a (n + D)).card
  let B : ℝ := (repeats (solutions a n)).card
  have hS : 0 < S := by dsimp [S]; exact_mod_cast hn
  have hslow' : (Q : ℝ) * Slarge ≤ ((Q : ℝ) + 1) * S := by
    dsimp only [Slarge, S]
    exact_mod_cast hslow
  have hrep' : (Q : ℝ) * B ≤ S := by dsimp [B, S]; exact_mod_cast hrep
  have hlarge : Slarge ≤ (1 + δ) * S := by
    apply le_of_mul_le_mul_left _ hQpos
    calc
      _ ≤ ((Q : ℝ) + 1) * S := hslow'
      _ ≤ ((Q : ℝ) + (Q : ℝ) * δ) * S := by
        gcongr
        linarith
      _ = _ := by ring
  have hsmall : R * B ≤ δ * S := calc
    _ ≤ ((Q : ℝ) * δ) * B := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [B]; positivity)
      linarith
    _ = δ * ((Q : ℝ) * B) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrep' hδ.le
  obtain ⟨χ, hχ⟩ := round_solutions a n (fun z c => w c (z : ZMod p))
    (fun z c => hw c z) (fun z => hsum z)
  have hweight : R * (∑ x ∈ solutions a n, W (residues x)) ≤ μ * Slarge := by
    calc
      _ ≤ R * ((∑ u ∈ T, W u) / T.card * Slarge) :=
        mul_le_mul_of_nonneg_left (transfer_weight a n D (hD n) W hW) hR.le
      _ = _ := by dsimp only [μ]; ring
  refine ⟨χ, ?_⟩
  change R * (((solutions a n).filter (mono χ)).card : ℝ) < (1 - δ / 2) * S
  have hmono := mul_le_mul_of_nonneg_left hχ hR.le
  change R * _ ≤ R * ((∑ x ∈ solutions a n, W (residues x)) + B) at hmono
  rw [mul_add] at hmono
  have hbound : μ * Slarge ≤ μ * S + δ * S := calc
    _ ≤ μ * ((1 + δ) * S) := mul_le_mul_of_nonneg_left hlarge hμ₀
    _ = μ * S + μ * (δ * S) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left (mul_nonneg hδ.le hS.le) hμ₁.le)
  have hsave : 0 < δ * S := mul_pos hδ hS
  have heq : μ * S + 2 * (δ * S) = (1 - δ) * S := by dsimp only [δ]; ring
  have heq' : (1 - δ / 2) * S = (1 - δ) * S + (δ * S) / 2 := by ring
  linarith only [hmono, hweight, hsmall, hbound, hsave, heq, heq']

end MetaMathlibExt
