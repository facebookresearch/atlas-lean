/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/871.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definitions `conjecture` and `disprovedForm` and the statement of
`conjecture_refuted`.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 871 is false

The theorem `conjecture_refuted` constructs an asymptotic basis of order two whose number
of unordered representations tends to infinity and which admits no partition into two
asymptotic bases. This gives a counterexample to Erdős Problem 871, resolved by Daniel
Larsen. [Larsen, *Three Questions of Erdős-Nathanson*](https://arxiv.org/abs/2603.03472)

The odd elements are generators `gen i`, each congruent to 1 modulo 8 and more than twice its
predecessor. At level `k` we consider all majority subsets `U` of a block of `2k + 1` generator
indices. We assign an odd target `special k U` to each such subset. All later generators exceed
the target, and we omit the even complements of the remaining generators outside `U`. Thus every
representation of the target uses a generator indexed by `U`. In any partition, choose a
monochromatic majority in a sufficiently late block. The other part misses its target.

To prove the representation bound, note that the omitted even numbers are all 2 modulo 8,
leaving enough pairs of even summands for every large even number. For odd numbers, the gaps
between targets allow a block to encounter omissions from at most one target. At the target
itself the whole majority survives. Away from the target at most one generator of the block
is lost, because a nonzero difference of two generators determines both indices.
-/

@[expose] public section

open Filter

namespace MathlibExt.NumberTheory.ErdosProblem871Wanted

/-- **Erdős Problem 871 (splitting rich bases of order 2).** The statement that for every set $A$
of natural numbers such that every sufficiently large $n$ is $a + b$ with $a, b \in A$ and, for
every natural number $t$, every sufficiently large $n$ has at least $t$ representations
$n = a + b$ with $a, b \in A$ and $a \le b$, the set $A$ is the disjoint union of two sets $B$ and
$C$ such that every sufficiently large $n$ is $a + b$ with $a, b \in B$ and every sufficiently
large $n$ is $a + b$ with $a, b \in C$. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ),
    (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
    (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
      pairs.card ≥ t ∧
        ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
    ∃ (B C : Set ℕ),
      (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
      Disjoint B C ∧
      (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
      (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n)

/-- **Negation of the Erdős Problem 871 statement.** This is the proposition that there is a set
$A$ of natural numbers such that every sufficiently large $n$ is $a + b$ with $a, b \in A$ and,
for every natural number $t$, every sufficiently large $n$ has at least $t$ representations
$n = a + b$ with $a, b \in A$ and $a \le b$, but $A$ is not the disjoint union of two sets $B$
and $C$ such that every sufficiently large $n$ is $a + b$ with $a, b \in B$ and every
sufficiently large $n$ is $a + b$ with $a, b \in C$. -/
def disprovedForm : Prop := ¬ conjecture

/-! ### The generators -/

/-- The odd generators of the counterexample, `1` modulo `8` and growing faster than doubling. -/
private def gen : ℕ → ℕ
  | 0 => 1
  | i + 1 => 2 ^ (i + 6) * (gen i + 1) + 1

private lemma gen_succ (i : ℕ) : gen (i + 1) = 2 ^ (i + 6) * (gen i + 1) + 1 := rfl

private lemma gen_mod (i : ℕ) : gen i % 8 = 1 := by
  cases i with
  | zero => rfl
  | succ i =>
    rw [gen_succ]
    have : 2 ^ (i + 6) * (gen i + 1) = 8 * (2 ^ i * 8 * (gen i + 1)) := by ring
    omega

private lemma two_mul_gen_lt_succ (i : ℕ) : 2 * gen i < gen (i + 1) := by
  rw [gen_succ]
  have h : 64 ≤ 2 ^ (i + 6) := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (i + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

private lemma gen_strictMono : StrictMono gen :=
  strictMono_nat_of_lt_succ fun i => by have := two_mul_gen_lt_succ i; omega

private lemma two_mul_gen_lt {i j : ℕ} (h : i < j) : 2 * gen i < gen j :=
  (two_mul_gen_lt_succ i).trans_le (gen_strictMono.monotone h)

private lemma gen_sidon_aux {a b c d : ℕ} (hba : b ≤ a) (hdc : d ≤ c)
    (h : gen a + gen b = gen c + gen d) : a = c ∧ b = d := by
  rcases lt_trichotomy a c with hac | rfl | hca
  · have h1 := two_mul_gen_lt hac
    have h2 := gen_strictMono.monotone hba
    omega
  · exact ⟨rfl, gen_strictMono.injective (by omega)⟩
  · have h1 := two_mul_gen_lt hca
    have h2 := gen_strictMono.monotone hdc
    omega

/-- The generators form a Sidon set: a sum of two of them determines the two summands. -/
private lemma gen_sidon {a b c d : ℕ} (h : gen a + gen b = gen c + gen d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total b a with hba | hab <;> rcases le_total d c with hdc | hcd
  · exact Or.inl (gen_sidon_aux hba hdc h)
  · obtain ⟨h1, h2⟩ := gen_sidon_aux hba hcd (by omega)
    exact Or.inr ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := gen_sidon_aux hab hdc (by omega)
    exact Or.inr ⟨h2, h1⟩
  · obtain ⟨h1, h2⟩ := gen_sidon_aux hab hcd (by omega)
    exact Or.inl ⟨h2, h1⟩

/-! ### Levels, special points and holes -/

/-- The largest generator of level `k`, of index `(k + 1)² - 1`. -/
private def top (k : ℕ) : ℕ := gen (k * k + 2 * k)

/-- The scale `2 ^ (k + 1) ^ 2` of level `k`; it bounds the codes of the subsets of the blocks of
the levels up to `k`. -/
private def scale (k : ℕ) : ℕ := 2 ^ (k * k + 2 * k + 1)

/-- The block of the `2k + 1` indices of level `k`. -/
private def block (k : ℕ) : Finset ℕ := Finset.Ico (k * k) (k * k + 2 * k + 1)

/-- A set of indices is admissible at level `k` if it holds more than half of the block. -/
private def Adm (k : ℕ) (U : Finset ℕ) : Prop := U ⊆ block k ∧ k + 1 ≤ U.card

/-- The special point of the set of indices `U` at level `k`, congruent to `3` modulo `8`. -/
private def special (k : ℕ) (U : Finset ℕ) : ℕ :=
  8 * ((top k + 1) * (scale k + ∑ i ∈ U, 2 ^ i)) + 3

/-- The holes: the numbers `special k U - gen i` with `i ∉ U` and `i < (k + 1)²`. -/
private def holes : Set ℕ :=
  {h | ∃ k U i, Adm k U ∧ i < k * k + 2 * k + 1 ∧ i ∉ U ∧ h + gen i = special k U}

/-- The counterexample: the generators and the even numbers that are not holes. -/
private def basisSet : Set ℕ := {a | a ∈ Set.range gen ∨ (a % 2 = 0 ∧ a ∉ holes)}

/-- `n` has reached the special points of level `k`, up to the largest generator of the level. -/
private def Reached (k n : ℕ) : Prop := 8 * ((top k + 1) * scale k) + 3 ≤ n + top k

private lemma gen_le_top {i k : ℕ} (h : i < k * k + 2 * k + 1) : gen i ≤ top k :=
  gen_strictMono.monotone (by omega)

private lemma top_mono {k k' : ℕ} (h : k ≤ k') : top k ≤ top k' :=
  gen_strictMono.monotone (by nlinarith)

private lemma one_le_scale (k : ℕ) : 1 ≤ scale k := Nat.one_le_two_pow

private lemma two_le_scale (k : ℕ) : 2 ≤ scale k :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k * k + 2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma scale_mono {k k' : ℕ} (h : k ≤ k') : scale k ≤ scale k' :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

private lemma code_lt {k : ℕ} {U : Finset ℕ} (hU : U ⊆ block k) : ∑ i ∈ U, 2 ^ i < scale k :=
  Nat.geomSum_lt (le_refl 2) fun _ hi => (Finset.mem_Ico.mp (hU hi)).2

private lemma special_mod (k : ℕ) (U : Finset ℕ) : special k U % 8 = 3 := by
  unfold special
  omega

private lemma holes_mod {h : ℕ} (hh : h ∈ holes) : h % 8 = 2 := by
  obtain ⟨k, U, i, -, -, -, he⟩ := hh
  have h1 := gen_mod i
  have h2 := special_mod k U
  omega

private lemma gen_mem (i : ℕ) : gen i ∈ basisSet := Or.inl ⟨i, rfl⟩

private lemma mem_basisSet_of_even {e : ℕ} (he : e % 2 = 0) (he8 : e % 8 ≠ 2) :
    e ∈ basisSet :=
  Or.inr ⟨he, fun hh => he8 (holes_mod hh)⟩

private lemma special_ge (k : ℕ) (U : Finset ℕ) :
    8 * ((top k + 1) * scale k) + 3 ≤ special k U := by
  unfold special
  have : (top k + 1) * scale k ≤ (top k + 1) * (scale k + ∑ i ∈ U, 2 ^ i) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  omega

private lemma special_lt {k : ℕ} {U : Finset ℕ} (hU : U ⊆ block k) :
    special k U < 16 * ((top k + 1) * scale k) + 3 := by
  unfold special
  have h := code_lt hU
  have h1 : (top k + 1) * (scale k + ∑ i ∈ U, 2 ^ i) < (top k + 1) * (2 * scale k) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have h2 : (top k + 1) * (2 * scale k) = 2 * ((top k + 1) * scale k) := by ring
  omega

private lemma gen_next (k : ℕ) :
    gen (k * k + 2 * k + 1) = 32 * ((top k + 1) * scale k) + 1 := by
  rw [gen_succ]
  unfold top scale
  rw [show k * k + 2 * k + 6 = (k * k + 2 * k + 1) + 5 by ring, pow_add]
  ring

/-- The special points of level `k` lie below the generators of the higher levels. -/
private lemma special_add_top_lt {k : ℕ} {U : Finset ℕ} (hU : U ⊆ block k) :
    special k U + top k < gen (k * k + 2 * k + 1) := by
  rw [gen_next]
  have h1 := special_lt hU
  have h2 : top k + 1 ≤ (top k + 1) * scale k := Nat.le_mul_of_pos_right _ (one_le_scale k)
  omega

private lemma reached_anti {k k' n : ℕ} (hkk' : k ≤ k') (h : Reached k' n) : Reached k n := by
  unfold Reached at *
  have ht := top_mono hkk'
  have hs := scale_mono hkk'
  have hs1 := one_le_scale k
  have h1 : (top k' + 1) * scale k ≤ (top k' + 1) * scale k' := Nat.mul_le_mul_left _ hs
  have h2 : top k * scale k + top k' ≤ top k' * scale k + top k := by nlinarith
  nlinarith

private lemma le_of_reached {k n : ℕ} (h : Reached k n) : 15 * top k + 19 ≤ n := by
  unfold Reached at h
  have : 2 * (top k + 1) ≤ (top k + 1) * scale k := by
    have := two_le_scale k
    nlinarith
  omega

/-- In the zone of level `k`, a hole `n - gen i` with `gen i` at most the largest generator of the
level comes from a special point of level `k`. -/
private lemma hole_level {k n i k' i' : ℕ} {U' : Finset ℕ} (hlo : Reached k n)
    (hhi : ¬ Reached (k + 1) n) (hi : gen i ≤ top k) (hU' : Adm k' U')
    (hi' : i' < k' * k' + 2 * k' + 1) (h : n - gen i + gen i' = special k' U') : k' = k := by
  have hn := le_of_reached hlo
  rcases lt_trichotomy k' k with hk | hk | hk
  · exfalso
    have h1 := special_add_top_lt hU'.1
    have h2 : gen (k' * k' + 2 * k' + 1) ≤ top k := gen_strictMono.monotone (by nlinarith)
    omega
  · exact hk
  · exfalso
    apply hhi
    apply reached_anti hk
    unfold Reached
    have h1 := special_ge k' U'
    have h2 := gen_le_top hi'
    omega

/-- Two special points of the same level within twice the largest generator are equal. -/
private lemma spacing {k : ℕ} {U V : Finset ℕ}
    (h1 : special k U ≤ special k V + 2 * top k) (h2 : special k V ≤ special k U + 2 * top k) :
    U = V := by
  have key : ∑ i ∈ U, 2 ^ i = ∑ i ∈ V, 2 ^ i := by
    by_contra hne
    unfold special at h1 h2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (top k + 1) * (scale k + ∑ i ∈ U, 2 ^ i) + (top k + 1) ≤
          (top k + 1) * (scale k + ∑ i ∈ V, 2 ^ i) := by
        rw [← Nat.mul_add_one]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    · have : (top k + 1) * (scale k + ∑ i ∈ V, 2 ^ i) + (top k + 1) ≤
          (top k + 1) * (scale k + ∑ i ∈ U, 2 ^ i) := by
        rw [← Nat.mul_add_one]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
  exact Finset.geomSum_injective (le_refl 2) key

/-! ### Many representations -/

/-- At level `k`, at least `k` generators are at most `n / 2` and have a complement outside
the holes. For odd `n` these complements belong to the basis. -/
private lemma zone {k n : ℕ} (hlo : Reached k n) (hhi : ¬ Reached (k + 1) n) :
    ∃ T : Finset ℕ, k ≤ T.card ∧ ∀ i ∈ T, 2 * gen i ≤ n ∧ n - gen i ∉ holes := by
  classical
  have hn15 := le_of_reached hlo
  have hblk : ∀ i ∈ block k, gen i ≤ top k := fun i hi =>
    gen_le_top (Finset.mem_Ico.mp hi).2
  by_cases hsp : ∃ U, Adm k U ∧ n = special k U
  · obtain ⟨U, hU, rfl⟩ := hsp
    refine ⟨U, by have := hU.2; omega, fun i hi => ⟨by have := hblk i (hU.1 hi); omega, ?_⟩⟩
    rintro ⟨k', U', i', hU', hi', hi'U', he⟩
    have hgi := hblk i (hU.1 hi)
    have hk := hole_level hlo hhi hgi hU' hi' he
    rw [hk] at hU' hi' he
    have hgi' := gen_le_top hi'
    have hUU' : U = U' := spacing (k := k) (by omega) (by omega)
    rw [← hUU'] at he hi'U'
    have hii' : i' = i := gen_strictMono.injective (by omega)
    rw [hii'] at hi'U'
    exact hi'U' hi
  · simp only [not_exists, not_and] at hsp
    have hbad : ((block k).filter fun i => n - gen i ∈ holes).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      obtain ⟨ha, k1, U1, i1, hU1, hi1, -, he1⟩ := ha
      obtain ⟨hb, k2, U2, i2, hU2, hi2, -, he2⟩ := hb
      have hga := hblk a ha
      have hgb := hblk b hb
      have hk1 := hole_level hlo hhi hga hU1 hi1 he1
      have hk2 := hole_level hlo hhi hgb hU2 hi2 he2
      rw [hk1] at hU1 hi1 he1
      rw [hk2] at hU2 hi2 he2
      have hg1 := gen_le_top hi1
      have hg2 := gen_le_top hi2
      have hU : U1 = U2 := spacing (k := k) (by omega) (by omega)
      rw [← hU] at he2
      rcases gen_sidon (a := i1) (b := b) (c := i2) (d := a) (by omega) with ⟨-, h⟩ | ⟨h, -⟩
      · exact h.symm
      · rw [h] at he1
        exact absurd (by omega : n = special k U1) (hsp U1 hU1)
    have hcard := Finset.card_filter_add_card_filter_not (s := block k)
      (fun i => n - gen i ∈ holes)
    have hblock : (block k).card = 2 * k + 1 := by
      rw [block, Nat.card_Ico]
      omega
    refine ⟨(block k).filter fun i => n - gen i ∉ holes, by omega, fun i hi => ?_⟩
    rw [Finset.mem_filter] at hi
    exact ⟨by have := hblk i hi.1; omega, hi.2⟩

/-- Every `n` reaching level `t` lies in the zone of some level `k ≥ t`. -/
private lemma exists_zone {t n : ℕ} (h : Reached t n) :
    ∃ k, t ≤ k ∧ Reached k n ∧ ¬ Reached (k + 1) n := by
  classical
  have hex : ∃ m, ¬ Reached m n := by
    refine ⟨n, fun hr => ?_⟩
    have h1 := le_of_reached hr
    have h2 : n * n + 2 * n ≤ top n := gen_strictMono.id_le (n * n + 2 * n)
    nlinarith
  have hmt : t < Nat.find hex := by
    by_contra hle
    exact Nat.find_spec hex (reached_anti (not_lt.mp hle) h)
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · exact not_not.mp (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
  · rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
    exact Nat.find_spec hex

/-- For every `t`, every sufficiently large `n` has at least `t` representations in
`basisSet`. -/
private lemma rich (t : ℕ) : ∀ᶠ n in atTop, ∃ pairs : Finset (ℕ × ℕ), pairs.card ≥ t ∧
    ∀ p ∈ pairs, p.1 ∈ basisSet ∧ p.2 ∈ basisSet ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2 := by
  classical
  rw [eventually_atTop]
  refine ⟨16 * t + 8 + (8 * ((top t + 1) * scale t) + 3), fun n hn => ?_⟩
  by_cases hodd : n % 2 = 1
  · have hr : Reached t n := by
      unfold Reached
      omega
    obtain ⟨k, htk, hlo, hhi⟩ := exists_zone hr
    obtain ⟨T, hTc, hT⟩ := zone hlo hhi
    refine ⟨T.image fun i => (gen i, n - gen i), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _
        (fun i j hij => gen_strictMono.injective (Prod.ext_iff.mp hij).1)]
      omega
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨h2i, hhole⟩ := hT i hi
      have := gen_mod i
      refine ⟨gen_mem i, Or.inr ⟨?_, hhole⟩, ?_, ?_⟩ <;> dsimp only <;> omega
  · -- Choose both even summands outside the residue class of the holes.
    let r := if n % 8 = 2 then 4 else 0
    have hr : (n % 8 = 2 ∧ r = 4) ∨ (n % 8 ≠ 2 ∧ r = 0) := by
      by_cases h : n % 8 = 2 <;> simp [r, h]
    refine ⟨(Finset.range t).image fun j => (8 * j + r, n - (8 * j + r)), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun i j hij => by
        have := (Prod.ext_iff.mp hij).1
        dsimp only at this
        omega)]
      simp
    · intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      rw [Finset.mem_range] at hj
      refine ⟨mem_basisSet_of_even ?_ ?_, mem_basisSet_of_even ?_ ?_, ?_, ?_⟩ <;>
        dsimp only <;> omega

/-! ### No splitting -/

/-- Every representation of `special k U` uses a generator `gen i` with `i ∈ U`. -/
private lemma odd_summand {k : ℕ} {U : Finset ℕ} (hU : Adm k U) {a b : ℕ} (ha : a ∈ basisSet)
    (hb : b ∈ basisSet) (hab : a + b = special k U) (hodd : a % 2 = 1) :
    ∃ i ∈ U, a = gen i := by
  have hsp := special_mod k U
  rcases ha with ⟨i, rfl⟩ | ⟨ha2, -⟩
  · refine ⟨i, ?_, rfl⟩
    by_contra hiU
    have hgi := gen_mod i
    rcases hb with ⟨j, rfl⟩ | ⟨-, hbh⟩
    · have := gen_mod j
      omega
    · apply hbh
      have hi : i < k * k + 2 * k + 1 := by
        have h1 := special_add_top_lt hU.1
        by_contra hge
        have := gen_strictMono.monotone (not_lt.mp hge)
        omega
      exact ⟨k, U, i, hU, hi, hiU, by omega⟩
  · omega

/-- If no generator of `U` lies in `D ⊆ basisSet`, then `special k U` is not in `D + D`. -/
private lemma no_rep {D : Set ℕ} (hD : D ⊆ basisSet) {k : ℕ} {U : Finset ℕ} (hU : Adm k U)
    (hUD : ∀ i ∈ U, gen i ∉ D) : ¬ ∃ a ∈ D, ∃ b ∈ D, a + b = special k U := by
  rintro ⟨a, ha, b, hb, hab⟩
  have hsp := special_mod k U
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · obtain ⟨i, hi, rfl⟩ := odd_summand hU (hD hb) (hD ha) (by omega) (by omega)
    exact hUD i hi hb
  · obtain ⟨i, hi, rfl⟩ := odd_summand hU (hD ha) (hD hb) hab h
    exact hUD i hi ha

private lemma not_split : ¬ ∃ (B C : Set ℕ), (∀ x, x ∈ basisSet ↔ x ∈ B ∨ x ∈ C) ∧
    Disjoint B C ∧ (∀ᶠ n in atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
    (∀ᶠ n in atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n) := by
  classical
  rintro ⟨B, C, hA, hBC, hB, hC⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hB.and hC)
  have hBA : B ⊆ basisSet := fun x hx => (hA x).mpr (Or.inl hx)
  have hCA : C ⊆ basisSet := fun x hx => (hA x).mpr (Or.inr hx)
  have hlarge : ∀ U, N ≤ special N U := fun U => by
    have h1 := special_ge N U
    have h2 : N ≤ scale N := le_trans (by nlinarith) (Nat.lt_two_pow_self).le
    have h3 : scale N ≤ (top N + 1) * scale N := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  have hcard : ((block N).filter fun i => gen i ∈ B).card +
      ((block N).filter fun i => gen i ∉ B).card = 2 * N + 1 := by
    rw [Finset.card_filter_add_card_filter_not, block, Nat.card_Ico]
    omega
  rcases le_or_gt (N + 1) ((block N).filter fun i => gen i ∈ B).card with h | h
  · refine no_rep hCA ⟨Finset.filter_subset _ _, h⟩ (fun i hi hiC => ?_) (hN _ (hlarge _)).2
    exact Set.disjoint_left.mp hBC (Finset.mem_filter.mp hi).2 hiC
  · refine no_rep (U := (block N).filter fun i => gen i ∉ B) hBA
      ⟨Finset.filter_subset _ _, by omega⟩ (fun i hi hiB => ?_) (hN _ (hlarge _)).1
    exact (Finset.mem_filter.mp hi).2 hiB

/-- **Erdős Problem 871 is false (Larsen).** There is a set $A$ of natural numbers such that every
sufficiently large $n$ is $a + b$ with $a, b \in A$ and, for every natural number $t$, every
sufficiently large $n$ has at least $t$ representations $n = a + b$ with $a, b \in A$ and
$a \le b$, but $A$ is not the disjoint union of two sets $B$ and $C$ such that every sufficiently
large $n$ is $a + b$ with $a, b \in B$ and every sufficiently large $n$ is $a + b$ with
$a, b \in C$.

Source:
Larsen (formalized in Lean), per erdosproblems.com/871, https://www.erdosproblems.com/871; Lean
disproof of Erdos Problem 871 (Larsen with Claude Opus 4.5), plby/lean-proofs at commit
dfe2d78128b493c572cf525b1b8edf4897fb7664,
https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos871.lean#L2388.
Moved from `OpenConjectures/NumberTheory/ErdosProblem871`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  have hbasis : ∀ᶠ n in atTop, ∃ a ∈ basisSet, ∃ b ∈ basisSet, a + b = n := by
    filter_upwards [rich 1] with n ⟨pairs, hcard, hp⟩
    obtain ⟨p, hpm⟩ := Finset.card_pos.mp (show 0 < pairs.card by omega)
    obtain ⟨h1, h2, h3, -⟩ := hp p hpm
    exact ⟨p.1, h1, p.2, h2, h3⟩
  obtain ⟨B, C, hBC⟩ := h basisSet ⟨hbasis, rich⟩
  exact not_split ⟨B, C, hBC⟩

end MathlibExt.NumberTheory.ErdosProblem871Wanted
