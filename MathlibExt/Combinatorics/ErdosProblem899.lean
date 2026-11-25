/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/899.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definition of the conjecture and the statement that it holds.
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Difference sets of sparse sets

Ruzsa's theorem states that the ratio of positive differences to elements of an infinite
set of density zero has infinite limit superior. The proof uses the Plünnecke–Ruzsa inequality
on finite truncations to bound the number of disjoint translates in a packing.
-/

@[expose] public section

open Filter
open scoped Pointwise Topology

namespace MathlibExt.Combinatorics.ErdosProblem899Wanted

/-- **Erdős Problem 899 on difference sets of sparse sets.** The proposition asserts the following
for every infinite set $A$ of natural numbers. Write $A(N) = |A \cap \{1, \dots, N\}|$ for its
counting function and $D(N)$ for the number of integers $d \in \{1, \dots, N\}$ of the form
$d = a - b$ with $a, b \in A$. If $A(N)/N \to 0$ as $N \to \infty$, then
$\limsup_{N \to \infty} D(N)/A(N) = +\infty$.

The ratio $D(N)/A(N)$ is computed in the extended reals and taken to be $0$ when $A(N) = 0$. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 0) →
    Filter.atTop.limsup (fun N => (((A - A : Set ℕ) ∩ Set.Icc 1 N).ncard : EReal) /
      ((A ∩ Set.Icc 1 N).ncard : EReal)) = ⊤

private noncomputable def window (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Set.finite_Icc 1 n).inter_of_right A |>.toFinset

private lemma mem_window {A : Set ℕ} {n a : ℕ} :
    a ∈ window A n ↔ a ∈ A ∧ 1 ≤ a ∧ a ≤ n := by
  simp [window, Set.mem_Icc]

private lemma card_window (A : Set ℕ) (n : ℕ) :
    (window A n).card = (A ∩ Set.Icc 1 n).ncard :=
  (Set.ncard_eq_toFinset_card _ _).symm

private noncomputable def intWindow (A : Set ℕ) (n : ℕ) : Finset ℤ :=
  (window A n).image Int.ofNat

private lemma card_intWindow (A : Set ℕ) (n : ℕ) : (intWindow A n).card = (window A n).card :=
  Finset.card_image_of_injective _ Int.ofNat_injective

private lemma intWindow_mono (A : Set ℕ) : Monotone (intWindow A) := by
  intro m n h
  apply Finset.image_subset_image
  intro a ha
  obtain ⟨ha, h₁, h₂⟩ := mem_window.mp ha
  exact mem_window.mpr ⟨ha, h₁, h₂.trans h⟩

private lemma pos_sub_mem {A : Set ℕ} {n : ℕ} {z : ℤ}
    (hz : z ∈ intWindow A n - intWindow A n) (hpos : 0 < z) :
    z ∈ intWindow (A - A) n := by
  obtain ⟨_, ha, _, hb, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨a, hwa, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, hwb, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ha, -, hna⟩ := mem_window.mp hwa
  obtain ⟨hb, -, -⟩ := mem_window.mp hwb
  change 0 < (a : ℤ) - b at hpos
  exact Finset.mem_image.mpr ⟨a - b, mem_window.mpr
    ⟨Set.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩, by omega, by omega⟩,
    show ((a - b : ℕ) : ℤ) = a - b by omega⟩

private lemma neg_mem_sub_self {B : Finset ℤ} {z : ℤ} (hz : z ∈ B - B) : -z ∈ B - B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  exact Finset.mem_sub.mpr ⟨b, hb, a, ha, by omega⟩

private lemma card_signed_sub_le (A : Set ℕ) (n : ℕ) :
    (intWindow A n - intWindow A n).card ≤ 2 * (window (A - A) n).card + 1 := by
  let B := intWindow (A - A) n
  have h : intWindow A n - intWindow A n ⊆ insert 0 (B ∪ -B) := by
    intro z hz
    rcases lt_trichotomy z 0 with hneg | rfl | hpos
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ <|
        Finset.mem_neg.mpr ⟨-z, pos_sub_mem (neg_mem_sub_self hz) (by omega), neg_neg _⟩)
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (pos_sub_mem hz hpos))
  have h₁ := Finset.card_le_card h
  have h₂ := Finset.card_insert_le 0 (B ∪ -B)
  have h₃ := Finset.card_union_le B (-B)
  rw [Finset.card_neg] at h₃
  have hcard : B.card = (window (A - A) n).card := card_intWindow ..
  omega

/-- A packing with centers in twice the difference set is bounded by the five-fold
Plünnecke–Ruzsa estimate. -/
private lemma packing_bound {B T : Finset ℤ} {K : ℕ} (hB : B.Nonempty)
    (hK : (B - B).card ≤ K * B.card) (hT : T ⊆ (B - B) + (B - B))
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ B - B → x = y) : T.card ≤ K ^ 5 := by
  have hcard : (T + B).card = T.card * B.card := by
    apply Finset.card_add_iff.mpr
    rintro ⟨x, b⟩ ⟨hx, hb⟩ ⟨y, c⟩ ⟨hy, hc⟩ he
    change x + b = y + c at he
    have hxy := hsep x hx y hy (Finset.mem_sub.mpr ⟨c, hc, b, hb, by omega⟩)
    exact Prod.ext hxy (by dsimp; omega)
  have hsub : T + B ⊆ 3 • B - 2 • B := by
    intro z hz
    obtain ⟨t, ht, b, hb, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (hT ht)
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_sub.mp hu
    obtain ⟨d, hd, e, he, rfl⟩ := Finset.mem_sub.mp hv
    rw [show 3 = 2 + 1 by decide, succ_nsmul, two_nsmul]
    exact Finset.mem_sub.mpr ⟨_, Finset.add_mem_add (Finset.add_mem_add ha hd) hb, _,
      Finset.add_mem_add hc he, by omega⟩
  have hr : ((B - B).card / (B.card : ℚ≥0)) ≤ K := by
    apply (div_le_iff₀ (by exact_mod_cast hB.card_pos)).mpr
    exact_mod_cast hK
  have hle : ((T + B).card : ℚ≥0) ≤ (K : ℚ≥0) ^ 5 * B.card := calc
    _ ≤ ((3 • B - 2 • B).card : ℚ≥0) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := (Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hB B 3 2).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr 5) (by positivity))
  rw [hcard, Nat.cast_mul] at hle
  exact_mod_cast (le_of_mul_le_mul_right hle (by exact_mod_cast hB.card_pos))

/-- Signed differences between positive elements of `A`, exhausted by finite windows. -/
private def signedDiff (A : Set ℕ) : Set ℤ :=
  {z | ∃ n, z ∈ intWindow A n - intWindow A n}

private lemma subWindow_mono (A : Set ℕ) :
    Monotone (fun n ↦ intWindow A n - intWindow A n) := by
  intro m n h
  exact Finset.sub_subset_sub (intWindow_mono A h) (intWindow_mono A h)

/-- Pass from the uniform bound on finite packings to a finite cover of the infinite sumset. -/
private lemma cover_signedDiff (A : Set ℕ) (K : ℕ)
    (hK : ∀ᶠ n in atTop, (intWindow A n).Nonempty ∧
      (intWindow A n - intWindow A n).card ≤ K * (intWindow A n).card) :
    ∃ T : Finset ℤ, ∀ z ∈ signedDiff A + signedDiff A, ∃ t ∈ T, z - t ∈ signedDiff A := by
  classical
  let D := signedDiff A
  let B := intWindow A
  let Q := fun n ↦ (B n - B n) + (B n - B n)
  have hQ : Monotone Q := fun _ _ h ↦
    Finset.add_subset_add (subWindow_mono A h) (subWindow_mono A h)
  -- Two centers can occur together precisely when their translated copies are disjoint.
  let pack : Set (Finset ℤ) := {T | (∃ n, T ⊆ Q n) ∧ ∀ x ∈ T, ∀ y ∈ T, x - y ∈ D → x = y}
  have hfin : (Finset.card '' pack).Finite := by
    apply (Set.finite_Iic (K ^ 5)).subset
    rintro _ ⟨T, ⟨⟨m, hm⟩, hs⟩, rfl⟩
    obtain ⟨n, hnm, hn, hsmall⟩ := ((eventually_ge_atTop m).and hK).exists
    exact packing_bound hn hsmall (hm.trans (hQ hnm))
      (fun x hx y hy h ↦ hs x hx y hy ⟨n, h⟩)
  obtain ⟨T, hT, hmax⟩ := hfin.exists_maximalFor' Finset.card pack
    ⟨∅, ⟨0, Finset.empty_subset _⟩, by simp⟩
  refine ⟨T, fun z hz ↦ ?_⟩
  obtain ⟨u, ⟨i, hi⟩, v, ⟨j, hj⟩, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨⟨m, hm⟩, hs⟩ := hT
  have hzero : (0 : ℤ) ∈ D := by
    obtain ⟨n, hn, -⟩ := hK.exists
    obtain ⟨a, ha⟩ := hn
    exact ⟨n, Finset.mem_sub.mpr ⟨a, ha, a, ha, sub_self _⟩⟩
  -- An uncovered sum would extend this packing by one more center.
  by_contra! h
  have hnew : u + v ∉ T := fun hz ↦ h _ hz (by simpa using hzero)
  have hins : insert (u + v) T ∈ pack := by
    refine ⟨⟨max m (max i j), Finset.insert_subset ?_ (hm.trans (hQ (le_max_left ..)))⟩, ?_⟩
    · apply hQ (le_max_right m (max i j))
      exact Finset.add_mem_add (subWindow_mono A (le_max_left i j) hi)
        (subWindow_mono A (le_max_right i j) hj)
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
    · rfl
    · exact (h _ hy hxy).elim
    · obtain ⟨n, hn⟩ := hxy
      exact (h _ hx ⟨n, by simpa only [neg_sub] using neg_mem_sub_self hn⟩).elim
    · exact hs _ hx _ hy hxy
  have := hmax hins (Finset.card_le_card (Finset.subset_insert _ _))
  simp [Finset.card_insert_of_notMem hnew] at this

private lemma mem_intWindow {A : Set ℕ} {a n : ℕ} (ha : a ∈ A) (hpos : 0 < a)
    (hle : a ≤ n) : (a : ℤ) ∈ intWindow A n :=
  Finset.mem_image.mpr ⟨a, mem_window.mpr ⟨ha, hpos, hle⟩, rfl⟩

/-- In a finite cover of the sumset, taking a step larger than every translation gives
a new positive difference within a bounded distance of the preceding one. -/
private lemma bounded_steps {A : Set ℕ} (hA : A.Infinite) {T : Finset ℤ}
    (hT : ∀ z ∈ signedDiff A + signedDiff A, ∃ t ∈ T, z - t ∈ signedDiff A) :
    ∃ H : ℕ, 0 < H ∧ ∀ x : ℕ, (x : ℤ) ∈ signedDiff A →
      ∃ y : ℕ, (y : ℤ) ∈ signedDiff A ∧ x < y ∧ y ≤ x + H := by
  let M := T.sup Int.natAbs
  obtain ⟨a, ha, hapos⟩ := hA.exists_gt 0
  obtain ⟨b, hb, hbig⟩ := hA.exists_gt (M + a)
  have hd : (b : ℤ) - a ∈ signedDiff A :=
    ⟨b, Finset.sub_mem_sub (mem_intWindow hb (by omega) le_rfl)
      (mem_intWindow ha hapos (by omega))⟩
  refine ⟨b + M, by omega, fun x hx ↦ ?_⟩
  obtain ⟨t, ht, hz⟩ := hT _ (Set.add_mem_add hx hd)
  have htM : t.natAbs ≤ M := Finset.le_sup ht
  have h₁ : t ≤ (t.natAbs : ℤ) := Int.le_natAbs
  have h₂ : -t ≤ ((-t).natAbs : ℤ) := Int.le_natAbs
  rw [Int.natAbs_neg] at h₂
  let y := (x : ℤ) + (b - a) - t
  have hy : 0 ≤ y := by
    dsimp [y]
    omega
  refine ⟨y.toNat, ?_, ?_, ?_⟩
  · rwa [Int.toNat_of_nonneg hy]
  · dsimp [y]
    omega
  · dsimp [y]
    omega

private lemma count_steps {A : Set ℕ} (hzero : (0 : ℤ) ∈ signedDiff A) {H : ℕ}
    (hstep : ∀ x : ℕ, (x : ℤ) ∈ signedDiff A →
      ∃ y : ℕ, (y : ℤ) ∈ signedDiff A ∧ x < y ∧ y ≤ x + H) (n : ℕ) :
    n ≤ (window (A - A) (n * H)).card := by
  have hmono : Monotone (window (A - A)) := by
    intro i j hij a ha
    obtain ⟨ha, hpos, hi⟩ := mem_window.mp ha
    exact mem_window.mpr ⟨ha, hpos, hi.trans hij⟩
  suffices ∃ x : ℕ, (x : ℤ) ∈ signedDiff A ∧ x ≤ n * H ∧ n ≤ (window (A - A) x).card by
    obtain ⟨x, -, hx, hcard⟩ := this
    exact hcard.trans (Finset.card_le_card (hmono hx))
  induction n with
  | zero => exact ⟨0, hzero, by simp, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨x, hx, hxle, hcard⟩ := ih
    obtain ⟨y, hy, hxy, hyle⟩ := hstep x hx
    obtain ⟨m, hm⟩ := hy
    have hpos : 0 < (y : ℤ) := by omega
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (pos_sub_mem hm hpos)
    have hvy : v = y := Int.ofNat_injective he
    subst v
    have hmem : y ∈ window (A - A) y :=
      mem_window.mpr ⟨(mem_window.mp hv).1, by omega, le_rfl⟩
    have hlt : window (A - A) x ⊂ window (A - A) y :=
      (Finset.ssubset_iff_of_subset (hmono hxy.le)).mpr
        ⟨y, hmem, fun hyx ↦ hxy.not_ge (mem_window.mp hyx).2.2⟩
    refine ⟨y, ⟨m, hm⟩, ?_, hcard.trans_lt (Finset.card_lt_card hlt)⟩
    rw [Nat.succ_mul]
    omega

/--
**Ruzsa's theorem on difference sets of sparse sets.** Let $A$ be an infinite set of natural
numbers whose counting function $A(N) = |A \cap \{1, \dots, N\}|$ satisfies $A(N)/N \to 0$ as
$N \to \infty$, and let $D(N)$ be the number of integers $d \in \{1, \dots, N\}$ of the form
$d = a - b$ with $a, b \in A$. Then $\limsup_{N \to \infty} D(N)/A(N) = +\infty$, where the ratio
is computed in the extended reals and taken to be $0$ when $A(N) = 0$.

This answers Erdős Problem 899 affirmatively.

Source: I. Z. Ruzsa, On the cardinality of A+A and A-A (1978), 933–938,
https://mathscinet.ams.org/mathscinet-getitem?mr=519317. Moved from
`OpenConjectures/Combinatorics/ErdosProblem899`.
-/
theorem conjecture_holds : conjecture := by
  intro A hA hdensity
  simp_rw [← card_window] at hdensity ⊢
  by_contra hfin
  obtain ⟨r, hr, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hfin)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  obtain ⟨a, ha, hapos⟩ := hA.exists_gt 0
  have hne : ∀ᶠ n in atTop, (intWindow A n).Nonempty :=
    (eventually_ge_atTop a).mono fun n hn ↦ ⟨a, mem_intWindow ha hapos hn⟩
  have hbound : ∀ᶠ n in atTop, (window (A - A) n).card ≤ k * (window A n).card := by
    filter_upwards [eventually_lt_of_limsup_lt hr, hne] with n hn hn'
    have hreal := EReal.coe_lt_coe_iff.mp hn
    change (window (A - A) n).card / ((window A n).card : ℝ) < r at hreal
    have hpos := hn'.card_pos
    rw [card_intWindow] at hpos
    exact_mod_cast (div_lt_iff₀ (by exact_mod_cast hpos)).mp (hreal.trans hk) |>.le
  have hsmall : ∀ᶠ n in atTop, (intWindow A n).Nonempty ∧
      (intWindow A n - intWindow A n).card ≤ (2 * k + 1) * (intWindow A n).card := by
    filter_upwards [hne, hbound] with n hn h
    refine ⟨hn, ?_⟩
    have hp := hn.card_pos
    rw [card_intWindow] at hp ⊢
    have := card_signed_sub_le A n
    rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    omega
  obtain ⟨T, hT⟩ := cover_signedDiff A (2 * k + 1) hsmall
  obtain ⟨H, hH, hstep⟩ := bounded_steps hA hT
  have hzero : (0 : ℤ) ∈ signedDiff A :=
    ⟨a, Finset.mem_sub.mpr ⟨_, mem_intWindow ha hapos le_rfl, _,
      mem_intWindow ha hapos le_rfl, sub_self _⟩⟩
  have hthin : ∀ᶠ n in atTop, (window (A - A) n).card * H < n := by
    have heps : 0 < 1 / ((k : ℝ) * H + 1) := by positivity
    filter_upwards [(tendsto_order.mp hdensity).2 _ heps, hbound, eventually_gt_atTop 0]
      with n hn hb hnpos
    have hcmp := (div_lt_div_iff₀ (by exact_mod_cast hnpos) (by positivity)).mp hn
    have hlt : (k * (window A n).card) * H < n := by
      exact_mod_cast (show (k : ℝ) * (window A n).card * H < n by
        nlinarith [Nat.cast_nonneg (α := ℝ) (window A n).card])
    exact (Nat.mul_le_mul_right H hb).trans_lt hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hthin
  exact (hN (N * H) (Nat.le_mul_of_pos_right N hH)).not_ge
    (Nat.mul_le_mul_right H (count_steps hzero hstep N))

end MathlibExt.Combinatorics.ErdosProblem899Wanted
