/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement of Erdős Problem 31 is adapted from
`FormalConjectures/ErdosProblems/31.lean` in Formal Conjectures.
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Data.Set.Density
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Lorentz's theorem on additive complements

We use the greedy covering and dyadic decomposition in Lorentz's 1954 proof.
For the density-zero conclusion, one threshold on the greedy gains suffices:
once no translate covers at least $q$ new points, double counting bounds the
uncovered set, and those points can be covered individually. This gives a
weaker finite bound than Lorentz's harmonic summation, but one whose ratio to
the block length still tends to zero.
-/

open Filter Finset
open scoped Pointwise

-- This namespace is retained so existing imports keep the same names.
namespace MathlibExt.NumberTheory.ErdosProblem31Wanted

/-- A finite family with at least `q * q` covers of each point admits a subcover
with `q * C.card ≤ R.card + V.card`. Count the shifts with gain at least `q`
against the points they remove, then count incidences in the residual set. -/
private theorem greedy_cover {α β : Type*} (P : β → α → Prop) [DecidableRel P]
    (V : Finset β) (q : ℕ) (hq : 0 < q) (R : Finset α)
    (hdeg : ∀ x ∈ R, q * q ≤ (V.filter (fun b ↦ P b x)).card) :
    ∃ C ⊆ V, (∀ x ∈ R, ∃ b ∈ C, P b x) ∧ q * C.card ≤ R.card + V.card := by
  classical
  induction hR : R.card using Nat.strong_induction_on generalizing R with
  | ind n ih =>
    let gain (b : β) := (R.filter (P b)).card
    by_cases hlarge : ∃ b ∈ V, q ≤ gain b
    · obtain ⟨b₀, hb₀, h₀⟩ := hlarge
      obtain ⟨b, hb, hmax⟩ := V.exists_max_image gain ⟨b₀, hb₀⟩
      have hgain : q ≤ gain b := h₀.trans (hmax b₀ hb₀)
      let R' := R \ R.filter (P b)
      have hsplit : R'.card + gain b = R.card := by
        simpa [R', gain, inter_eq_right.mpr (filter_subset _ _)] using
          card_sdiff_add_card_inter R (R.filter (P b))
      obtain ⟨C, hCV, hcov, hcard⟩ := ih R'.card (by omega) R'
        (fun x hx ↦ hdeg x (sdiff_subset hx)) rfl
      refine ⟨insert b C, insert_subset hb hCV, ?_, ?_⟩
      · intro x hx
        by_cases hbx : P b x
        · exact ⟨b, mem_insert_self _ _, hbx⟩
        · obtain ⟨b', hb', hp⟩ := hcov x (mem_sdiff.mpr ⟨hx, by simp [hbx]⟩)
          exact ⟨b', mem_insert_of_mem hb', hp⟩
      · calc
          q * (insert b C).card ≤ q * (C.card + 1) :=
            Nat.mul_le_mul_left _ (card_insert_le _ _)
          _ = q * C.card + q := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ n + V.card := by omega
    · have hsmall (b : β) (hb : b ∈ V) : gain b ≤ q := by
        apply Nat.le_of_lt
        exact lt_of_not_ge (fun h ↦ hlarge ⟨b, hb, h⟩)
      have hdouble : (∑ x ∈ R, (V.filter (fun b ↦ P b x)).card) =
          ∑ b ∈ V, gain b := by
        simp only [gain, card_filter]
        exact sum_comm
      have hcount : q * (q * R.card) ≤ q * V.card := calc
        q * (q * R.card) = ∑ _x ∈ R, q * q := by
          simp only [sum_const, nsmul_eq_mul]
          ac_rfl
        _ ≤ ∑ x ∈ R, (V.filter (fun b ↦ P b x)).card := sum_le_sum hdeg
        _ = ∑ b ∈ V, gain b := hdouble
        _ ≤ ∑ _b ∈ V, q := sum_le_sum hsmall
        _ = q * V.card := by simp [Nat.mul_comm]
      have hrest : q * R.card ≤ V.card := le_of_mul_le_mul_left hcount hq
      have hex (x : R) : ∃ b ∈ V, P b x := by
        have hp : 0 < (V.filter (fun b ↦ P b (x : α))).card :=
          (Nat.mul_pos hq hq).trans_le (hdeg x x.property)
        obtain ⟨b, hb⟩ := card_pos.mp hp
        exact ⟨b, (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩
      choose f hfV hfP using hex
      refine ⟨R.attach.image f, ?_, ?_, ?_⟩
      · intro b hb
        obtain ⟨x, -, rfl⟩ := mem_image.mp hb
        exact hfV x
      · intro x hx
        exact ⟨f ⟨x, hx⟩, mem_image_of_mem f (mem_attach _ _), hfP ⟨x, hx⟩⟩
      · have hC : (R.attach.image f).card ≤ R.card := by
          simpa using (card_image_le (s := R.attach) (f := f))
        exact (Nat.mul_le_mul_left _ hC).trans <|
          hrest.trans (Nat.le_add_left ..)

open scoped Classical in
/-- Cover `[2m, 4m)` by translates with shifts in `[m, 4m)`, using only the
points of `A` up through `m`. The gain threshold is the integer square root of
the number of available points of `A`. -/
private theorem interval_cover (A : Set ℕ) (m : ℕ) :
    ∃ C ⊆ Ico m (4 * m),
      (0 < ((Iic m).filter (· ∈ A)).card.sqrt →
        Set.Ico (2 * m) (4 * m) ⊆ A + (C : Set ℕ)) ∧
      ((Iic m).filter (· ∈ A)).card.sqrt * C.card ≤ 5 * m := by
  classical
  let F := (Iic m).filter (· ∈ A)
  let q := F.card.sqrt
  let V := Ico m (4 * m)
  let R := Ico (2 * m) (4 * m)
  let P (b x : ℕ) := ∃ a ∈ F, a + b = x
  change ∃ C ⊆ V, (0 < q → Set.Ico (2 * m) (4 * m) ⊆ A + ↑C) ∧
    q * C.card ≤ 5 * m
  by_cases hq : 0 < q
  · have hdeg (x : ℕ) (hx : x ∈ R) : q * q ≤ (V.filter (fun b ↦ P b x)).card := by
      apply (Nat.sqrt_le _).trans
      have hx' := mem_Ico.mp hx
      refine card_le_card_of_injOn (x - ·) ?_ ?_
      · intro a ha
        have ha' := mem_Iic.mp (mem_filter.mp (mem_coe.mp ha)).1
        change x - a ∈ V.filter (fun b ↦ P b x)
        exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, a, ha, by omega⟩
      · intro a ha a' ha' heq
        have ha₁ := mem_Iic.mp (mem_filter.mp (mem_coe.mp ha)).1
        have ha₂ := mem_Iic.mp (mem_filter.mp (mem_coe.mp ha')).1
        change x - a = x - a' at heq
        omega
    obtain ⟨C, hCV, hcov, hcard⟩ := greedy_cover P V q hq R hdeg
    refine ⟨C, hCV, ?_, ?_⟩
    · intro _ x hx
      obtain ⟨b, hb, a, ha, he⟩ := hcov x (mem_Ico.mpr hx)
      exact Set.mem_add.mpr ⟨a, (mem_filter.mp ha).2, b, hb, he⟩
    · have hlength : 4 * m - 2 * m + (4 * m - m) = 5 * m := by omega
      simpa [R, V, Nat.card_Ico, hlength] using hcard
  · exact ⟨∅, empty_subset _, fun h ↦ (hq h).elim, by simp⟩

open scoped Classical in
/-- Each fixed square eventually fits into the initial segment of `A` used
on every later dyadic block. -/
private theorem eventually_le_block_degree {A : Set ℕ} (hA : A.Infinite) (q : ℕ) :
    ∃ K : ℕ, ∀ i ≥ K, q ≤ ((Iic (2 ^ i)).filter (· ∈ A)).card.sqrt := by
  obtain ⟨F, hFA, hF⟩ := hA.exists_subset_card_eq (q * q)
  refine ⟨F.sup id, fun i hi ↦ Nat.le_sqrt.mpr ?_⟩
  rw [← hF]
  apply card_le_card
  intro a ha
  have hsup : a ≤ F.sup id := le_sup (f := id) ha
  exact mem_filter.mpr ⟨mem_Iic.mpr (hsup.trans (hi.trans Nat.lt_two_pow_self.le)),
    hFA ha⟩

/-- Only blocks with `2 ^ i < n` can meet `[0, n)`. For such blocks the sum of
`2 ^ i` is at most `2 * n`, so a uniform tail bound gives a prefix bound. -/
private theorem count_union_prefix (C : ℕ → Finset ℕ)
    (hstart : ∀ i, C i ⊆ Ico (2 ^ i) (4 * 2 ^ i))
    (q K : ℕ) (hcard : ∀ i ≥ K, q * (C i).card ≤ 5 * 2 ^ i)
    {n : ℕ} (hn : n ≠ 0) :
    q * ((⋃ i, (C i : Set ℕ)) ∩ Set.Iio n).ncard ≤
      q * ((range K).biUnion C).card + 10 * n := by
  classical
  let e := Nat.log 2 n
  let U := (range K).biUnion C
  let T := (Ico K (e + 1)).biUnion C
  have hsub : (⋃ i, (C i : Set ℕ)) ∩ Set.Iio n ⊆ ↑(U ∪ T) := by
    rintro x ⟨hx, hxn⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    apply mem_union.mpr
    by_cases hiK : i < K
    · exact Or.inl (mem_biUnion.mpr ⟨i, mem_range.mpr hiK, hi⟩)
    · have hie : i ≤ e := Nat.le_log_of_pow_le (by decide)
        ((mem_Ico.mp (hstart i hi)).1.trans (Set.mem_Iio.mp hxn).le)
      exact Or.inr (mem_biUnion.mpr ⟨i, mem_Ico.mpr ⟨by omega, by omega⟩, hi⟩)
  have hgeom : (∑ i ∈ range (e + 1), (2 : ℕ) ^ i) + 1 = 2 ^ (e + 1) := by
    simpa using (geom_sum_mul_add (1 : ℕ) (e + 1))
  have hpow : 2 ^ (e + 1) ≤ 2 * n := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hn)
  have htail : q * T.card ≤ 10 * n := calc
    q * T.card ≤ q * ∑ i ∈ Ico K (e + 1), (C i).card :=
      Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ i ∈ Ico K (e + 1), q * (C i).card := by rw [mul_sum]
    _ ≤ ∑ i ∈ Ico K (e + 1), 5 * 2 ^ i :=
      sum_le_sum fun i hi ↦ hcard i (mem_Ico.mp hi).1
    _ = 5 * ∑ i ∈ Ico K (e + 1), 2 ^ i := by rw [mul_sum]
    _ ≤ 5 * ∑ i ∈ range (e + 1), 2 ^ i := by
      apply Nat.mul_le_mul_left
      exact sum_le_sum_of_subset_of_nonneg (fun i hi ↦ mem_range.mpr (mem_Ico.mp hi).2)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ 10 * n := by
      have hsum : (∑ i ∈ range (e + 1), (2 : ℕ) ^ i) ≤ 2 * n := by omega
      calc
        _ ≤ 5 * (2 * n) := Nat.mul_le_mul_left _ hsum
        _ = 10 * n := by rw [← Nat.mul_assoc]
  have hunion : ((⋃ i, (C i : Set ℕ)) ∩ Set.Iio n).ncard ≤
      (U ∪ T).card := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub
  calc
    _ ≤ q * (U ∪ T).card := Nat.mul_le_mul_left _ hunion
    _ ≤ q * (U.card + T.card) := Nat.mul_le_mul_left _ (card_union_le U T)
    _ = q * U.card + q * T.card := Nat.mul_add ..
    _ ≤ q * U.card + 10 * n := Nat.add_le_add_left htail _

/-! Source record `FC-ErdosProblem31`, ported from FormalConjectures
`ErdosProblems/31.lean` (`theorem erdos_31`) and checked against
[the public problem statement](https://www.erdosproblems.com/31). -/

@[expose] public def conjecture : Prop :=
  ∀ A : Set ℕ, A.Infinite →
    ∃ B : Set ℕ, B.HasDensity 0 ∧ ∀ᶠ n in atTop, n ∈ A + B

/-- **Lorentz's theorem on additive complements (Erdős Problem 31).** For every
infinite set $A$ of natural numbers there is a set $B$ of natural numbers of
natural density $0$ such that every sufficiently large natural number lies in
$A + B = \{a + b \mid a \in A,\ b \in B\}$.

Source: George G. Lorentz, *On a problem of additive number theory*,
Proceedings of the American Mathematical Society 5 (1954), 838–841,
https://doi.org/10.1090/s0002-9939-1954-0063389-3.
-/
public theorem conjecture_holds : conjecture := by
  classical
  intro A hA
  choose C hstart hcover hbound using fun i : ℕ ↦ interval_cover A (2 ^ i)
  let B : Set ℕ := ⋃ i, (C i : Set ℕ)
  refine ⟨B, ?_, ?_⟩
  · rw [Set.HasDensity, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨q, hq⟩ := exists_nat_gt (20 / ε)
    have hqpos : (0 : ℝ) < q := (by positivity : 0 < 20 / ε).trans hq
    have hqε : (20 : ℝ) < (q : ℝ) * ε := (div_lt_iff₀ hε).mp hq
    obtain ⟨K, hK⟩ := eventually_le_block_degree hA q
    let M := ((range K).biUnion C).card
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (M : ℝ) / ε)
    refine ⟨max 1 N, fun n hn ↦ ?_⟩
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left ..).trans hn)
    have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right 1 N).trans hn
    have hM : 2 * (M : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    have hcount := count_union_prefix C hstart q K
      (fun i hi ↦ (Nat.mul_le_mul_right _ (hK i hi)).trans (hbound i)) hnpos.ne'
    have hcount' : (q : ℝ) * ((B ∩ Set.Iio n).ncard : ℝ) ≤
        (q : ℝ) * M + 10 * n := by exact_mod_cast hcount
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat,
      Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (by positivity), div_lt_iff₀ hnpos']
    apply (mul_lt_mul_iff_right₀ hqpos).mp
    nlinarith only [hcount', mul_lt_mul_of_pos_left hM hqpos,
      mul_lt_mul_of_pos_right hqε hnpos']
  · obtain ⟨K, hK⟩ := eventually_le_block_degree hA 1
    refine eventually_atTop.mpr ⟨2 * 2 ^ K, fun n hn ↦ ?_⟩
    have hlog : K + 1 ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by decide) (by rwa [pow_succ'])
    let i := Nat.log 2 n - 1
    have hi : i + 1 = Nat.log 2 n := by dsimp [i]; omega
    have hKi : K ≤ i := by omega
    have hnpos : 0 < n := (by positivity : 0 < 2 * 2 ^ K).trans_le hn
    have hlo : 2 * 2 ^ i ≤ n := by
      rw [← pow_succ', hi]
      exact Nat.pow_log_le_self 2 hnpos.ne'
    have hhi : n < 4 * 2 ^ i := by
      have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
      rw [← hi, Nat.succ_eq_add_one, pow_succ', pow_succ'] at hp
      omega
    obtain ⟨a, ha, b, hb, he⟩ := Set.mem_add.mp
      (hcover i (hK i hKi) (Set.mem_Ico.mpr ⟨hlo, hhi⟩))
    exact Set.mem_add.mpr ⟨a, ha, b, Set.mem_iUnion.mpr ⟨i, hb⟩, he⟩

end MathlibExt.NumberTheory.ErdosProblem31Wanted
