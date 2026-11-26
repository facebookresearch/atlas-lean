/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Counting the sets of line-incidence numbers (Erdős Problem 607)

Erdős Problem 607: for `n` points `P ⊆ ℝ²` let `A = {|ℓ ∩ P|}` over the lines `ℓ` determined by `P`,
and let `F(n)` count the possible sets `A`. Is `F(n) ≤ exp(O(√n))`?

The main result is `lineIncidenceSetCountSubexponential_holds`: there is a real constant `C`
such that `F(n) ≤ exp (C * √n)` for every natural number `n`, proved by counting, for each
realizable set `A`, the incidences between a chosen line for each element of `A` and the points
of `P`, and then counting the subsets of `{0, …, n}` whose elements sum to at most `7 * n`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #607, https://www.erdosproblems.com/607 (status
PROVED). UnsolvedMath record UM-30006949 (`EP-607`), dataset ulamai/UnsolvedMath v1.8.0.

The lines determined by `P` are the lines `line[ℝ, p, q]` through two distinct points of `P`. Every
`A(P)` is a subset of `{0, …, n}`, so `F(n)` is counted inside that powerset. `exp(O(√n))` is `∃ C,
∀ n, F(n) ≤ exp(C √n)`, equivalent because `F(n)` is finite for each `n` and `F(0) = 1`.
-/

open Classical in
/-- **Line-incidence set of a finite planar point set.** For a finite set
$P \subseteq \mathbb{R}^2$, $A(P)$ is the set of the numbers $|\ell \cap P|$ over the lines $\ell$
determined by $P$, that is, the lines through at least two distinct points of $P$. -/
noncomputable def lineIncidenceSet (P : Finset (ℝ × ℝ)) : Finset ℕ :=
  P.offDiag.image fun pq => (P.filter fun r => r ∈ line[ℝ, pq.1, pq.2]).card

open Classical in
/-- **Number of line-incidence sets.** For a finite set $P \subseteq \mathbb{R}^2$, let $A(P)$ be
the set of the numbers $|\ell \cap P|$ over the lines $\ell$ through at least two distinct points
of $P$. For a natural number $n$, $F(n)$ is the number of distinct sets $A(P)$ over all $n$-point
sets $P \subseteq \mathbb{R}^2$. Every such $A(P)$ is a subset of $\{0, \dots, n\}$. -/
noncomputable def lineIncidenceSetCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).powerset.filter fun A =>
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineIncidenceSet P = A).card

/-- **Erdős Problem 607: subexponentially many line-incidence sets.** For a finite set
$P \subseteq \mathbb{R}^2$, let $A(P)$ be the set of the numbers $|\ell \cap P|$ over the lines
$\ell$ through at least two distinct points of $P$, and let $F(n)$ be the number of distinct sets
$A(P)$ over all $n$-point sets $P \subseteq \mathbb{R}^2$. This is the statement that there is a
real constant $C$ such that $F(n) \le e^{C\sqrt{n}}$ for every natural number $n$, that is,
$F(n) \le \exp(O(\sqrt{n}))$. -/
def lineIncidenceSetCountSubexponential : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, (lineIncidenceSetCount n : ℝ) ≤ Real.exp (C * Real.sqrt n)


open Classical in
private lemma exists_pair_of_mem {P : Finset (ℝ × ℝ)} {k : ℕ}
    (hk : k ∈ lineIncidenceSet P) :
    ∃ pq ∈ P.offDiag, (P.filter fun r => r ∈ line[ℝ, pq.1, pq.2]).card = k := by
  unfold lineIncidenceSet at hk
  rw [Finset.mem_image] at hk
  obtain ⟨pq, hpq, h⟩ := hk
  exact ⟨pq, hpq, h⟩

open Classical in
private lemma line_eq_of_two_mem {a b p q p' q' : ℝ × ℝ}
    (ha : a ∈ line[ℝ, p, q]) (hb : b ∈ line[ℝ, p, q]) (hab : a ≠ b)
    (ha' : a ∈ line[ℝ, p', q']) (hb' : b ∈ line[ℝ, p', q']) :
    line[ℝ, p, q] = line[ℝ, p', q'] := by
  rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne ha hb hab,
    affineSpan_pair_eq_of_mem_of_mem_of_ne ha' hb' hab]

open Classical in
private lemma sum_le_aux (P : Finset (ℝ × ℝ)) :
    (∑ k ∈ lineIncidenceSet P, (k : ℝ)) ≤
      P.card + (lineIncidenceSet P).card * Real.sqrt P.card := by
  set A := lineIncidenceSet P with hA
  have hrep : ∀ k : ℕ, ∃ S : Finset (ℝ × ℝ), ∃ pq : (ℝ × ℝ) × (ℝ × ℝ), k ∈ A →
      S.card = k ∧ pq ∈ P.offDiag ∧ S = P.filter fun r => r ∈ line[ℝ, pq.1, pq.2] := by
    intro k
    by_cases hk : k ∈ A
    · obtain ⟨pq, hpq, hcard⟩ := exists_pair_of_mem (P := P) hk
      exact ⟨P.filter fun r => r ∈ line[ℝ, pq.1, pq.2], pq,
        fun _ => ⟨hcard, hpq, rfl⟩⟩
    · exact ⟨∅, (((0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ))), fun h => absurd h hk⟩
  choose L pq hL using hrep
  -- d p = number of representative lines through p
  set d : (ℝ × ℝ) → ℕ := fun p => (A.filter fun k => p ∈ L k).card with hd
  have hcardL : ∀ k ∈ A, (L k).card = k := fun k hk => (hL k hk).1
  have hpq : ∀ k ∈ A, pq k ∈ P.offDiag := fun k hk => (hL k hk).2.1
  have hLeq : ∀ k ∈ A, L k =
      P.filter fun r => r ∈ line[ℝ, (pq k).1, (pq k).2] := fun k hk => (hL k hk).2.2
  have hsubL : ∀ k ∈ A, L k ⊆ P := by
    intro k hk
    rw [hLeq k hk]
    exact Finset.filter_subset _ _
  -- sum over p of d p equals sum over k of k
  have hsum : ∑ p ∈ P, d p = ∑ k ∈ A, k := by
    have h1 : ∀ p ∈ P, d p = ∑ k ∈ A, if p ∈ L k then (1 : ℕ) else 0 := by
      intro p hp
      exact Finset.card_filter _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.card_filter]
    have h3 : P.filter (fun p => p ∈ L k) = L k := by
      ext r
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨hsubL k hk h, h⟩
    rw [h3, hcardL k hk]
  -- pair counting: ordered pairs of distinct representative lines through a point
  have hpair : ∑ p ∈ P, d p * (d p - 1) ≤ A.card * (A.card - 1) := by
    set T : Finset ((ℝ × ℝ) × (ℕ × ℕ)) :=
      (P ×ˢ (A ×ˢ A)).filter fun x =>
        x.2.1 ≠ x.2.2 ∧ x.1 ∈ L x.2.1 ∧ x.1 ∈ L x.2.2 with hT
    have hTle : T.card ≤ A.offDiag.card := by
      apply Finset.card_le_card_of_injOn (fun x => (x.2.1, x.2.2))
      · intro x hx
        simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
          Finset.mem_offDiag] at hx ⊢
        exact ⟨hx.1.2.1, hx.1.2.2, hx.2.1⟩
      · intro x hx y hy hxy
        simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
        obtain ⟨⟨hxP, hxA1, hxA2⟩, hxne, hx1, hx2⟩ := hx
        obtain ⟨⟨hyP, hyA1, hyA2⟩, hyne, hy1, hy2⟩ := hy
        have hk1 : x.2.1 = y.2.1 := congrArg Prod.fst hxy
        have hk2 : x.2.2 = y.2.2 := congrArg Prod.snd hxy
        have hpoints : x.1 = y.1 := by
          by_contra hne12
          have hxline1 : x.1 ∈ line[ℝ, (pq x.2.1).1, (pq x.2.1).2] := by
            have hmem : x.1 ∈ L x.2.1 := hx1
            rw [hLeq x.2.1 hxA1] at hmem
            exact (Finset.mem_filter.mp hmem).2
          have hxline2 : x.1 ∈ line[ℝ, (pq x.2.2).1, (pq x.2.2).2] := by
            have hmem : x.1 ∈ L x.2.2 := hx2
            rw [hLeq x.2.2 hxA2] at hmem
            exact (Finset.mem_filter.mp hmem).2
          have hyline1 : y.1 ∈ line[ℝ, (pq x.2.1).1, (pq x.2.1).2] := by
            have hmem : y.1 ∈ L y.2.1 := hy1
            rw [← hk1] at hmem
            rw [hLeq x.2.1 hxA1] at hmem
            exact (Finset.mem_filter.mp hmem).2
          have hyline2 : y.1 ∈ line[ℝ, (pq x.2.2).1, (pq x.2.2).2] := by
            have hmem : y.1 ∈ L y.2.2 := hy2
            rw [← hk2] at hmem
            rw [hLeq x.2.2 hxA2] at hmem
            exact (Finset.mem_filter.mp hmem).2
          have hlineeq := line_eq_of_two_mem hxline1 hyline1 hne12 hxline2 hyline2
          have hLeqeq : L x.2.1 = L x.2.2 := by
            rw [hLeq x.2.1 hxA1, hLeq x.2.2 hxA2, hlineeq]
          have hcardeq : x.2.1 = x.2.2 := by
            have h1 := hcardL x.2.1 hxA1
            have h2 := hcardL x.2.2 hxA2
            rw [hLeqeq] at h1
            omega
          exact hxne hcardeq
        exact Prod.ext hpoints (Prod.ext hk1 hk2)
    have hTcard : T.card = ∑ p ∈ P, d p * (d p - 1) := by
      have hstep : T.card = ∑ p ∈ P, ((A ×ˢ A).filter fun kk =>
          kk.1 ≠ kk.2 ∧ p ∈ L kk.1 ∧ p ∈ L kk.2).card := by
        rw [hT, Finset.card_filter, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro p hp
        exact (Finset.card_filter _ _).symm
      rw [hstep]
      apply Finset.sum_congr rfl
      intro p hp
      have heq : ((A ×ˢ A).filter fun kk =>
          kk.1 ≠ kk.2 ∧ p ∈ L kk.1 ∧ p ∈ L kk.2) =
          (A.filter fun k => p ∈ L k).offDiag := by
        ext kk
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
        constructor
        · rintro ⟨⟨h1, h2⟩, hne, h3, h4⟩
          exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩, hne⟩
        · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩, hne⟩
          exact ⟨⟨h1, h2⟩, hne, h3, h4⟩
      rw [heq, Finset.offDiag_card]
      have hdcard : d p = (A.filter fun k => p ∈ L k).card := rfl
      rw [hdcard]
      cases (A.filter fun k => p ∈ L k).card with
      | zero => simp
      | succ a => simp [Nat.mul_succ, Nat.succ_mul]
    rw [Finset.offDiag_card] at hTle
    rw [hTcard] at hTle
    have hcard : A.card * A.card - A.card = A.card * (A.card - 1) := by
      cases A.card with
      | zero => simp
      | succ a => simp [Nat.mul_succ, Nat.succ_mul]
    rw [hcard] at hTle
    exact hTle
  -- real-valued form of the two counting identities
  have hsumR : ∑ p ∈ P, (d p : ℝ) = ∑ k ∈ A, (k : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    exact_mod_cast hsum
  have hterm : ∀ p : ℝ × ℝ, ((d p : ℝ)) ^ 2 =
      (d p : ℝ) + ((d p * (d p - 1) : ℕ) : ℝ) := by
    intro p
    by_cases hp0 : d p = 0
    · simp [hp0]
    · have h1 : 1 ≤ d p := Nat.pos_of_ne_zero hp0
      have hcast : ((d p * (d p - 1) : ℕ) : ℝ) = (d p : ℝ) * ((d p : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
      rw [hcast]
      ring
  have hsqsum : ∑ p ∈ P, ((d p : ℝ)) ^ 2 ≤
      (∑ k ∈ A, (k : ℝ)) + (A.card : ℝ) ^ 2 := by
    calc ∑ p ∈ P, ((d p : ℝ)) ^ 2
        = ∑ p ∈ P, ((d p : ℝ) + ((d p * (d p - 1) : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hterm p
      _ = (∑ p ∈ P, (d p : ℝ)) + ∑ p ∈ P, ((d p * (d p - 1) : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ k ∈ A, (k : ℝ)) + (A.card : ℝ) ^ 2 := by
          rw [hsumR]
          have hpairR : (∑ p ∈ P, ((d p * (d p - 1) : ℕ) : ℝ)) ≤ (A.card : ℝ) ^ 2 := by
            have h := hpair
            have hcast : ((∑ p ∈ P, d p * (d p - 1) : ℕ) : ℝ) ≤
                ((A.card * (A.card - 1) : ℕ) : ℝ) := by exact_mod_cast h
            rw [Nat.cast_sum] at hcast
            have hle : ((A.card * (A.card - 1) : ℕ) : ℝ) ≤ (A.card : ℝ) ^ 2 := by
              cases hA0 : A.card with
              | zero => simp
              | succ a =>
                rw [Nat.cast_mul, Nat.cast_sub (Nat.le_add_left 1 a)]
                simp
                nlinarith [Nat.cast_nonneg (α := ℝ) a]
            exact le_trans hcast hle
          exact add_le_add le_rfl hpairR
  have hquad : (∑ k ∈ A, (k : ℝ)) ^ 2 ≤
      (P.card : ℝ) * (∑ k ∈ A, (k : ℝ)) + (P.card : ℝ) * (A.card : ℝ) ^ 2 := by
    have hcauchy := sq_sum_le_card_mul_sum_sq (s := P) (f := fun p => (d p : ℝ))
    rw [hsumR] at hcauchy
    calc (∑ k ∈ A, (k : ℝ)) ^ 2 ≤ (P.card : ℝ) * ∑ p ∈ P, ((d p : ℝ)) ^ 2 := hcauchy
      _ ≤ (P.card : ℝ) * ((∑ k ∈ A, (k : ℝ)) + (A.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsqsum (Nat.cast_nonneg _)
      _ = (P.card : ℝ) * (∑ k ∈ A, (k : ℝ)) + (P.card : ℝ) * (A.card : ℝ) ^ 2 := by ring
  by_cases hn0 : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hn0
    subst hPempty
    simp [lineIncidenceSet, hA]
  · have hnpos : (1 : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have ht1 : (1 : ℝ) ≤ Real.sqrt (P.card : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hnpos
    have ht0 : (0 : ℝ) ≤ Real.sqrt (P.card : ℝ) := Real.sqrt_nonneg _
    have hnn : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have hMnn : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    by_contra hcon
    have hgt : (P.card : ℝ) + (A.card : ℝ) * Real.sqrt (P.card : ℝ) <
        ∑ k ∈ A, (k : ℝ) := not_le.mp hcon
    set S : ℝ := ∑ k ∈ A, (k : ℝ) with hSdef
    set t : ℝ := Real.sqrt (P.card : ℝ) with htdef
    have hSpos : 0 < S := lt_of_le_of_lt (by positivity) hgt
    have hsq : t ^ 2 = (P.card : ℝ) := Real.sq_sqrt hnn
    have h1 : ((P.card : ℝ) + (A.card : ℝ) * t) * S < S ^ 2 := by
      have hdiff : 0 < S - ((P.card : ℝ) + (A.card : ℝ) * t) := sub_pos.mpr hgt
      nlinarith [mul_pos hdiff hSpos]
    have h2 : (P.card : ℝ) * S + (P.card : ℝ) * (A.card : ℝ) ^ 2 ≤
        ((P.card : ℝ) + (A.card : ℝ) * t) * S := by
      nlinarith [mul_pos (sub_pos.mpr hgt) (lt_of_lt_of_le one_pos ht1), hsq, ht1, hnn, hMnn, hSpos,
        mul_nonneg hMnn hnn, mul_nonneg ht0 hnn]
    linarith [hquad, h1, h2]

open Classical in
private lemma two_mul_sum_ge_card_mul_pred (s : Finset ℕ) :
    s.card * (s.card - 1) ≤ 2 * ∑ k ∈ s, k := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      set a := s.max' hne with ha
      have hamem : a ∈ s := Finset.max'_mem s hne
      have hcard : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem hamem
      have hlt : (s.erase a).card ≤ a := by
        calc (s.erase a).card ≤ (Finset.range a).card :=
              Finset.card_le_card (by
                intro k hk
                rw [Finset.mem_erase] at hk
                rw [Finset.mem_range]
                exact lt_of_le_of_ne (Finset.le_max' s k hk.2) hk.1)
          _ = a := Finset.card_range a
      have ihs := ih (s.erase a) (Finset.erase_ssubset hamem)
      rw [hcard] at ihs
      have hsum : ∑ k ∈ s, k = a + ∑ k ∈ s.erase a, k := by
        rw [← Finset.add_sum_erase s _ hamem]
      have h1 : s.card * (s.card - 1) ≤
          (s.card - 1) * (s.card - 1 - 1) + 2 * a := by
        by_cases hc : s.card ≤ 1
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
          · rw [h]; simp
          · rw [h]; simp
        · have hc' : 2 ≤ s.card := by omega
          obtain ⟨k, hk⟩ : ∃ k, s.card = k + 2 := ⟨s.card - 2, by omega⟩
          have hlt2 : k + 1 ≤ a := by
            have h2 := hlt
            rw [hcard, hk] at h2
            have h2' : (k + 2) - 1 = k + 1 := by omega
            rw [h2'] at h2
            exact h2
          rw [hk]
          have e1 : (k + 2) - 1 = k + 1 := by omega
          have e2 : (k + 1) - 1 = k := by omega
          rw [e1, e2]
          calc (k + 2) * (k + 1)
              = (k + 1) * k + 2 * (k + 1) := by ring
            _ ≤ (k + 1) * k + 2 * a :=
                Nat.add_le_add_left (Nat.mul_le_mul_left 2 hlt2) _
      calc s.card * (s.card - 1)
          ≤ (s.card - 1) * (s.card - 1 - 1) + 2 * a := h1
        _ ≤ 2 * ∑ k ∈ s.erase a, k + 2 * a :=
            Nat.add_le_add_right ihs _
        _ = 2 * ∑ k ∈ s, k := by rw [hsum]; ring

open Classical in
private lemma realizable_sum_le (P : Finset (ℝ × ℝ)) :
    ∑ k ∈ lineIncidenceSet P, (k : ℝ) ≤ 7 * (P.card : ℝ) := by
  by_cases hn0 : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hn0
    subst hPempty
    simp [lineIncidenceSet]
  · have hSle := sum_le_aux P
    have hlowNat := two_mul_sum_ge_card_mul_pred (lineIncidenceSet P)
    have hlow : ((lineIncidenceSet P).card : ℝ) * (((lineIncidenceSet P).card : ℝ) - 1) ≤
        2 * ∑ k ∈ lineIncidenceSet P, (k : ℝ) := by
      rcases Nat.eq_zero_or_pos (lineIncidenceSet P).card with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, zero_mul]
        positivity
      · have hcast : (((lineIncidenceSet P).card * ((lineIncidenceSet P).card - 1) : ℕ) : ℝ) ≤
            ((2 * ∑ k ∈ lineIncidenceSet P, k : ℕ) : ℝ) := by exact_mod_cast hlowNat
        rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ (lineIncidenceSet P).card by omega),
          Nat.cast_one, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] at hcast
        exact hcast
    have hnn : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have hnpos : (1 : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have ht1 : (1 : ℝ) ≤ Real.sqrt (P.card : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hnpos
    have hsq : (Real.sqrt (P.card : ℝ)) ^ 2 = (P.card : ℝ) := Real.sq_sqrt hnn
    have hMnn : (0 : ℝ) ≤ ((lineIncidenceSet P).card : ℝ) := Nat.cast_nonneg _
    -- bound on the number of distinct line sizes
    have hm : ((lineIncidenceSet P).card : ℝ) ≤ 4 * Real.sqrt (P.card : ℝ) + 2 := by
      by_contra hcon
      have hmgt : 4 * Real.sqrt (P.card : ℝ) + 2 < ((lineIncidenceSet P).card : ℝ) :=
        not_le.mp hcon
      set t := Real.sqrt (P.card : ℝ) with htdef
      set M := ((lineIncidenceSet P).card : ℝ) with hMdef
      nlinarith [mul_pos (sub_pos.mpr hmgt) (show (0:ℝ) < M - 1 - 2 * t by linarith),
        mul_pos (sub_pos.mpr hmgt) (show (0:ℝ) < 4 * t + 2 by linarith),
        hlow, hSle, hsq, ht1, hMnn]
    -- combine with the sum bound, using √n ≤ n for n ≥ 1
    have htn : Real.sqrt (P.card : ℝ) ≤ (P.card : ℝ) := by
      rw [← Real.sqrt_one] at ht1
      calc Real.sqrt (P.card : ℝ) ≤ Real.sqrt ((P.card : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [hnpos, hnn])
        _ = (P.card : ℝ) := Real.sqrt_sq hnn
    nlinarith [hSle, hm, htn, hnn, hMnn, Real.sqrt_nonneg (P.card : ℝ)]

open Classical in
private lemma card_filter_sum_le_exp (n N : ℕ) (hN : 1 ≤ N) :
    (((Finset.range (n + 1)).powerset.filter fun A : Finset ℕ =>
      ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)).card : ℝ) ≤ Real.exp (7 * Real.sqrt (N : ℝ)) := by
  set s : ℝ := Real.sqrt (N : ℝ) + 1 with hsdef
  set t : ℝ := Real.exp (-(1 / s)) with htdef
  have hspos : (0 : ℝ) < s := by
    rw [hsdef]
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) one_pos
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hsdef]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have htpos : (0 : ℝ) < t := Real.exp_pos _
  have htlt : t < 1 := by
    rw [htdef, Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (by positivity)
  have ht1le : t ≤ 1 := htlt.le
  -- generating-function identity
  have hprod : ∏ k ∈ Finset.range (n + 1), (1 + t ^ k) =
      ∑ A ∈ (Finset.range (n + 1)).powerset, t ^ (∑ k ∈ A, k) := by
    have h := Finset.prod_add (fun k => t ^ k) (fun _ => (1 : ℝ)) (Finset.range (n + 1))
    simp only [Finset.prod_const_one, mul_one] at h
    calc ∏ k ∈ Finset.range (n + 1), (1 + t ^ k)
        = ∏ k ∈ Finset.range (n + 1), (t ^ k + 1) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [add_comm]
      _ = ∑ A ∈ (Finset.range (n + 1)).powerset, ∏ i ∈ A, t ^ i := h
      _ = ∑ A ∈ (Finset.range (n + 1)).powerset, t ^ (∑ k ∈ A, k) := by
          apply Finset.sum_congr rfl
          intro A hA
          exact Finset.prod_pow_eq_pow_sum A (fun k => k) t
  -- the filtered family has at most the product many members, weighted by t^N
  have hcard_le : ((((Finset.range (n + 1)).powerset.filter fun A : Finset ℕ =>
      ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)).card : ℝ) * t ^ N) ≤
      ∏ k ∈ Finset.range (n + 1), (1 + t ^ k) := by
    have hstep1 : ((((Finset.range (n + 1)).powerset.filter fun A : Finset ℕ =>
        ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)).card : ℝ) * t ^ N) =
        ∑ A ∈ (Finset.range (n + 1)).powerset.filter (fun A : Finset ℕ =>
          ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)), t ^ N := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hstep1, hprod]
    calc ∑ A ∈ (Finset.range (n + 1)).powerset.filter (fun A : Finset ℕ =>
            ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)), t ^ N
        ≤ ∑ A ∈ (Finset.range (n + 1)).powerset.filter (fun A : Finset ℕ =>
            ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)), t ^ (∑ k ∈ A, k) := by
          apply Finset.sum_le_sum
          intro A hA
          rw [Finset.mem_filter] at hA
          have hNat : ∑ k ∈ A, k ≤ N := by
            have hcast : ((∑ k ∈ A, k : ℕ) : ℝ) ≤ (N : ℝ) := by
              rw [Nat.cast_sum]
              exact hA.2
            exact_mod_cast hcast
          exact pow_le_pow_of_le_one htpos.le ht1le hNat
      _ ≤ ∑ A ∈ (Finset.range (n + 1)).powerset, t ^ (∑ k ∈ A, k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro A hA _
            exact pow_nonneg htpos.le _
  -- bound the product by splitting the log sum at s
  have hgeom : ∑ k ∈ Finset.range (n + 1), t ^ k ≤ 1 / (1 - t) := by
    have hmul : (∑ k ∈ Finset.range (n + 1), t ^ k) * (1 - t) ≤ 1 := by
      have h := geom_sum_mul t (n + 1)
      have h2 : (∑ k ∈ Finset.range (n + 1), t ^ k) * (1 - t) = 1 - t ^ (n + 1) := by
        calc (∑ k ∈ Finset.range (n + 1), t ^ k) * (1 - t)
            = -((∑ k ∈ Finset.range (n + 1), t ^ k) * (t - 1)) := by ring
          _ = -(t ^ (n + 1) - 1) := by rw [h]
          _ = 1 - t ^ (n + 1) := by ring
      rw [h2]
      have := pow_nonneg htpos.le (n + 1)
      linarith
    rw [le_div_iff₀ (show (0 : ℝ) < 1 - t by linarith)]
    exact hmul
  have hone : (1 : ℝ) / (1 - t) ≤ s + 1 := by
    have hexp : 1 / s + 1 ≤ Real.exp (1 / s) := Real.add_one_le_exp _
    have ht_le : t ≤ s / (s + 1) := by
      have h1 : s / (s + 1) = 1 / (1 / s + 1) := by
        rw [div_add_one (ne_of_gt hspos), one_div_div, add_comm (1 : ℝ) s]
      rw [htdef, Real.exp_neg, inv_eq_one_div, h1]
      exact one_div_le_one_div_of_le (by positivity) hexp
    have h1t : (1 : ℝ) / (s + 1) ≤ 1 - t := by
      have h2 : (1 : ℝ) - s / (s + 1) = 1 / (s + 1) := by
        field_simp
        ring
      linarith [ht_le, h2]
    have hpos1 : (0 : ℝ) < 1 / (s + 1) := by positivity
    have h3 := one_div_le_one_div_of_le hpos1 h1t
    rwa [one_div_one_div] at h3
  have hlogsum : ∑ k ∈ Finset.range (n + 1), Real.log (1 + t ^ k) ≤
      (s + 1) * (Real.log 2 + 1) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
      (fun k : ℕ => (k : ℝ) < s) (fun k : ℕ => Real.log (1 + t ^ k))
    have hhead : ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s),
        Real.log (1 + t ^ k) ≤ (s + 1) * Real.log 2 := by
      have hterm : ∀ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s),
          Real.log (1 + t ^ k) ≤ Real.log 2 := by
        intro k hk
        apply Real.log_le_log (by positivity)
        have htk : t ^ k ≤ 1 := pow_le_one₀ htpos.le ht1le
        linarith
      have hcard : (((Finset.range (n + 1)).filter
          (fun k : ℕ => (k : ℝ) < s)).card : ℝ) ≤ s + 1 := by
        have hsub : (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s) ⊆
            Finset.range (Nat.ceil s) := by
          intro k hk
          rw [Finset.mem_filter, Finset.mem_range] at hk
          rw [Finset.mem_range]
          exact Nat.cast_lt.mp (lt_of_lt_of_le hk.2 (Nat.le_ceil s))
        have hle : ((Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s)).card ≤
            Nat.ceil s := by
          calc ((Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s)).card
              ≤ (Finset.range (Nat.ceil s)).card := Finset.card_le_card hsub
            _ = Nat.ceil s := Finset.card_range _
        have hceil : (Nat.ceil s : ℝ) ≤ s + 1 :=
          (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ s by positivity)).le
        exact le_trans (by exact_mod_cast hle) hceil
      calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s),
            Real.log (1 + t ^ k)
          ≤ ((Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s)).card •
              Real.log 2 :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = (((Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) < s)).card : ℝ) *
              Real.log 2 := by rw [nsmul_eq_mul]
        _ ≤ (s + 1) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hcard (Real.log_nonneg (by norm_num))
    have htail : ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) < s),
        Real.log (1 + t ^ k) ≤ s + 1 := by
      calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) < s),
              Real.log (1 + t ^ k)
          ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) < s), t ^ k := by
            apply Finset.sum_le_sum
            intro k hk
            have hpos : (0 : ℝ) < 1 + t ^ k :=
              add_pos_of_pos_of_nonneg one_pos (pow_nonneg htpos.le k)
            have hle := Real.log_le_sub_one_of_pos hpos
            have htk : (0 : ℝ) ≤ t ^ k := pow_nonneg htpos.le k
            linarith
        _ ≤ ∑ k ∈ Finset.range (n + 1), t ^ k := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.filter_subset _ _
            · intro k _ _
              exact pow_nonneg htpos.le k
        _ ≤ 1 / (1 - t) := hgeom
        _ ≤ s + 1 := hone
    have heq : (s + 1) * Real.log 2 + (s + 1) = (s + 1) * (Real.log 2 + 1) := by ring
    linarith [hsplit, hhead, htail, heq]
  have hprodbound : ∏ k ∈ Finset.range (n + 1), (1 + t ^ k) ≤
      Real.exp ((s + 1) * (Real.log 2 + 1)) := by
    have hpos : ∀ k ∈ Finset.range (n + 1), (0 : ℝ) < 1 + t ^ k := by
      intro k hk
      exact add_pos_of_pos_of_nonneg one_pos (pow_nonneg htpos.le k)
    have hlog : Real.log (∏ k ∈ Finset.range (n + 1), (1 + t ^ k)) =
        ∑ k ∈ Finset.range (n + 1), Real.log (1 + t ^ k) := by
      rw [Real.log_prod]
      intro k hk
      exact ne_of_gt (hpos k hk)
    rw [← Real.exp_log (Finset.prod_pos hpos)]
    rw [hlog]
    exact Real.exp_le_exp.mpr hlogsum
  have htNpos : (0 : ℝ) < t ^ N := pow_pos htpos N
  have hcard2 : (((Finset.range (n + 1)).powerset.filter fun A : Finset ℕ =>
      ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)).card : ℝ) ≤
      (∏ k ∈ Finset.range (n + 1), (1 + t ^ k)) / t ^ N := by
    rw [le_div_iff₀ htNpos]
    exact hcard_le
  have hNs : (N : ℝ) / s ≤ Real.sqrt (N : ℝ) := by
    rw [div_le_iff₀ hspos]
    have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith [Real.sqrt_nonneg (N : ℝ), hsq]
  have htNinv : (t ^ N)⁻¹ ≤ Real.exp (Real.sqrt (N : ℝ)) := by
    have hexpN : t ^ N = Real.exp (-((N : ℝ) / s)) := by
      rw [htdef, ← Real.exp_nat_mul]
      congr 1
      rw [mul_neg, mul_one_div]
    have hinv : (t ^ N)⁻¹ = Real.exp ((N : ℝ) / s) := by
      rw [hexpN, Real.exp_neg, inv_inv]
    rw [hinv]
    exact Real.exp_le_exp.mpr hNs
  calc (((Finset.range (n + 1)).powerset.filter fun A : Finset ℕ =>
        ∑ k ∈ A, (k : ℝ) ≤ (N : ℝ)).card : ℝ)
      ≤ (∏ k ∈ Finset.range (n + 1), (1 + t ^ k)) / t ^ N := hcard2
    _ = (∏ k ∈ Finset.range (n + 1), (1 + t ^ k)) * (t ^ N)⁻¹ := by
        rw [div_eq_mul_inv]
    _ ≤ Real.exp ((s + 1) * (Real.log 2 + 1)) * Real.exp (Real.sqrt (N : ℝ)) :=
        mul_le_mul hprodbound htNinv (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((s + 1) * (Real.log 2 + 1) + Real.sqrt (N : ℝ)) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (7 * Real.sqrt (N : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
        have hlog2 : Real.log 2 ≤ 1 := by
          have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
        nlinarith [hsdef, hsqrt1, hlog2, Real.sqrt_nonneg (N : ℝ)]

open Classical in
/--
**Szemerédi–Trotter bound for line-incidence sets (Erdős Problem 607).** For a finite set
$P \subseteq \mathbb{R}^2$, let $A(P)$ be the set of the numbers $|\ell \cap P|$ over the lines
$\ell$ through at least two distinct points of $P$, and let $F(n)$ be the number of distinct sets
$A(P)$ over all $n$-point sets $P \subseteq \mathbb{R}^2$. There is a real constant $C$ such that
$F(n) \le e^{C\sqrt{n}}$ for every natural number $n$.

Source: T. F. Bloom, Erdős Problems, Problem #607, https://www.erdosproblems.com/607 (status
PROVED); resolution: E. Szemerédi and W. T. Trotter, Extremal problems in discrete geometry,
Combinatorica 3 (1983), 381-392, erdosproblems.com/607: proved by Szemerédi and Trotter [SzTr83],
https://doi.org/10.1007/BF02579194.
-/
theorem lineIncidenceSetCountSubexponential_holds :
    lineIncidenceSetCountSubexponential := by
  refine ⟨25, fun n => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0
    have hle : lineIncidenceSetCount 0 ≤ 1 := by
      unfold lineIncidenceSetCount
      rw [Finset.card_le_one]
      intro A hA B hB
      obtain ⟨P, hPc, hPA⟩ := (Finset.mem_filter.mp hA).2
      obtain ⟨Q, hQc, hQB⟩ := (Finset.mem_filter.mp hB).2
      have hP : P = ∅ := Finset.card_eq_zero.mp hPc
      have hQ : Q = ∅ := Finset.card_eq_zero.mp hQc
      subst hP
      subst hQ
      have hempty : lineIncidenceSet (∅ : Finset (ℝ × ℝ)) = ∅ := by
        simp [lineIncidenceSet]
      rw [hempty] at hPA hQB
      rw [← hPA, ← hQB]
    have hleR : (lineIncidenceSetCount 0 : ℝ) ≤ 1 := by exact_mod_cast hle
    simpa using hleR
  · have hsub : lineIncidenceSetCount n ≤
        (((Finset.range (n + 1)).powerset.filter fun A : Finset ℕ =>
          ∑ k ∈ A, (k : ℝ) ≤ ((7 * n : ℕ) : ℝ)).card) := by
      unfold lineIncidenceSetCount
      apply Finset.card_le_card
      intro A hA
      rw [Finset.mem_filter] at hA ⊢
      refine ⟨hA.1, ?_⟩
      obtain ⟨P, hPcard, hPA⟩ := hA.2
      rw [← hPA]
      calc ∑ k ∈ lineIncidenceSet P, (k : ℝ) ≤ 7 * (P.card : ℝ) := realizable_sum_le P
        _ = ((7 * n : ℕ) : ℝ) := by rw [hPcard]; push_cast; ring
    have hcount := card_filter_sum_le_exp n (7 * n) (by omega : 1 ≤ 7 * n)
    have hleR : (lineIncidenceSetCount n : ℝ) ≤ Real.exp (7 * Real.sqrt ((7 * n : ℕ) : ℝ)) := by
      exact le_trans (by exact_mod_cast hsub) hcount
    have hsqrtle : 7 * Real.sqrt ((7 * n : ℕ) : ℝ) ≤ 25 * Real.sqrt (n : ℝ) := by
      have hcast : ((7 * n : ℕ) : ℝ) = 7 * (n : ℝ) := by push_cast; ring
      rw [hcast]
      have h1 : (7 * Real.sqrt (7 * (n : ℝ))) ^ 2 ≤ (25 * Real.sqrt (n : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 7 * (n:ℝ)),
          mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h2 := sq_le_sq.mp h1
      rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h2
    exact le_trans hleR (Real.exp_le_exp.mpr hsqrtle)

end MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607Wanted
