/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ArndtCompositions
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Arndt compositions with parts at most four

Removing the first descending pair leaves a shorter Arndt composition. The six possible
pairs have weights `3, 4, 5, 5, 6, 7`; the empty composition or a singleton contributes one
extra composition at each weight from `0` to `4`. Iterating the Narayana recurrence gives
the same equations for the shifted sequence.
-/

namespace MetaMathlibExt

open Finset

private def leadingPairs : Finset (ℕ × ℕ) := {(2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (4, 3)}

private lemma mem_leadingPairs {a b : ℕ} : (a, b) ∈ leadingPairs ↔ 0 < b ∧ b < a ∧ a ≤ 4 := by
  simp [leadingPairs, Prod.mk.injEq]; omega

private abbrev countFour : ℕ → ℕ → ℕ := arndtCompositionCount (fun i => i ≤ 4)

private abbrev valid {k : ℕ} (c : Fin k → ℕ) : Prop :=
  (∀ i, 0 < c i ∧ c i ≤ 4) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i

private abbrev tuples (n k : ℕ) : Finset (Fin k → ℕ) :=
  (Nat.antidiagonalTuple k n).filter valid

-- As in the unrestricted pair decomposition, shifting both indices by two preserves the descents.
private lemma valid_cons {k a b : ℕ} {c : Fin k → ℕ} :
    valid (Fin.cons a (Fin.cons b c)) ↔ (a, b) ∈ leadingPairs ∧ valid c := by
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨mem_leadingPairs.mpr ⟨(hp (Fin.succ 0)).1, hd 0 (Fin.succ 0) rfl rfl, (hp 0).2⟩,
      fun i ↦ hp i.succ.succ, ?_⟩
    intro i j hi hj
    apply hd i.succ.succ j.succ.succ <;> simp only [Fin.val_succ] <;> omega
  · rintro ⟨hab, hp, hd⟩
    obtain ⟨hb, hba, ha⟩ := mem_leadingPairs.mp hab
    constructor
    · intro i
      refine Fin.cases ⟨hb.trans hba, ha⟩ (fun i ↦ ?_) i
      exact Fin.cases ⟨hb, hba.le.trans ha⟩ hp i
    · intro i
      refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
      · intro j _ hj
        have : j = Fin.succ 0 := Fin.ext (by simpa using hj)
        simpa [this] using hba
      · simp
      · intro j
        refine Fin.cases (by simp) (fun j ↦ Fin.cases (by simp) (fun j ↦ ?_) j) j
        intro hi hj
        exact hd i j (by simp only [Fin.val_succ] at hi; omega)
          (by simp only [Fin.val_succ] at hj; omega)

-- A shift contributes nothing when the removed pair weighs more than the whole composition.
private def shift (f : ℕ → ℕ) (d n : ℕ) : ℕ := if d ≤ n then f (n - d) else 0

private lemma count_pair (n k : ℕ) :
    countFour n (k + 2) = ∑ p ∈ leadingPairs, shift (fun t ↦ countFour t k) (p.1 + p.2) n := by
  let pieces := leadingPairs.sigma fun p ↦
    if p.1 + p.2 ≤ n then tuples (n - (p.1 + p.2)) k else ∅
  let join (z : Σ _ : ℕ × ℕ, Fin k → ℕ) : Fin (k + 2) → ℕ :=
    Fin.cons z.1.1 (Fin.cons z.1.2 z.2)
  let split (c : Fin (k + 2) → ℕ) : Σ _ : ℕ × ℕ, Fin k → ℕ :=
    ⟨(c 0, c (Fin.succ 0)), fun i ↦ c i.succ.succ⟩
  have rejoin (c : Fin (k + 2) → ℕ) : join (split c) = c := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i) i
  have mem_pieces (p : ℕ × ℕ) (c : Fin k → ℕ) :
      (⟨p, c⟩ : Σ _ : ℕ × ℕ, Fin k → ℕ) ∈ pieces ↔
        p ∈ leadingPairs ∧ (∑ i, c i) + (p.1 + p.2) = n ∧ valid c := by
    by_cases h : p.1 + p.2 ≤ n
    · have hw : (∑ i, c i) = n - (p.1 + p.2) ↔ (∑ i, c i) + (p.1 + p.2) = n := by omega
      simp only [pieces, mem_sigma, h, ↓reduceIte, tuples, mem_filter,
        Nat.mem_antidiagonalTuple, hw]
    · have hw : ¬ (∑ i, c i) + (p.1 + p.2) = n := by omega
      simp [pieces, h, hw]
  have hcard : pieces.card = ∑ p ∈ leadingPairs, shift (fun t ↦ countFour t k) (p.1 + p.2) n := by
    rw [card_sigma]
    apply sum_congr rfl
    intro p _
    by_cases h : p.1 + p.2 ≤ n <;> simp [h, shift, tuples, arndtCompositionCount, valid]
  rw [← hcard]
  change (tuples n (k + 2)).card = pieces.card
  symm
  apply card_nbij' join split
  · rintro ⟨p, c⟩ hz
    obtain ⟨hp, hs, hc⟩ := (mem_pieces p c).mp hz
    simp only [mem_coe, tuples, mem_filter, Nat.mem_antidiagonalTuple, join, Fin.sum_cons,
      valid_cons]
    exact ⟨by omega, hp, hc⟩
  · intro c hc
    obtain ⟨hs, hv⟩ := mem_filter.mp hc
    rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
    change c 0 + (c (Fin.succ 0) + ∑ i : Fin k, c i.succ.succ) = n at hs
    have ⟨hp, ht⟩ := valid_cons.mp (show valid (join (split c)) by rwa [rejoin])
    refine (mem_pieces _ _).mpr ⟨hp, ?_, ht⟩
    change (∑ i : Fin k, c i.succ.succ) + (c 0 + c (Fin.succ 0)) = n
    omega
  · intro _ _
    rfl
  · intro c _
    exact rejoin c

private def total (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), countFour n k

private lemma count_of_lt {n k : ℕ} (h : n < k) : countFour n k = 0 := by
  change (tuples n k).card = 0
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hs, hp, _⟩ := mem_filter.mp hc
  have hk := sum_le_sum (s := univ) fun i _ ↦ (show 1 ≤ c i from (hp i).1)
  simp [Nat.mem_antidiagonalTuple.mp hs] at hk
  omega

private lemma total_eq_sum {n N : ℕ} (h : n ≤ N) :
    total n = ∑ k ∈ range (N + 1), countFour n k := by
  apply sum_subset (range_mono (by omega))
  intro k _ hk
  exact count_of_lt (by simpa using hk)

private lemma short_count (n : ℕ) : countFour n 0 + countFour n 1 = if n ≤ 4 then 1 else 0 := by
  rcases n with _ | n
  · simp [arndtCompositionCount, Fin.forall_fin_one, filter_singleton]
  · by_cases h : n < 4 <;> simp [arndtCompositionCount, Fin.forall_fin_one, filter_singleton, h]

private lemma total_pair (n : ℕ) :
    total n = (if n ≤ 4 then 1 else 0) + ∑ p ∈ leadingPairs, shift total (p.1 + p.2) n := by
  rw [total_eq_sum (N := n + 2) (by omega), show n + 2 + 1 = 2 + (n + 1) by omega,
    sum_range_add, sum_range_succ, sum_range_succ, sum_range_zero, zero_add, short_count]
  congr 1
  simp_rw [Nat.add_comm 2, count_pair]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases h : p.1 + p.2 ≤ n
  · simp [shift, h, total_eq_sum (Nat.sub_le n (p.1 + p.2))]
  · simp [shift, h]

private abbrev cows (n : ℕ) : ℕ := narayanaCowsSequence (n + 1)

private lemma cows_step (n : ℕ) : cows (n + 3) = cows (n + 2) + cows n := rfl

private lemma sum_pair_weights (f : ℕ → ℕ) :
    ∑ p ∈ leadingPairs, f (p.1 + p.2) = f 3 + f 4 + f 5 + f 5 + f 6 + f 7 := by
  simp [leadingPairs, add_assoc]

private lemma cows_pair (n : ℕ) :
    cows n = (if n ≤ 4 then 1 else 0) + ∑ p ∈ leadingPairs, shift cows (p.1 + p.2) n := by
  rw [sum_pair_weights (fun d ↦ shift cows d n)]
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> try decide
  simp only [shift, show ¬ n + 7 ≤ 4 by omega, ite_false, zero_add,
    show 3 ≤ n + 7 by omega, show 4 ≤ n + 7 by omega, show 5 ≤ n + 7 by omega,
    show 6 ≤ n + 7 by omega, show 7 ≤ n + 7 by omega, ite_true,
    show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega,
    show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega,
    show n + 7 - 7 = n by omega]
  change cows (n + 7) = _
  -- Expand the terms in the ordinary recurrence until the six pair weights appear.
  have h₄ := cows_step (n + 4)
  have h₃ := cows_step (n + 3)
  have h₂ := cows_step (n + 2)
  have h₁ := cows_step (n + 1)
  have h₀ := cows_step n
  simp only [Nat.add_assoc, Nat.reduceAdd] at h₄ h₃ h₂ h₁
  omega

/-- **Arndt compositions with parts at most 4 and Narayana's cows sequence.** For every
$n \ge 0$, the number of Arndt compositions of $n$ (compositions $(\sigma_1, \dots, \sigma_k)$
with $\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$) with all parts in $\{1, 2, 3, 4\}$,
counting the empty composition when $n = 0$, equals $N_{n+1}$, where $(N_m)$ is Narayana's cows
sequence: $N_0 = 0$, $N_1 = N_2 = 1$ and $N_m = N_{m-1} + N_{m-3}$ for $m \ge 3$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 4 (`jis-2025-25.3.6-thm-4`). -/
public theorem sum_arndtCompositionCount_le_four (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), arndtCompositionCount (fun i => i ≤ 4) n k =
      narayanaCowsSequence (n + 1) := by
  change total n = cows n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [total_pair n, cows_pair n]
    congr 1
    apply sum_congr rfl
    rintro ⟨a, b⟩ hab
    obtain ⟨hb, hba, _⟩ := mem_leadingPairs.mp hab
    dsimp only
    by_cases h : a + b ≤ n
    · simpa only [shift, h, ite_true] using ih (n - (a + b)) (by omega)
    · simp [shift, h]

end MetaMathlibExt
