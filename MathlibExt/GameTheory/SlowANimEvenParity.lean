/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SlowANim
import all MathlibExt.GameTheory.SlowANimGeneralReduction

/-!
# Parity in Slow A-Nim with an even number of stacks

When one stack or all stacks may be played, and the number of stacks is even, the
P-positions are exactly those with even total and even minimum.

## References

* Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
  Slow A-Nim*, INTEGERS 26 (2026), Article G3, pp. 1–25, Theorem 2(2).
* Michael H. Albert, Richard J. Nowakowski, and David Wolfe, *Lessons in Play: An Introduction
  to Combinatorial Game Theory*, 2nd ed., CRC Press, 2019, §2.3, for the P-position criterion.
* Elwyn R. Berlekamp, John H. Conway, and Richard K. Guy, *Winning Ways for Your Mathematical
  Plays*, 2nd ed., vol. 1, A. K. Peters, 2001, Ch. 4, for the same impartial-game background.
-/

namespace MetaMathlibExt

/-- **P-positions of Slow A-Nim with A = {1, n}, n even.** Let $n \ge 1$ be even and let
$A = \{1, n\}$. A position $p = (p_1, \dots, p_n)$ of Slow$A$-Nim on $n$ stacks is a P-position
if and only if its total number of tokens $p_1 + \dots + p_n$ and its smallest stack
$\min_i p_i$ are both even.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 2. -/
public theorem slowANim_one_n_even_isP_iff (n : ℕ) (hn : 0 < n) (hne : Even n)
    (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n {1, n}) p ↔
      Even (∑ i, p i) ∧ ∃ i, (∀ j, p i ≤ p j) ∧ Even (p i) := by
  induction p using (measure (fun p : Fin n → ℕ => ∑ i, p i)).wf.induction with
  | h p ih =>
    obtain ⟨i, -, hmin⟩ := Finset.exists_min_image Finset.univ p
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hleast (j : Fin n) : p i ≤ p j := hmin j (Finset.mem_univ j)
    have hparity (S : Finset (Fin n)) (hpos : ∀ j ∈ S, 1 ≤ p j) :
        Even (∑ j, p j) ↔ (Even (∑ j, slowANimAfter p S j) ↔ Even S.card) := by
      rw [← slowANim_generalReduction.sum_after_add_card p S hpos, Nat.even_add]
    have hsingle (j : Fin n) (hj : 1 ≤ p j) :
        Even (∑ k, p k) ↔ ¬ Even (∑ k, slowANimAfter p {j} k) := by
      simpa using hparity {j} (by simpa using hj)
    have hall (j : Fin n) : slowANimAfter p Finset.univ j = p j - 1 := by
      simp [slowANimAfter]
    have hallMin (j : Fin n) : slowANimAfter p Finset.univ i ≤ slowANimAfter p Finset.univ j := by
      rw [hall, hall]
      exact Nat.sub_le_sub_right (hleast j) _
    have hmove (S : Finset (Fin n)) (hneS : S.Nonempty) (hsize : S.card ∈ ({1, n} : Finset ℕ))
        (hpos : ∀ j ∈ S, 1 ≤ p j) : slowANimAfter p S ∈ slowANimMoves {1, n} p := by
      simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter]
      exact ⟨S, ⟨Finset.mem_univ _, hneS, hsize, hpos⟩, rfl⟩
    rw [SpragueGrundy.isP_iff (slowANimGame n {1, n}) p]
    change (∀ q : Fin n → ℕ, q ∈ slowANimMoves {1, n} p →
      ¬ SpragueGrundy.IsP (slowANimGame n {1, n}) q) ↔ _
    constructor
    · intro hp
      by_contra hbad
      suffices ∃ q ∈ slowANimMoves {1, n} p,
          Even (∑ j, q j) ∧ ∃ k, (∀ j, q k ≤ q j) ∧ Even (q k) by
        obtain ⟨q, hq, hpar⟩ := this
        exact hp q hq ((ih q (sum_lt_of_mem_slowANimMoves {1, n} p q hq)).2 hpar)
      by_cases hsum : Even (∑ j, p j)
      · have hodd := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp
          (fun he => hbad ⟨hsum, i, hleast, he⟩))
        have hpos (j : Fin n) (_ : j ∈ Finset.univ) : 1 ≤ p j := by
          have := hleast j
          omega
        refine ⟨_, hmove Finset.univ ⟨i, Finset.mem_univ i⟩ (by simp) hpos, ?_,
          i, hallMin, ?_⟩
        · exact ((hparity Finset.univ hpos).1 hsum).2 (by simpa using hne)
        · rw [hall, Nat.even_iff]
          omega
      · by_cases he : Even (p i)
        · -- An odd total rules out equal heights, so a higher stack can be played.
          obtain ⟨k, hk⟩ : ∃ k, p i < p k := by
            by_contra! hh
            have hconst (j : Fin n) : p j = p i := le_antisymm (hh j) (hleast j)
            apply hsum
            rw [show p = (fun _ => p i) from funext hconst]
            simpa using hne.mul_right (p i)
          have hkpos : 1 ≤ p k := by omega
          have hik : i ≠ k := by
            intro h
            exact (lt_irrefl (p k)) (h ▸ hk)
          have hafter : slowANimAfter p {k} i = p i := by simp [slowANimAfter, hik]
          refine ⟨_, hmove {k} (by simp) (by simp) (by simpa using hkpos),
            not_not.mp (mt (hsingle k hkpos).2 hsum), i, ?_, ?_⟩
          · intro j
            rw [hafter]
            by_cases hj : j = k
            · subst j
              simpa [slowANimAfter] using Nat.le_sub_one_of_lt hk
            · simpa [slowANimAfter, hj] using hleast j
          · simpa [hafter] using he
        · have hodd := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
          have hipos : 1 ≤ p i := by omega
          refine ⟨_, hmove {i} (by simp) (by simp) (by simpa using hipos),
            not_not.mp (mt (hsingle i hipos).2 hsum), i, ?_, ?_⟩
          · intro j
            by_cases hj : j = i
            · simp [hj]
            · simp [slowANimAfter, hj, (Nat.sub_le (p i) 1).trans (hleast j)]
          · simp only [slowANimAfter, Finset.mem_singleton_self, ite_true, Nat.even_iff]
            omega
    · rintro ⟨hsum, k, hk, he⟩ q hq hPq
      obtain ⟨hqsum, l, hl, hle⟩ := (ih q (sum_lt_of_mem_slowANimMoves {1, n} p q hq)).1 hPq
      simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter] at hq
      obtain ⟨S, ⟨-, -, hcard, hpos⟩, rfl⟩ := hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
      rcases hcard with hcard | hcard
      · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
        exact (hsingle j (hpos j (Finset.mem_singleton_self j))).1 hsum hqsum
      · have hS : S = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simp [hcard]
        subst S
        have hpmin : p i = p k := le_antisymm (hleast k) (hk i)
        have hqmin : slowANimAfter p Finset.univ i = slowANimAfter p Finset.univ l :=
          le_antisymm (hallMin l) (hl i)
        have hbefore : Even (p i) := hpmin ▸ he
        have hafter : Even (p i - 1) := by simpa only [← hqmin, hall] using hle
        have hipos := hpos i (Finset.mem_univ i)
        rw [Nat.even_iff] at hbefore hafter
        omega

end MetaMathlibExt
