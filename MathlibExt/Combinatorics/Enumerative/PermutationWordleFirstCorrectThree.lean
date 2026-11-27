/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationWordle
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Three-guess permutation Wordle solves with no early correct positions

When both of the first two guesses miss every position, the third guess is the inverse square
of the strategy's full-size component. For a full cycle, this secret indeed misses both guesses.
-/

namespace MetaMathlibExt

private theorem nextGuess_of_forall_ne {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (g : Fin n → Fin n) (h : ∀ i, g i ≠ π i) :
    permWordleNextGuess S π g = g ∘ (S n).symm := by
  have allPositions (I : Finset (Fin n)) (hI : I = Finset.univ) :
      permuteAlong I rfl (S I.card) g = g ∘ (S n).symm := by
    subst I
    have useCard (m : ℕ) (hm : (Finset.univ : Finset (Fin n)).card = m) (hmn : m = n) :
        permuteAlong Finset.univ hm (S m) g = g ∘ (S n).symm := by
      subst hmn
      exact permuteAlong_univ hm _ _
    exact useCard _ rfl (by simp)
  exact allPositions _ (Finset.eq_univ_of_forall fun i =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i⟩)

/-- **A unique three-guess solve with no early correct position.** Let $n \ge 4$ and let $S$ be
a permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) whose
component $S[n]$ is an $n$-cycle. Exactly one permutation $\pi$ of $\{0, \dots, n-1\}$ is
guessed by $S$ in exactly three guesses with the third guess being the first guess that has a
correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 11 (`jis-2026-26.1.7-thm-11`). -/
public theorem card_solvedIn_three_firstCorrectAt_three (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hcyc : (S n).IsCycle)
    (hsupp : (S n).support = Finset.univ) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 3} = 1 := by
  let σ : Equiv.Perm (Fin n) := (S n)⁻¹
  let τ : Equiv.Perm (Fin n) := σ ^ 2
  have guess_one (π : Equiv.Perm (Fin n)) (h₀ : ∀ i, i ≠ π i) :
      permWordleGuess S π 1 = ⇑σ :=
    permWordleGuess_one_of_forall_ne S π fun i => (h₀ i).symm
  have guess_two (π : Equiv.Perm (Fin n)) (h₀ : ∀ i, i ≠ π i) (h₁ : ∀ i, σ i ≠ π i) :
      permWordleGuess S π 2 = ⇑τ := by
    change permWordleGuess S π (1 + 1) = ⇑τ
    rw [permWordleGuess_succ, guess_one π h₀]
    have h := nextGuess_of_forall_ne S π σ h₁
    change permWordleNextGuess S π σ = ⇑σ ∘ ⇑σ at h
    simpa only [τ, pow_two, Equiv.Perm.coe_mul] using h
  have hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    have hset : (↑(S n).support : Set (Fin n)) = {i | S n i ≠ i} := by
      ext i
      simp only [Finset.mem_coe, Equiv.Perm.mem_support, Set.mem_ofPred_eq]
    rw [← hsupp, hset]
    exact hcyc.isCycleOn.inv
  -- Every position has period n, so neither of the first two powers returns it to itself.
  have hpow (i : Fin n) (k : ℕ) (hk : 0 < k) (hkn : k < n) : (σ ^ k) i ≠ i := by
    intro h
    apply Nat.not_dvd_of_pos_of_lt hk hkn
    simpa using (hcycle.pow_apply_eq (Finset.mem_univ i)).mp h
  have h₀ (i : Fin n) : i ≠ τ i := (hpow i 2 (by decide) (by omega)).symm
  have h₁ (i : Fin n) : σ i ≠ τ i := by
    intro h
    have hi : σ i = σ (σ i) := by simpa only [τ, pow_two, Equiv.Perm.mul_apply] using h
    apply hpow i 1 (by decide) (by omega)
    simpa only [pow_one] using (σ.injective hi).symm
  have h₂ := guess_two τ h₀ h₁
  have hmiss (j : ℕ) (hj : j < 2) (i : Fin n) : permWordleGuess S τ j i ≠ τ i := by
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact h₀ i
    · rw [guess_one τ h₀]
      exact h₁ i
  let i₀ : Fin n := ⟨0, by omega⟩
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨τ, ?_, ?_⟩, ?_⟩
  · exact ⟨by decide, h₂, fun j hj heq => hmiss j hj i₀ (congrFun heq i₀)⟩
  · exact ⟨by decide, ⟨i₀, congrFun h₂ i₀⟩, hmiss⟩
  · intro π
    obtain ⟨hsolve, hfirst⟩ := π.property
    have hzero : ∀ i, i ≠ π.val i := hfirst.2.2 0 (by decide)
    have hone := hfirst.2.2 1 (by decide)
    rw [guess_one π.val hzero] at hone
    exact Subtype.ext (Equiv.coe_inj.mp (hsolve.2.1.symm.trans (guess_two π.val hzero hone)))

end MetaMathlibExt
