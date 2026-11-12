/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MixedNashExistence

/-! Matching pennies has a mixed equilibrium by Nash's theorem, and no pure profile is one, so mixed
existence is strictly more than pure existence. A player with no actions rules out any
equilibrium. -/

@[expose] public section

open MathlibExt.GameTheory.MixedNashExistence

namespace MathlibExtTest.GameTheory.MixedNashExistence

def mp : Fin 2 → (Fin 2 → Fin 2) → ℝ :=
  fun i a => if a 0 = a 1 then (if i = 0 then 1 else -1) else (if i = 0 then -1 else 1)

example : ∃ σ : ∀ _ : Fin 2, Convexity.StdSimplex ℝ (Fin 2), IsMixedNash mp σ := by
  exact exists_isMixedNash mp

example (s : Fin 2 → Fin 2) : ¬ IsMixedNash mp (fun i => Convexity.StdSimplex.single (s i)) := by
  have hpure : ∀ (t : Fin 2 → Fin 2) (k : Fin 2),
      expectedPayoff mp (fun j => Convexity.StdSimplex.single (t j)) k = mp k t := by
    intro t k
    simp only [expectedPayoff]
    have h0 : ∀ a : Fin 2 → Fin 2, a ≠ t →
        (∏ j, ((Convexity.StdSimplex.single (t j) :
          Convexity.StdSimplex ℝ (Fin 2)).weights) (a j)) *
          mp k a = 0 := by
      intro a ha
      have hne : ∃ j, a j ≠ t j := by
        by_contra h
        apply ha
        funext j
        by_contra hj
        exact h ⟨j, hj⟩
      obtain ⟨j, hj⟩ := hne
      have hj01 : j = 0 ∨ j = 1 := by
        have h : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
          intro x
          fin_cases x <;> simp
        exact h j
      rw [Fin.prod_univ_two]
      rcases hj01 with rfl | rfl
      · have hw0 : ((Convexity.StdSimplex.single (t 0) :
            Convexity.StdSimplex ℝ (Fin 2)).weights) (a 0) = 0 := by
          rw [Convexity.StdSimplex.weights_single]
          exact Finsupp.single_eq_of_ne hj
        rw [hw0, zero_mul, zero_mul]
      · have hw1 : ((Convexity.StdSimplex.single (t 1) :
            Convexity.StdSimplex ℝ (Fin 2)).weights) (a 1) = 0 := by
          rw [Convexity.StdSimplex.weights_single]
          exact Finsupp.single_eq_of_ne hj
        rw [hw1, mul_zero, zero_mul]
    rw [Fintype.sum_eq_single t h0]
    have h1 : ∀ j : Fin 2,
        ((Convexity.StdSimplex.single (t j) : Convexity.StdSimplex ℝ (Fin 2)).weights) (t j) =
            1 := by
      intro j
      rw [Convexity.StdSimplex.weights_single]
      exact Finsupp.single_eq_same
    rw [Fin.prod_univ_two, h1 0, h1 1, mul_one, one_mul]
  have hupd : ∀ (t : Fin 2 → Fin 2) (k : Fin 2) (b : Fin 2),
      Function.update
          (fun i => (Convexity.StdSimplex.single (t i) : Convexity.StdSimplex ℝ (Fin 2))) k
          (Convexity.StdSimplex.single b : Convexity.StdSimplex ℝ (Fin 2)) =
        (fun j => (Convexity.StdSimplex.single ((Function.update t k b) j) :
          Convexity.StdSimplex ℝ (Fin 2))) := by
    intro t k b
    funext j
    by_cases hj : j = k
    · subst hj
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  intro hNash
  by_cases hmatch : s 0 = s 1
  · have h01 : s 1 = 0 ∨ s 1 = 1 := by
      have h : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
        intro x
        fin_cases x <;> simp
      exact h (s 1)
    rcases h01 with hs1 | hs1
    · have hdev := hNash 1 (Convexity.StdSimplex.single 1)
      rw [hupd] at hdev
      have e1 := hpure (Function.update s 1 1) 1
      have e2 := hpure s 1
      rw [e1, e2] at hdev
      have ht0 : (Function.update s 1 1) 0 = 0 := by
        rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        rw [hmatch, hs1]
      have ht1 : (Function.update s 1 1) 1 = 1 := Function.update_self 1 1 s
      have hmt : ¬ (Function.update s 1 1) 0 = (Function.update s 1 1) 1 := by
        rw [ht0, ht1]
        decide
      have g1 : mp 1 (Function.update s 1 1) = 1 := by
        simp only [mp]
        rw [ite_eq_right hmt, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0)]
      have g2 : mp 1 s = -1 := by
        simp only [mp]
        rw [ite_eq_left hmatch, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0)]
      rw [g1, g2] at hdev
      norm_num at hdev
    · have hdev := hNash 1 (Convexity.StdSimplex.single 0)
      rw [hupd] at hdev
      have e1 := hpure (Function.update s 1 0) 1
      have e2 := hpure s 1
      rw [e1, e2] at hdev
      have ht0 : (Function.update s 1 0) 0 = 1 := by
        rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        rw [hmatch, hs1]
      have ht1 : (Function.update s 1 0) 1 = 0 := Function.update_self 1 0 s
      have hmt : ¬ (Function.update s 1 0) 0 = (Function.update s 1 0) 1 := by
        rw [ht0, ht1]
        decide
      have g1 : mp 1 (Function.update s 1 0) = 1 := by
        simp only [mp]
        rw [ite_eq_right hmt, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0)]
      have g2 : mp 1 s = -1 := by
        simp only [mp]
        rw [ite_eq_left hmatch, ite_eq_right (by decide : ¬ (1 : Fin 2) = 0)]
      rw [g1, g2] at hdev
      norm_num at hdev
  · have hdev := hNash 0 (Convexity.StdSimplex.single (s 1))
    rw [hupd] at hdev
    have e1 := hpure (Function.update s 0 (s 1)) 0
    have e2 := hpure s 0
    rw [e1, e2] at hdev
    have ht01 : (Function.update s 0 (s 1)) 0 = (Function.update s 0 (s 1)) 1 := by
      rw [Function.update_self]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    have g1 : mp 0 (Function.update s 0 (s 1)) = 1 := by
      simp only [mp]
      rw [ite_eq_left ht01]
      simp
    have g2 : mp 0 s = -1 := by
      simp only [mp]
      rw [ite_eq_right hmatch]
      simp
    rw [g1, g2] at hdev
    norm_num at hdev

example {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i,
    Fintype (A i)] (i₀ : ι) [IsEmpty (A i₀)] (u : ι → (∀ i, A i) → ℝ) : ¬ ∃ σ : ∀ i,
    Convexity.StdSimplex ℝ (A i), IsMixedNash u σ := by
  rintro ⟨σ, -⟩
  obtain ⟨a⟩ := (σ i₀).nonempty
  exact IsEmpty.false a

end MathlibExtTest.GameTheory.MixedNashExistence
