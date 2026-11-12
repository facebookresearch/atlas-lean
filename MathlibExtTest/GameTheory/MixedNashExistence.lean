/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MixedNashExistence

/-! Matching pennies: a mixed equilibrium exists, the uniform profile is one, and no pure profile
is, so mixed existence is strictly more than pure existence. A player with no actions rules out
any equilibrium. -/

@[expose] public section

open MathlibExt.GameTheory.MixedNashExistence

namespace MathlibExtTest.GameTheory.MixedNashExistence

def mp : Fin 2 → (Fin 2 → Fin 2) → ℝ := fun i a =>
  if a 0 = a 1 then (if i = 0 then 1 else -1) else (if i = 0 then -1 else 1)

-- Test 1: apply main theorem with Brouwer hypothesis
example (hB : ∀ g : (∀ _ : Fin 2, Fin 2 → ℝ) → (∀ _ : Fin 2, Fin 2 → ℝ),
    ContinuousOn g (MixedProfile (fun _ : Fin 2 => Fin 2)) →
    Set.MapsTo g (MixedProfile (fun _ : Fin 2 => Fin 2)) (MixedProfile (fun _ : Fin 2 => Fin 2)) →
    ∃ σ ∈ MixedProfile (fun _ : Fin 2 => Fin 2), g σ = σ) :
    ∃ σ, IsMixedNash mp σ :=
  exists_isMixedNash_of_brouwer hB mp

-- Test 2: uniform profile is an equilibrium
example : IsMixedNash mp (fun _ _ => (1 : ℝ) / 2) := by
  constructor
  · intro i
    constructor
    · intro a
      norm_num
    · rw [Fin.sum_univ_two]
      norm_num
  · intro i τ hτnn hτsum
    have hE0 : expectedPayoff mp (fun _ _ => (1 : ℝ) / 2) i = 0 := by
      unfold expectedPayoff
      have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
        (fun a : Fin 2 → Fin 2 => (∏ j, (fun _ _ => (1 : ℝ) / 2) j (a j)) * mp i a)
      rw [← h, Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
      simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
      fin_cases i <;> simp
    have hE1 : expectedPayoff mp (Function.update (fun _ _ => (1 : ℝ) / 2) i τ) i = 0 := by
      unfold expectedPayoff
      have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
        (fun a : Fin 2 → Fin 2 => (∏ j, (Function.update (fun _ _ => (1 : ℝ) / 2) i τ) j (a j)) *
            mp i a)
      rw [← h, Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
      simp only [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, Fin.prod_univ_two]
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      have h01 : (0 : Fin 2) ≠ 1 := by decide
      fin_cases i <;> simp [Fin.mk_zero, Fin.mk_one, Function.update, h10, h01] <;> ring
    rw [hE1, hE0]

-- Test 3: no pure equilibrium
example : ∀ s : Fin 2 → Fin 2, ¬ IsMixedNash mp (fun i a => if a = s i then (1 : ℝ) else 0) := by
  have hHelper : ∀ x y : Fin 2, ¬ IsMixedNash mp
      (fun i a => if a = ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm (x,
          y)) i then (1 : ℝ) else 0) := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · intro hNash
        obtain ⟨hmem, heq⟩ := hNash
        have hτnn : ∀ a : Fin 2, 0 ≤ (if a = (1 : Fin 2) then (1 : ℝ) else 0) := by
          intro a
          split_ifs <;> norm_num
        have hτsum : ∑ a : Fin 2, (if a = (1 : Fin 2) then (1 : ℝ) else 0) = 1 := by simp
        have hLe := heq 1 _ hτnn hτsum
        have hE : expectedPayoff mp (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
            (0 : Fin 2))) i then (1 : ℝ) else 0) 1 = -1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
                (0 : Fin 2))) i then (1 : ℝ) else 0) j (a j)) * mp 1 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
        have hE' : expectedPayoff mp (Function.update (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
            (0 : Fin 2))) i then (1 : ℝ) else 0) 1 (fun a => if a =
            (1 : Fin 2) then (1 : ℝ) else 0)) 1 = 1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (Function.update (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
                (0 : Fin 2))) i then (1 : ℝ) else 0) 1 (fun a => if a =
                (1 : Fin 2) then (1 : ℝ) else 0)) j (a j)) * mp 1 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, Function.update]
        rw [hE', hE] at hLe
        norm_num at hLe
      · intro hNash
        obtain ⟨hmem, heq⟩ := hNash
        have hτnn : ∀ a : Fin 2, 0 ≤ (if a = (1 : Fin 2) then (1 : ℝ) else 0) := by
          intro a
          split_ifs <;> norm_num
        have hτsum : ∑ a : Fin 2, (if a = (1 : Fin 2) then (1 : ℝ) else 0) = 1 := by simp
        have hLe := heq 0 _ hτnn hτsum
        have hE : expectedPayoff mp (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
            (1 : Fin 2))) i then (1 : ℝ) else 0) 0 = -1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
                (1 : Fin 2))) i then (1 : ℝ) else 0) j (a j)) * mp 0 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
        have hE' : expectedPayoff mp (Function.update (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
            (1 : Fin 2))) i then (1 : ℝ) else 0) 0 (fun a => if a =
            (1 : Fin 2) then (1 : ℝ) else 0)) 0 = 1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (Function.update (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((0 : Fin 2),
                (1 : Fin 2))) i then (1 : ℝ) else 0) 0 (fun a => if a =
                (1 : Fin 2) then (1 : ℝ) else 0)) j (a j)) * mp 0 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, Function.update]
        rw [hE', hE] at hLe
        norm_num at hLe
    · rw [Fin.forall_fin_two]
      constructor
      · intro hNash
        obtain ⟨hmem, heq⟩ := hNash
        have hτnn : ∀ a : Fin 2, 0 ≤ (if a = (0 : Fin 2) then (1 : ℝ) else 0) := by
          intro a
          split_ifs <;> norm_num
        have hτsum : ∑ a : Fin 2, (if a = (0 : Fin 2) then (1 : ℝ) else 0) = 1 := by simp
        have hLe := heq 0 _ hτnn hτsum
        have hE : expectedPayoff mp (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
            (0 : Fin 2))) i then (1 : ℝ) else 0) 0 = -1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
                (0 : Fin 2))) i then (1 : ℝ) else 0) j (a j)) * mp 0 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
        have hE' : expectedPayoff mp (Function.update (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
            (0 : Fin 2))) i then (1 : ℝ) else 0) 0 (fun a => if a =
            (0 : Fin 2) then (1 : ℝ) else 0)) 0 = 1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (Function.update (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
                (0 : Fin 2))) i then (1 : ℝ) else 0) 0 (fun a => if a =
                (0 : Fin 2) then (1 : ℝ) else 0)) j (a j)) * mp 0 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, Function.update]
        rw [hE', hE] at hLe
        norm_num at hLe
      · intro hNash
        obtain ⟨hmem, heq⟩ := hNash
        have hτnn : ∀ a : Fin 2, 0 ≤ (if a = (0 : Fin 2) then (1 : ℝ) else 0) := by
          intro a
          split_ifs <;> norm_num
        have hτsum : ∑ a : Fin 2, (if a = (0 : Fin 2) then (1 : ℝ) else 0) = 1 := by simp
        have hLe := heq 1 _ hτnn hτsum
        have hE : expectedPayoff mp (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
            (1 : Fin 2))) i then (1 : ℝ) else 0) 1 = -1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
                (1 : Fin 2))) i then (1 : ℝ) else 0) j (a j)) * mp 1 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
        have hE' : expectedPayoff mp (Function.update (fun i a => if a =
            ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
            (1 : Fin 2))) i then (1 : ℝ) else 0) 1 (fun a => if a =
            (0 : Fin 2) then (1 : ℝ) else 0)) 1 = 1 := by
          unfold expectedPayoff
          have h := Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm
            (fun a : Fin 2 → Fin 2 => (∏ j, (Function.update (fun i a => if a =
                ((piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm ((1 : Fin 2),
                (1 : Fin 2))) i then (1 : ℝ) else 0) 1 (fun a => if a =
                (0 : Fin 2) then (1 : ℝ) else 0)) j (a j)) * mp 1 a)
          rw [← h, Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two]
          simp [mp, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, Function.update]
        rw [hE', hE] at hLe
        norm_num at hLe
  intro s
  have hseq : s = (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm (s 0, s 1) := by
    ext i
    fin_cases i
    · simp [piFinTwoEquiv_symm_apply, Fin.cons_zero]
    · simp [piFinTwoEquiv_symm_apply, Fin.cons_one]
  rw [hseq]
  exact hHelper (s 0) (s 1)

-- Test 4: empty action set kills existence
example {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (i₀ : ι) [IsEmpty (A i₀)] (u : ι → (∀ i, A i) → ℝ) : ¬ ∃ σ, IsMixedNash u σ := by
  intro h
  obtain ⟨σ, hmem, _⟩ := h
  obtain ⟨hnn, hsum⟩ := hmem i₀
  have hempty : ∑ a : A i₀, σ i₀ a = 0 := Fintype.sum_empty _
  rw [hempty] at hsum
  exact zero_ne_one hsum

-- Unconditional Nash existence for matching pennies via `exists_isMixedNash`.
example : ∃ σ, IsMixedNash mp σ := by
  exact exists_isMixedNash mp

end MathlibExtTest.GameTheory.MixedNashExistence
