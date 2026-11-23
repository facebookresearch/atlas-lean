/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_ncard_charpoly_coeff_pair_eq_ncard_symm_pair_
of_finrank_eq_three.lean`
and
`P2M/Sol/S_LanglandsTunnell_ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

@[expose] public section

open Finset

namespace CubicPairCount

section Counting

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def sigma3 (r : F × F × F) : F × F × F :=
  (r.1 + r.2.1 + r.2.2, r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1, r.1 * r.2.1 * r.2.2)

private def mulLin (p : F × F × F) : F × F × F := (p.1 + p.2.1, p.2.2 + p.1 * p.2.1, p.1 * p.2.2)

private def cube (a : F) : F × F × F := (3 * a, 3 * a ^ 2, a ^ 3)

private def IsRoot (e : F × F × F) (a : F) : Prop := a ^ 3 - e.1 * a ^ 2 + e.2.1 * a - e.2.2 = 0

private scoped instance (e : F × F × F) (a : F) : Decidable (IsRoot e a) := by
  unfold IsRoot
  infer_instance

private def rootCount (e : F × F × F) : ℕ := (univ.filter fun a : F => IsRoot e a).card

private def tripleCount (e : F × F × F) : ℕ := (univ.filter fun r : F × F × F => sigma3 r = e).card

private def cubeCount (e : F × F × F) : ℕ := (univ.filter fun a : F => cube a = e).card

private def rootlessCount (e : F × F × F) : ℕ := if rootCount e = 0 then 1 else 0

private theorem card_mulLin_fibre (e : F × F × F) :
    (univ.filter fun p : F × F × F => mulLin p = e).card = rootCount e := by
  unfold rootCount
  refine Finset.card_bij' (fun p _ => p.1) (fun a _ => (a, e.1 - a, e.2.1 - a * (e.1 - a))) ?_ ?_
      ?_ ?_
  · rintro ⟨a, b₁, b₂⟩ hp
    simp only [mem_filter, mem_univ, true_and, mulLin, Prod.ext_iff] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    simp only [mem_filter, mem_univ, true_and]
    show a ^ 3 - e.1 * a ^ 2 + e.2.1 * a - e.2.2 = 0
    rw [← h1, ← h2, ← h3]
    ring
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    have ha' : a ^ 3 - e.1 * a ^ 2 + e.2.1 * a - e.2.2 = 0 := ha
    simp only [mem_filter, mem_univ, true_and, mulLin, Prod.ext_iff]
    refine ⟨by ring, by ring, ?_⟩
    linear_combination ha'
  · rintro ⟨a, b₁, b₂⟩ hp
    simp only [mem_filter, mem_univ, true_and, mulLin, Prod.ext_iff] at hp
    obtain ⟨h1, h2, -⟩ := hp
    simp only [Prod.ext_iff]
    refine ⟨by first | trivial | rfl, ?_, ?_⟩
    · rw [← h1]; ring
    · rw [← h2, ← h1]; ring
  · intro a _
    rfl

private theorem isRoot_of_sigma3 {r e : F × F × F} (h : sigma3 r = e) : IsRoot e r.1 := by
  obtain ⟨α, β, γ⟩ := r
  simp only [sigma3, Prod.ext_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  show IsRoot e α
  unfold IsRoot
  rw [← h1, ← h2, ← h3]
  ring

private theorem eq_of_isRoot_of_cube_eq {a b : F} {e : F × F × F} (h : cube a = e) (hb : IsRoot e
    b) : b = a := by
  subst h
  unfold IsRoot cube at hb
  simp only at hb
  have h3 : (b - a) ^ 3 = 0 := by linear_combination hb
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h3)

private theorem isRoot_cube_self (a : F) : IsRoot (cube a) a := by
  unfold IsRoot cube
  simp only
  ring

private theorem card_quadratic_roots_le_two
    (b : F × F) : (univ.filter fun x : F => x ^ 2 - b.1 * x + b.2 = 0).card ≤ 2 := by
  by_cases h : ∃ β : F, β ^ 2 - b.1 * β + b.2 = 0
  · obtain ⟨β, hβ⟩ := h
    calc (univ.filter fun x : F => x ^ 2 - b.1 * x + b.2 = 0).card ≤ ({β, b.1 - β} : Finset
        F).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          simp only [mem_insert, mem_singleton]
          have : (x - β) * (x - (b.1 - β)) = 0 := by linear_combination hx - hβ
          rcases mul_eq_zero.mp this with h1 | h1
          · exact Or.inl (sub_eq_zero.mp h1)
          · exact Or.inr (sub_eq_zero.mp h1)
      _ ≤ 2 := Finset.card_le_two
  · rw [Finset.filter_eq_empty_iff.mpr fun x _ hx => h ⟨x, hx⟩]
    simp

private def cofactor (e : F × F × F) (a : F) : F × F := (e.1 - a, e.2.1 - a * (e.1 - a))

private theorem mulLin_cofactor {e : F × F × F} {a : F} (ha : IsRoot e a) : mulLin (a, cofactor e
    a) = e := by
  unfold IsRoot at ha
  simp only [mulLin, cofactor, Prod.ext_iff]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination ha

private theorem isRoot_iff_of_isRoot {e : F × F × F} {a : F} (ha : IsRoot e a) (b : F) :
    IsRoot e b ↔ b = a ∨ b ^ 2 - (cofactor e a).1 * b + (cofactor e a).2 = 0 := by
  rw [← mulLin_cofactor ha]
  simp only [IsRoot, mulLin, cofactor]
  constructor
  · intro h
    have : (b - a) * (b ^ 2 - (e.1 - a) * b + (e.2.1 - a * (e.1 - a))) = 0 := by
        linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (by linear_combination h1)
  · rintro (rfl | h)
    · ring
    · linear_combination (b - a) * h

private theorem sigma3_eq_iff {e : F × F × F} (α β γ : F) :
    sigma3 (α, β, γ) = e ↔ IsRoot e α ∧ β + γ = (cofactor e α).1 ∧ β * γ = (cofactor e α).2 := by
  simp only [sigma3, cofactor, Prod.ext_iff, IsRoot]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← h1, ← h2, ← h3]; ring
    · rw [← h1]; ring
    · rw [← h1, ← h2]; ring
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2 + α * h1
    · linear_combination α * h2 + h0

private theorem tripleCount_eq_sum (e : F × F × F) :
    tripleCount e = ∑ α ∈ univ.filter (fun α : F => IsRoot e α),
      (univ.filter fun β : F => β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0).card := by
  unfold tripleCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun α _ => ?_
  by_cases hα : IsRoot e α
  · rw [if_pos hα, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine sum_congr rfl fun β _ => ?_
    by_cases hβ : β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0
    · rw [if_pos hβ]
      rw [Finset.sum_eq_single ((cofactor e α).1 - β)]
      · rw [if_pos]
        rw [sigma3_eq_iff]
        exact ⟨hα, by ring, by linear_combination -hβ⟩
      · intro γ _ hγ
        rw [if_neg]
        rw [sigma3_eq_iff]
        rintro ⟨-, h1, -⟩
        exact hγ (by linear_combination h1)
      · intro h; exact absurd (mem_univ _) h
    · rw [if_neg hβ]
      refine Finset.sum_eq_zero fun γ _ => ?_
      rw [if_neg]
      rw [sigma3_eq_iff]
      rintro ⟨-, h1, h2⟩
      exact hβ (by linear_combination -h2 + β * h1)
  · rw [if_neg hα]
    refine Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun γ _ => ?_
    rw [if_neg]
    rw [sigma3_eq_iff]
    exact fun h => hα h.1

private theorem card_cofactor_roots {e : F × F × F} {α : F} (hα : IsRoot e α) :
    (univ.filter fun β : F => β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0).card
      = rootCount e - 1 + (if α ^ 2 - (cofactor e α).1 * α + (cofactor e α).2 = 0 then 1 else 0)
          := by
  have hroots : (univ.filter fun a : F => IsRoot e a)
      = insert α (univ.filter fun β : F => β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0) :=
          by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    exact isRoot_iff_of_isRoot hα b
  unfold rootCount
  rw [hroots, Finset.card_insert_eq_ite]
  by_cases hm : α ^ 2 - (cofactor e α).1 * α + (cofactor e α).2 = 0
  · rw [if_pos hm, if_pos (by simpa using hm)]
    have : 0 < (univ.filter fun β : F => β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0).card
        :=
      Finset.card_pos.mpr ⟨α, by simpa using hm⟩
    omega
  · rw [if_neg hm, if_neg (by simpa using hm)]
    omega

private theorem tripleCount_eq (e : F × F × F) :
    tripleCount e = rootCount e * (rootCount e - 1)
      + (univ.filter fun α : F => IsRoot e α ∧ α ^ 2 - (cofactor e α).1 * α + (cofactor e α).2 =
          0).card := by
  rw [tripleCount_eq_sum]
  rw [Finset.sum_congr rfl fun α hα => card_cofactor_roots (mem_filter.mp hα).2]
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole, Nat.cast_id,
      Finset.filter_filter]
  rfl

private theorem rootCount_le_three (e : F × F × F) : rootCount e ≤ 3 := by
  unfold rootCount
  by_cases h : ∃ α : F, IsRoot e α
  · obtain ⟨α, hα⟩ := h
    calc (univ.filter fun a : F => IsRoot e a).card
        ≤ (insert α (univ.filter fun β : F => β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 =
            0)).card := by
          apply Finset.card_le_card
          intro b hb
          simp only [mem_filter, mem_univ, true_and] at hb
          simp only [mem_insert, mem_filter, mem_univ, true_and]
          exact (isRoot_iff_of_isRoot hα b).mp hb
      _ ≤ (univ.filter fun β : F => β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ 2 + 1 := by have := card_quadratic_roots_le_two (cofactor e α); omega
  · rw [Finset.filter_eq_empty_iff.mpr fun a _ ha => h ⟨a, ha⟩]
    simp

private theorem isRoot_sigma3_iff (α β γ x : F) : IsRoot (sigma3 (α, β, γ)) x ↔ x = α ∨ x = β ∨ x
    = γ := by
  unfold IsRoot sigma3
  simp only
  constructor
  · intro h
    have : (x - α) * ((x - β) * (x - γ)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h2))
  · rintro (rfl | rfl | rfl) <;> ring

private theorem mult_sigma3 (α β γ : F) :
    α ^ 2 - (cofactor (sigma3 (α, β, γ)) α).1 * α + (cofactor (sigma3 (α, β, γ)) α).2 = (α - β) *
        (α - γ) := by
  unfold cofactor sigma3
  simp only
  ring

private theorem sigma3_swap_left (α β γ : F) : sigma3 (β, α, γ) = sigma3 (α, β, γ) := by
  unfold sigma3; simp only [Prod.ext_iff]; refine ⟨by ring, by ring, by ring⟩

private theorem sigma3_rotate (α β γ : F) : sigma3 (γ, α, β) = sigma3 (α, β, γ) := by
  unfold sigma3; simp only [Prod.ext_iff]; refine ⟨by ring, by ring, by ring⟩

private theorem mult_sigma3_iff (α β γ x : F) (hx : x = α ∨ x = β ∨ x = γ) :
    x ^ 2 - (cofactor (sigma3 (α, β, γ)) x).1 * x + (cofactor (sigma3 (α, β, γ)) x).2 = 0 ↔
      (x = α ∧ (α = β ∨ α = γ)) ∨ (x = β ∧ (β = α ∨ β = γ)) ∨ (x = γ ∧ (γ = α ∨ γ = β)) := by
  rcases hx with rfl | rfl | rfl
  · rw [mult_sigma3, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    constructor
    · intro h; exact Or.inl ⟨rfl, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact h
      · exact Or.inl h
      · exact Or.inr h
  · rw [← sigma3_swap_left, mult_sigma3, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
    · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact h
      · exact Or.inr h
  · rw [← sigma3_rotate, mult_sigma3, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨rfl, h⟩)
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact h

private theorem cubeCount_sigma3_of_eq (α : F) : cubeCount (sigma3 (α, α, α)) = 1 := by
  have h : cube α = sigma3 (α, α, α) := by
    unfold cube sigma3; simp only [Prod.ext_iff]; refine ⟨by ring, by ring, by ring⟩
  have hroot : IsRoot (sigma3 (α, α, α)) α := (isRoot_sigma3_iff α α α α).mpr (Or.inl rfl)
  unfold cubeCount
  rw [Finset.card_eq_one]
  refine ⟨α, ?_⟩
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro ha
    exact (eq_of_isRoot_of_cube_eq ha hroot).symm
  · rintro rfl
    exact h

private theorem card_multiple_roots_sigma3 (α β γ : F) :
    (univ.filter fun x : F => IsRoot (sigma3 (α, β, γ)) x ∧
        x ^ 2 - (cofactor (sigma3 (α, β, γ)) x).1 * x + (cofactor (sigma3 (α, β, γ)) x).2 = 0).card
      = if rootCount (sigma3 (α, β, γ)) = 2 then 1 else cubeCount (sigma3 (α, β, γ)) := by
  have hroots : (univ.filter fun x : F => IsRoot (sigma3 (α, β, γ)) x) = {α, β, γ} := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]; exact
        isRoot_sigma3_iff α β γ x
  have hmult : (univ.filter fun x : F => IsRoot (sigma3 (α, β, γ)) x ∧
      x ^ 2 - (cofactor (sigma3 (α, β, γ)) x).1 * x + (cofactor (sigma3 (α, β, γ)) x).2 = 0)
      = ({α, β, γ} : Finset F).filter fun x => (x = α ∧ (α = β ∨ α = γ)) ∨ (x = β ∧ (β = α ∨ β =
          γ)) ∨
          (x = γ ∧ (γ = α ∨ γ = β)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, isRoot_sigma3_iff]
    constructor
    · rintro ⟨hx, hd⟩; exact ⟨hx, (mult_sigma3_iff α β γ x hx).mp hd⟩
    · rintro ⟨hx, hd⟩; exact ⟨hx, (mult_sigma3_iff α β γ x hx).mpr hd⟩
  unfold rootCount
  rw [hroots, hmult]
  clear hmult hroots
  by_cases hαβ : α = β
  · subst hαβ
    by_cases hαγ : α = γ
    · subst hαγ
      simp [cubeCount_sigma3_of_eq, Finset.filter_singleton]
    · have hγα : ¬γ = α := fun h => hαγ h.symm
      rw [if_pos (by simp [Finset.card_pair hαγ])]
      rw [Finset.card_eq_one]
      exact ⟨α, by ext x; simp only [mem_filter, mem_insert, mem_singleton]; first | tauto | aesop⟩
  · have hβα : ¬β = α := fun h => hαβ h.symm
    by_cases hαγ : α = γ
    · subst hαγ
      rw [if_pos (by simp [Finset.card_pair hαβ, Finset.card_pair (Ne.symm hαβ)])]
      rw [Finset.card_eq_one]
      exact ⟨α, by ext x; simp only [mem_filter, mem_insert, mem_singleton]; first | tauto | aesop⟩
    · have hγα : ¬γ = α := fun h => hαγ h.symm
      by_cases hβγ : β = γ
      · subst hβγ
        rw [if_pos (by simp [Finset.card_pair hαβ])]
        rw [Finset.card_eq_one]
        exact ⟨β, by ext x; simp only [mem_filter, mem_insert, mem_singleton]; first | tauto |
            aesop⟩
      · have hγβ : ¬γ = β := fun h => hβγ h.symm
        have h3 : ({α, β, γ} : Finset F).card = 3 := Finset.card_eq_three.mpr ⟨α, β, γ, hαβ, hαγ,
            hβγ, rfl⟩
        rw [if_neg (by omega)]
        have hcc : cubeCount (sigma3 (α, β, γ)) = 0 := by
          unfold cubeCount
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro a _ ha
          have h1 : α = a := eq_of_isRoot_of_cube_eq ha ((isRoot_sigma3_iff α β γ α).mpr (Or.inl
              rfl))
          have h2 : β = a := eq_of_isRoot_of_cube_eq ha ((isRoot_sigma3_iff α β γ β).mpr (Or.inr
              (Or.inl rfl)))
          exact hαβ (h1.trans h2.symm)
        rw [hcc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ hx
        first | tauto | aesop

private theorem card_multiple_roots (e : F × F × F) :
    (univ.filter fun α : F => IsRoot e α ∧ α ^ 2 - (cofactor e α).1 * α + (cofactor e α).2 = 0).card
      = if rootCount e = 2 then 1 else cubeCount e := by
  by_cases hex : ∃ α : F, IsRoot e α
  · obtain ⟨α, hα⟩ := hex
    by_cases hq : ∃ β : F, β ^ 2 - (cofactor e α).1 * β + (cofactor e α).2 = 0
    · obtain ⟨β, hβ⟩ := hq
      have he : sigma3 (α, β, (cofactor e α).1 - β) = e :=
        (sigma3_eq_iff α β _).mpr ⟨hα, by ring, by linear_combination -hβ⟩
      rw [← he]
      exact card_multiple_roots_sigma3 α β _
    · have hroots : (univ.filter fun a : F => IsRoot e a) = {α} := by
        ext b
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        rw [isRoot_iff_of_isRoot hα]
        exact ⟨fun h => h.elim id fun h' => absurd ⟨b, h'⟩ hq, fun h => Or.inl h⟩
      have hrc : rootCount e = 1 := by unfold rootCount; rw [hroots]; rfl
      have hcc : cubeCount e = 0 := by
        unfold cubeCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c _ hc
        have hcα : α = c := eq_of_isRoot_of_cube_eq hc hα
        subst hcα
        apply hq
        refine ⟨α, ?_⟩
        rw [← hc]
        unfold cofactor cube
        simp only
        ring
      rw [hrc, if_neg (by omega), hcc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨hx, hd⟩
      have hxα : x = α := by
        have := (mem_filter.mp (show x ∈ univ.filter fun a : F => IsRoot e a from by simp [hx])).2
        have hm : x ∈ ({α} : Finset F) := hroots ▸ (by simp [hx])
        exact mem_singleton.mp hm
      subst hxα
      exact hq ⟨x, hd⟩
  · have hrc : rootCount e = 0 := by
      unfold rootCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun a _ ha => hex ⟨a, ha⟩
    have hcc : cubeCount e = 0 := by
      unfold cubeCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro c _ hc
      apply hex
      refine ⟨c, ?_⟩
      rw [← hc]
      unfold IsRoot cube
      simp only
      ring
    rw [hrc, if_neg (by omega), hcc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨hx, -⟩
    exact hex ⟨x, hx⟩

private theorem cubeCount_le_one (e : F × F × F) : cubeCount e ≤ 1 := by
  unfold cubeCount
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact eq_of_isRoot_of_cube_eq hb (ha ▸ isRoot_cube_self a)

private theorem rootCount_eq_one_of_cubeCount {e : F × F × F} (h : cubeCount e = 1) : rootCount e
    = 1 := by
  unfold cubeCount at h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (univ.filter fun a : F => cube a = e).card)
  simp only [mem_filter, mem_univ, true_and] at ha
  unfold rootCount
  rw [Finset.card_eq_one]
  refine ⟨a, Finset.ext fun b => ?_⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun hb => eq_of_isRoot_of_cube_eq ha hb, fun hb => hb ▸ ha ▸ isRoot_cube_self a⟩

private theorem cubeCount_eq_zero_of_rootCount_eq_zero {e : F × F × F} (h : rootCount e = 0) :
    cubeCount e = 0 := by
  have hno : ∀ a : F, ¬ IsRoot e a := by
    intro a ha
    have := Finset.card_pos.mpr ⟨a, (mem_filter.mpr ⟨mem_univ a, ha⟩ : a ∈ univ.filter fun a : F
        => IsRoot e a)⟩
    unfold rootCount at h
    omega
  unfold cubeCount
  have hempty : (univ.filter fun a : F => cube a = e) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun a _ (ha : cube a = e) => hno a (ha ▸ isRoot_cube_self a)
  rw [hempty, Finset.card_empty]

private theorem count_identity (e : F × F × F) :
    3 * rootlessCount e + cubeCount e + 3 * rootCount e = tripleCount e + 3 := by
  rw [tripleCount_eq, card_multiple_roots]
  unfold rootlessCount
  have h3 := rootCount_le_three e
  have hc := cubeCount_le_one e
  rcases Nat.lt_or_ge (rootCount e) 4 with h | h
  · interval_cases hr : rootCount e
    · rw [cubeCount_eq_zero_of_rootCount_eq_zero hr]; simp
    · simp
    · have : cubeCount e = 0 := by
        by_contra hne
        have h1 : cubeCount e = 1 := by omega
        have := rootCount_eq_one_of_cubeCount h1
        omega
      simp [this]
    · have : cubeCount e = 0 := by
        by_contra hne
        have h1 : cubeCount e = 1 := by omega
        have := rootCount_eq_one_of_cubeCount h1
        omega
      simp [this]
  · omega

variable {R : Type*} [CommSemiring R]

private theorem sum_card_fibre_mul {α : Type*} [Fintype α] (φ : α → F × F × F) (W : F × F × F → R) :
    ∑ e : F × F × F, (((univ.filter fun x : α => φ x = e).card : ℕ) : R) * W e = ∑ x : α, W (φ x)
        := by
  rw [← Finset.sum_fiberwise univ φ (fun x => W (φ x))]
  refine sum_congr rfl fun e _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => W e) (fun x hx => by rw [(mem_filter.mp hx).2]),
      sum_const, nsmul_eq_mul]

private theorem weighted_identity (W : F × F × F → R) :
    ∑ e : F × F × F, ((3 * rootlessCount e + cubeCount e : ℕ) : R) * W e + 3 * ∑ p : F × F × F, W
        (mulLin p)
      = ∑ r : F × F × F, W (sigma3 r) + 3 * ∑ e : F × F × F, W e := by
  rw [← sum_card_fibre_mul mulLin W, ← sum_card_fibre_mul sigma3 W]
  simp only [card_mulLin_fibre]
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  have h : (3 * (rootlessCount e : R) + cubeCount e + 3 * rootCount e) = (tripleCount e : R) + 3
      := by
    have h1 : ((3 * rootlessCount e + cubeCount e + 3 * rootCount e : ℕ) : R) = ((tripleCount e +
        3 : ℕ) : R) := by
      rw [count_identity e]
    push_cast at h1
    exact h1
  push_cast
  calc (3 * (rootlessCount e : R) + cubeCount e) * W e + 3 * ((rootCount e : R) * W e)
      = (3 * (rootlessCount e : R) + cubeCount e + 3 * rootCount e) * W e := by ring
    _ = ((tripleCount e : R) + 3) * W e := by rw [h]
    _ = ((univ.filter fun r : F × F × F => sigma3 r = e).card : R) * W e + 3 * W e := by
        unfold tripleCount; ring

end Counting

section FieldSide

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {F' : Type*} [Field F'] [Algebra F F']
    [Fintype F']
  [DecidableEq F'] [Module.Finite F F']

private noncomputable def elemTriple (F : Type*) [Field F] {F' : Type*} [Field F'] [Algebra F F']
    [Module.Finite F F']
    (y : F') : F × F × F :=
  (-(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 2, (LinearMap.charpoly (Algebra.lmul F F'
      y)).coeff 1,
    -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 0)

private theorem elemTriple_fst
    (h3 : Module.finrank F F' = 3) (y : F') : (elemTriple F y).1 = Algebra.trace F F' y := by
  let b := Module.finBasis F F'
  haveI : Nonempty (Fin (Module.finrank F F')) := ⟨⟨0, by omega⟩⟩
  have hcard : Fintype.card (Fin (Module.finrank F F')) - 1 = 2 := by simp [h3]
  simp only [elemTriple]
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_coeff,
    LinearMap.charpoly_toMatrix, hcard]

private theorem elemTriple_last (h3 : Module.finrank F F' = 3) (y : F') : (elemTriple F y).2.2 =
    Algebra.norm F y := by
  let b := Module.finBasis F F'
  have hcard : Fintype.card (Fin (Module.finrank F F')) = 3 := by simp [h3]
  simp only [elemTriple]
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff,
      LinearMap.charpoly_toMatrix,
    hcard]
  ring

private theorem elemTriple_snd
    (y : F') : (elemTriple F y).2.1 = (LinearMap.charpoly (Algebra.lmul F F' y)).coeff 1 := rfl

private theorem eval_eq_of_natDegree_eq_three {p : Polynomial F} (hp : p.Monic) (hdeg :
    p.natDegree = 3) (a : F) :
    p.eval a = a ^ 3 + p.coeff 2 * a ^ 2 + p.coeff 1 * a + p.coeff 0 := by
  have hlead : p.coeff 3 = 1 := by
    have h := hp.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at h
  rw [Polynomial.eval_eq_sum_range, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlead]
  ring

private theorem rootCount_elemTriple_eq_zero (h3 : Module.finrank F F' = 3) {y : F'}
    (hy : ¬ ∃ a : F, algebraMap F F' a = y) : rootCount (elemTriple F y) = 0 := by
  rw [rootCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have hpmonic : (Algebra.lmul F F' y).charpoly.Monic := LinearMap.charpoly_monic _
  have hpdeg : (Algebra.lmul F F' y).charpoly.natDegree = 3 := by rw
      [LinearMap.charpoly_natDegree, h3]

  have hroot : (Algebra.lmul F F' y).charpoly.IsRoot a := by
    rw [Polynomial.IsRoot, eval_eq_of_natDegree_eq_three hpmonic hpdeg]
    simp only [IsRoot, elemTriple] at ha
    linear_combination ha

  have hint : IsIntegral F y := IsIntegral.of_finite (R := F) y
  have hmin_deg : (minpoly F y).natDegree = 3 := by
    have hdvd : (minpoly F y).natDegree ∣ 3 := h3 ▸ minpoly.degree_dvd hint
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact absurd (minpoly.natDegree_eq_one_iff.mp h1) (fun h => hy (RingHom.mem_range.mp h))
    · exact h3'
  have hmin_eq : minpoly F y = (Algebra.lmul F F' y).charpoly :=
    Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff (minpoly.dvd F y
        (Algebra.aeval_self_charpoly_lmul y))
      (by rw [hpdeg, hmin_deg]) (by rw [(minpoly.monic hint).leadingCoeff, hpmonic.leadingCoeff])

  have hroot' : (minpoly F y).IsRoot a := by rw [hmin_eq]; exact hroot
  have : (minpoly F y).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some <|
      Polynomial.degree_eq_one_of_irreducible_of_root (minpoly.irreducible hint) hroot'
  omega

private noncomputable def cubicPoly (e : F × F × F) : Polynomial F :=
  Polynomial.X ^ 3 - Polynomial.C e.1 * Polynomial.X ^ 2 + Polynomial.C e.2.1 * Polynomial.X -
      Polynomial.C e.2.2

private theorem cubicPoly_coeff_three (e : F × F × F) : (cubicPoly e).coeff 3 = 1 := by
  simp [cubicPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]

private theorem cubicPoly_coeff_two (e : F × F × F) : (cubicPoly e).coeff 2 = -e.1 := by
  simp [cubicPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]

private theorem cubicPoly_coeff_one (e : F × F × F) : (cubicPoly e).coeff 1 = e.2.1 := by
  simp [cubicPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]

private theorem cubicPoly_coeff_zero (e : F × F × F) : (cubicPoly e).coeff 0 = -e.2.2 := by
  simp [cubicPoly, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C]

private theorem cubicPoly_ne_zero (e : F × F × F) : cubicPoly e ≠ 0 := by
  intro h
  have h3 := cubicPoly_coeff_three e
  rw [h, Polynomial.coeff_zero] at h3
  exact zero_ne_one h3

private theorem cubicPoly_natDegree_le (e : F × F × F) : (cubicPoly e).natDegree ≤ 3 := by
  unfold cubicPoly
  compute_degree

private theorem charpoly_eq_cubicPoly (h3 : Module.finrank F F' = 3) (y : F') :
    LinearMap.charpoly (Algebra.lmul F F' y) = cubicPoly (elemTriple F y) := by
  have hdeg : (LinearMap.charpoly (Algebra.lmul F F' y)).natDegree = 3 := by
    rw [LinearMap.charpoly_natDegree, h3]
  have hlead : (LinearMap.charpoly (Algebra.lmul F F' y)).coeff 3 = 1 := by
    have h := (LinearMap.charpoly_monic (Algebra.lmul F F' y)).leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at h
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow (LinearMap.charpoly (Algebra.lmul F F' y)),
      hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlead, cubicPoly, elemTriple, map_neg,
      map_one]
  ring

private theorem elemTriple_eq_iff (h3 : Module.finrank F F' = 3) (y : F') (e : F × F × F) :
    elemTriple F y = e ↔ LinearMap.charpoly (Algebra.lmul F F' y) = cubicPoly e := by
  constructor
  · rintro rfl
    exact charpoly_eq_cubicPoly h3 y
  · intro h
    have h2 := congrArg (fun q : Polynomial F => q.coeff 2) h
    have h1 := congrArg (fun q : Polynomial F => q.coeff 1) h
    have h0 := congrArg (fun q : Polynomial F => q.coeff 0) h
    simp only [cubicPoly_coeff_two, cubicPoly_coeff_one, cubicPoly_coeff_zero] at h2 h1 h0
    unfold elemTriple
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · show -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 2 = e.1
      rw [h2, neg_neg]
    · exact h1
    · show -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 0 = e.2.2
      rw [h0, neg_neg]

private theorem elemTriple_algebraMap (h3 : Module.finrank F F' = 3) (a : F) :
    elemTriple F (algebraMap F F' a) = cube a := by
  have hl : Algebra.lmul F F' (algebraMap F F' a) = a • (LinearMap.id : F' →ₗ[F] F') := by
    ext x
    simp [Algebra.smul_def]
  rw [elemTriple_eq_iff h3, hl, ← LinearMap.charpoly_toMatrix _ (Module.finBasis F F'), map_smul,
    LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, h3, cubicPoly, cube, map_mul,
      map_pow,
    map_ofNat]
  ring

private theorem card_elemTriple_fibre_le_three (h3 : Module.finrank F F' = 3) (e : F × F × F) :
    (univ.filter fun y : F' => elemTriple F y = e).card ≤ 3 := by
  calc (univ.filter fun y : F' => elemTriple F y = e).card
      ≤ ((cubicPoly e).map (algebraMap F F')).roots.toFinset.card := by
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Multiset.mem_toFinset, Polynomial.mem_roots_map (cubicPoly_ne_zero e), ←
            Polynomial.aeval_def,
          ← (elemTriple_eq_iff h3 y e).mp hy.2]
        exact Algebra.aeval_self_charpoly_lmul y
    _ ≤ Multiset.card ((cubicPoly e).map (algebraMap F F')).roots := Multiset.toFinset_card_le _
    _ ≤ ((cubicPoly e).map (algebraMap F F')).natDegree := Polynomial.card_roots' _
    _ ≤ (cubicPoly e).natDegree := Polynomial.natDegree_map_le
    _ ≤ 3 := cubicPoly_natDegree_le e

private theorem card_elemTriple_fibre_le_cubeCount (h3 : Module.finrank F F' = 3) {e : F × F × F}
    (he : rootCount e ≠ 0) : (univ.filter fun y : F' => elemTriple F y = e).card ≤ cubeCount e := by
  unfold cubeCount
  rw [← Finset.card_image_of_injective (univ.filter fun a : F => cube a = e) (algebraMap F
      F').injective]
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy
  obtain ⟨a, rfl⟩ : ∃ a : F, algebraMap F F' a = y := by
    by_contra hne
    apply he
    rw [← hy.2]
    exact rootCount_elemTriple_eq_zero h3 hne
  rw [Finset.mem_image]
  refine ⟨a, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ a, by rw [← elemTriple_algebraMap h3 a]; exact hy.2⟩

private theorem card_elemTriple_fibre_le (h3 : Module.finrank F F' = 3) (e : F × F × F) :
    (univ.filter fun y : F' => elemTriple F y = e).card ≤ 3 * rootlessCount e + cubeCount e := by
  unfold rootlessCount
  split_ifs with he
  · have h := card_elemTriple_fibre_le_three h3 e
    omega
  · have h := card_elemTriple_fibre_le_cubeCount h3 he
    omega

private theorem sum_card_elemTriple_fibre (h3 : Module.finrank F F' = 3) :
    ∑ e : F × F × F, (univ.filter fun y : F' => elemTriple F y = e).card = Fintype.card F ^ 3 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := elemTriple F) (s := (univ : Finset F'))
    (t := (univ : Finset (F × F × F))) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Module.card_eq_pow_finrank (K := F) (V := F'), h3] at h
  exact h.symm

private theorem sum_three_mul_rootlessCount_add_cubeCount :
    ∑ e : F × F × F, (3 * rootlessCount e + cubeCount e) = Fintype.card F ^ 3 := by
  have h := weighted_identity (R := ℕ) (fun _ : F × F × F => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul,
      Nat.cast_id] at h
  have hq : Fintype.card F ^ 3 = Fintype.card F * (Fintype.card F * Fintype.card F) := by ring
  rw [hq]
  linarith

private theorem card_elemTriple_fibre (h3 : Module.finrank F F' = 3) (e : F × F × F) :
    (univ.filter fun y : F' => elemTriple F y = e).card = 3 * rootlessCount e + cubeCount e := by
  have hle : ∀ e' ∈ (univ : Finset (F × F × F)),
      (univ.filter fun y : F' => elemTriple F y = e').card ≤ 3 * rootlessCount e' + cubeCount e' :=
    fun e' _ => card_elemTriple_fibre_le h3 e'
  have hsum : ∑ e' : F × F × F, (univ.filter fun y : F' => elemTriple F y = e').card
      = ∑ e' : F × F × F, (3 * rootlessCount e' + cubeCount e') := by
    rw [sum_card_elemTriple_fibre h3, sum_three_mul_rootlessCount_add_cubeCount]
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum e (Finset.mem_univ e)

variable {R : Type*} [CommSemiring R]

private theorem sum_elemTriple (h3 : Module.finrank F F' = 3) (W : F × F × F → R) :
    ∑ y : F', W (elemTriple F y) = ∑ e : F × F × F, ((3 * rootlessCount e + cubeCount e : ℕ) : R)
        * W e := by
  rw [← sum_card_fibre_mul (elemTriple F) W]
  simp only [card_elemTriple_fibre h3]

private theorem card_mulLin_pair (t s : F) :
    (univ.filter fun p : F × F × F => (mulLin p).1 = t ∧ (mulLin p).2.1 = s).card = Fintype.card F
        := by
  rw [← Finset.card_univ]
  refine Finset.card_bij' (fun p _ => p.1) (fun a _ => (a, t - a, s - a * (t - a))) ?_ ?_ ?_ ?_
  · intro p _; exact mem_univ _
  · intro a _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      show a + (t - a) = t; ring, by
      show s - a * (t - a) + a * (t - a) = s; ring⟩
  · rintro ⟨a, b₁, b₂⟩ hp
    rw [Finset.mem_filter] at hp
    obtain ⟨h1, h2⟩ := hp.2
    change a + b₁ = t at h1
    change b₂ + a * b₁ = s at h2
    simp only [Prod.ext_iff]
    refine ⟨by first | trivial | rfl, ?_, ?_⟩
    · rw [← h1]; ring
    · rw [← h2, ← h1]; ring
  · intro a _; rfl

private theorem card_pair
    (t s : F) : (univ.filter fun e : F × F × F => e.1 = t ∧ e.2.1 = s).card = Fintype.card F := by
  rw [← Finset.card_univ]
  refine Finset.card_bij' (fun e _ => e.2.2) (fun n _ => (t, s, n)) ?_ ?_ ?_ ?_
  · intro e _; exact mem_univ _
  · intro n _; simp
  · rintro ⟨e₁, e₂, e₃⟩ he
    simp only [mem_filter, mem_univ, true_and] at he
    simp only [Prod.ext_iff]
    exact ⟨he.1.symm, he.2.symm, trivial⟩
  · intro n _; rfl

private theorem card_elemTriple_pair_eq_card_sigma3_pair (h3 : Module.finrank F F' = 3) (t s : F) :
    (univ.filter fun y : F' => (elemTriple F y).1 = t ∧ (elemTriple F y).2.1 = s).card
      = (univ.filter fun r : F × F × F => (sigma3 r).1 = t ∧ (sigma3 r).2.1 = s).card := by
  have h := weighted_identity (R := ℕ) (fun e : F × F × F => if e.1 = t ∧ e.2.1 = s then 1 else 0)
  have hy := sum_elemTriple h3 (fun e : F × F × F => if e.1 = t ∧ e.2.1 = s then (1 : ℕ) else 0)
  simp only [Nat.cast_id] at h hy
  rw [Finset.sum_boole, Finset.sum_boole, Finset.sum_boole] at h
  rw [Finset.sum_boole] at hy
  simp only [Nat.cast_id, card_mulLin_pair, card_pair] at h hy
  rw [hy]
  omega

end FieldSide

end CubicPairCount

/-- In a cubic extension `F'` of a finite field `F`, the elements of `F'`
whose characteristic polynomial has prescribed coefficients (the negated
coefficient of `X ^ 2` equal to `t` and the coefficient of `X` equal to `s`)
are counted by the ordered triples in `F ^ 3` whose first two elementary
symmetric polynomials take the values `t` and `s`. -/
theorem ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three
    (F : Type*) [Field F] [Fintype F] (F' : Type*) [Field F'] [Algebra F F'] [Fintype F']
    (h3 : Module.finrank F F' = 3) (t s : F) :
    {y : F' | -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 2 = t ∧
        (LinearMap.charpoly (Algebra.lmul F F' y)).coeff 1 = s}.ncard
      = {r : F × F × F | r.1 + r.2.1 + r.2.2 = t ∧ r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1 =
          s}.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_setOf]
  convert CubicPairCount.card_elemTriple_pair_eq_card_sigma3_pair (F := F) (F' := F') h3 t s using 2
  rfl
  rfl
