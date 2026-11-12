/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib

namespace StatMech.Onsager.GroundUp












theorem rect_angleSum_iff_balance (c r : ℤ) :
    (90 * c + 270 * r = 180 * (c + r) - 360) ↔ (c - r = 4) := by
  omega




theorem balance_form (c r : ℤ) :
    (c - r = 4 ↔ 90 * (c - r) = 360) ∧ (c - r = -4 ↔ 90 * (c - r) = -360) := by
  omega









noncomputable def convexCount {n : ℕ} (t : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => t i = 1)).card


noncomputable def reflexCount {n : ℕ} (t : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => t i = -1)).card


def turnSum {n : ℕ} (t : Fin n → ℤ) : ℤ := ∑ i, t i



theorem turnSum_eq {n : ℕ} (t : Fin n → ℤ) (h : ∀ i, t i = 1 ∨ t i = -1) :
    turnSum t = (convexCount t : ℤ) - reflexCount t := by
  classical
  unfold turnSum convexCount reflexCount
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => t i = 1) t]
  have hset : Finset.univ.filter (fun i => ¬ t i = 1)
      = Finset.univ.filter (fun i => t i = -1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h i with h1 | h1 <;> rw [h1] <;> decide
  have e1 : ∑ i ∈ Finset.univ.filter (fun i => t i = 1), t i
      = ((Finset.univ.filter (fun i => t i = 1)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2)]
    simp
  have e2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ t i = 1), t i
      = - ((Finset.univ.filter (fun i => t i = -1)).card : ℤ) := by
    rw [hset, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2)]
    simp
  rw [e1, e2]; ring



theorem card_split {n : ℕ} (t : Fin n → ℤ) (h : ∀ i, t i = 1 ∨ t i = -1) :
    convexCount t + reflexCount t = n := by
  classical
  unfold convexCount reflexCount
  have hset : Finset.univ.filter (fun i => t i = -1)
      = Finset.univ.filter (fun i => ¬ t i = 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h i with h1 | h1 <;> rw [h1] <;> decide
  rw [hset, Finset.card_filter_add_card_filter_not]
  simp





















theorem balance_split (c r c₁ r₁ c₂ r₂ : ℤ)
    (hc : c₁ + c₂ = c + 3) (hr : r₁ + r₂ = r - 1) :
    (c - r) = (c₁ - r₁) + (c₂ - r₂) - 4 := by
  omega




theorem balance_of_split (c r c₁ r₁ c₂ r₂ : ℤ)
    (hc : c₁ + c₂ = c + 3) (hr : r₁ + r₂ = r - 1)
    (h₁ : c₁ - r₁ = 4) (h₂ : c₂ - r₂ = 4) :
    c - r = 4 := by
  omega
















structure RectPolygonData where
  
  Poly : Type
  
  size : Poly → ℕ
  
  cc : Poly → ℤ
  
  rc : Poly → ℤ
  
  simple : Poly → Prop
  
  hcc : ∀ P, 0 ≤ cc P
  
  hrc : ∀ P, 0 ≤ rc P
  

  base : ∀ P, simple P → rc P = 0 → cc P = 4
  



  chord : ∀ P, simple P → 0 < rc P →
    ∃ P₁ P₂, simple P₁ ∧ simple P₂ ∧
      size P₁ < size P ∧ size P₂ < size P ∧
      cc P₁ + cc P₂ = cc P + 3 ∧ rc P₁ + rc P₂ = rc P - 1


def RectPolygonData.balance (D : RectPolygonData) (P : D.Poly) : ℤ := D.cc P - D.rc P



theorem RectPolygonData.umlaufsatz_aux (D : RectPolygonData) :
    ∀ n : ℕ, ∀ P : D.Poly, D.size P = n → D.simple P → D.balance P = 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro P hsz hsimple
    by_cases hr : D.rc P = 0
    · 
      have hcc : D.cc P = 4 := D.base P hsimple hr
      unfold RectPolygonData.balance
      omega
    · 
      have hrpos : 0 < D.rc P := lt_of_le_of_ne (D.hrc P) (Ne.symm hr)
      obtain ⟨P₁, P₂, hs₁, hs₂, hlt₁, hlt₂, hcceq, hrceq⟩ := D.chord P hsimple hrpos
      have hb₁ : D.balance P₁ = 4 := IH (D.size P₁) (hsz ▸ hlt₁) P₁ rfl hs₁
      have hb₂ : D.balance P₂ = 4 := IH (D.size P₂) (hsz ▸ hlt₂) P₂ rfl hs₂
      unfold RectPolygonData.balance at hb₁ hb₂ ⊢
      omega






theorem RectPolygonData.umlaufsatz (D : RectPolygonData) (P : D.Poly) (hP : D.simple P) :
    D.balance P = 4 :=
  D.umlaufsatz_aux (D.size P) P rfl hP











noncomputable def staircaseModel : RectPolygonData where
  Poly := ℕ
  size := fun k => k
  cc := fun k => (k : ℤ) + 4
  rc := fun k => (k : ℤ)
  simple := fun _ => True
  hcc := by intro k; positivity
  hrc := by intro k; positivity
  base := by intro k _ h; omega
  chord := by
    intro k _ hk
    
    refine ⟨k - 1, 0, trivial, trivial, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
    · push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring





theorem staircase_balance (k : ℕ) : staircaseModel.balance k = 4 :=
  staircaseModel.umlaufsatz k trivial





























































end StatMech.Onsager.GroundUp
