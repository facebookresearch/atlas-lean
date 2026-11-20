/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Mathlib

namespace StatMech.Onsager.PolygonWalk


abbrev Pt := ℤ × ℤ


def cross (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1


def isUnitDir (d : Pt) : Prop := d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)



theorem cross_unit_mem (a b : Pt) (ha : isUnitDir a) (hb : isUnitDir b) :
    cross a b = -1 ∨ cross a b = 0 ∨ cross a b = 1 := by
  rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;>
    subst h <;> subst h' <;> simp only [cross] <;> norm_num


theorem cross_swap (a b : Pt) : cross b a = - cross a b := by
  simp only [cross]; ring


theorem cross_self (a : Pt) : cross a a = 0 := by simp only [cross]; ring





theorem balance_split (c r c₁ r₁ c₂ r₂ : ℤ)
    (hc : c₁ + c₂ = c + 3) (hr : r₁ + r₂ = r - 1) :
    (c - r) = (c₁ - r₁) + (c₂ - r₂) - 4 := by omega



def cornerBalance {n : ℕ} (t : Fin n → ℤ) : ℤ := ∑ i, t i



theorem cornerBalance_eq_count {n : ℕ} (t : Fin n → ℤ)
    (h : ∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) [DecidablePred fun i => t i = 1]
    [DecidablePred fun i => t i = -1] :
    cornerBalance t
      = ((Finset.univ.filter fun i => t i = 1).card : ℤ)
        - ((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
  classical
  unfold cornerBalance
  
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => t i = 1)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i => ¬ t i = 1)
        (fun i => t i = -1)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => t i = 1), t i
      = ((Finset.univ.filter fun i => t i = 1).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    simp
  have h2 : ∑ i ∈ (Finset.univ.filter (fun i => ¬ t i = 1)).filter (fun i => t i = -1), t i
      = - ((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    have : (Finset.univ.filter (fun i => ¬ t i = 1)).filter (fun i => t i = -1)
        = Finset.univ.filter (fun i => t i = -1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun ⟨_, h⟩ => h
      · intro h; exact ⟨by omega, h⟩
    rw [this]; simp
  have h3 : ∑ i ∈ (Finset.univ.filter (fun i => ¬ t i = 1)).filter (fun i => ¬ t i = -1), t i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter, Finset.mem_filter] at hi
    rcases h i with h' | h' | h' <;> simp_all
  rw [h1, h2, h3]; ring


def dirCode (d : Pt) : ZMod 4 :=
  if d = (1, 0) then 0 else if d = (0, 1) then 1 else if d = (-1, 0) then 2 else 3



theorem cross_congr_dirCode (a b : Pt) (ha : isUnitDir a) (hb : isUnitDir b)
    (hnu : b ≠ (-a.1, -a.2)) :
    ((cross a b : ℤ) : ZMod 4) = dirCode b - dirCode a := by
  rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;>
    subst h <;> subst h' <;> revert hnu <;> decide





theorem cornerBalance_mod4 {n : ℕ} [NeZero n] (dir : Fin n → Pt)
    (hunit : ∀ i, isUnitDir (dir i))
    (hnu : ∀ i, dir (i + 1) ≠ (-(dir i).1, -(dir i).2)) :
    ((cornerBalance (fun i => cross (dir i) (dir (i + 1))) : ℤ) : ZMod 4) = 0 := by
  unfold cornerBalance
  rw [Int.cast_sum]
  have hstep : ∀ i : Fin n,
      ((cross (dir i) (dir (i + 1)) : ℤ) : ZMod 4)
        = dirCode (dir (i + 1)) - dirCode (dir i) := by
    intro i; exact cross_congr_dirCode _ _ (hunit i) (hunit (i + 1)) (hnu i)
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  
  rw [Finset.sum_sub_distrib]
  have hreindex : ∑ i : Fin n, dirCode (dir (i + 1)) = ∑ i : Fin n, dirCode (dir i) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun i => dirCode (dir i))
  rw [hreindex, sub_self]

end StatMech.Onsager.PolygonWalk
