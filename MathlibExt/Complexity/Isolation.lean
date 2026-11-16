/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Ring

/-!
# Isolation counting over F2

For a nonzero vector over `ZMod 2`, exactly half of all
linear functionals annihilate it. The Valiant-Vazirani
isolation argument is not included here.
-/

@[expose] public section

/-- Random linear functional over `F2` (MOD-56 isolation
core). For a coefficient vector `a` and input `v`, the
pairing is `∑ i, a i * v i` in `ZMod 2`. -/
def dotF2 {n : ℕ} (a v : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, a i * v i

/-- Exactly half of all coefficient vectors annihilate a
nonzero vector: the annihilating set has cardinality
`2^(n-1)` in counting form, stated as twice its size being
`2^n`. -/
theorem dotF2_card {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) :
    2 * (Finset.univ.filter (fun a => dotF2 a v = 0)).card
      = 2 ^ n := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hadd1 : ∀ x : ZMod 2, x + 1 + 1 = x := by decide
  have hflip : ∀ x : ZMod 2, (x + 1 = 0 ↔ x ≠ 0) := by decide
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, v i₀ ≠ 0 := by
    simpa using Function.ne_iff.mp hv
  have hvi0 : v i₀ = 1 := by
    rcases h01 (v i₀) with h | h
    · exact absurd h hi₀
    · exact h
  set g : (Fin n → ZMod 2) → (Fin n → ZMod 2) :=
    fun a => Function.update a i₀ (a i₀ + 1) with hg
  have hg_apply : ∀ (a : Fin n → ZMod 2) (i : Fin n), i ≠ i₀ → g a i = a i := by
    intro a i h
    simp only [hg]
    exact Function.update_of_ne h _ _
  have hg_apply_self : ∀ (a : Fin n → ZMod 2), g a i₀ = a i₀ + 1 := by
    intro a
    simp only [hg]
    exact Function.update_self _ _ _
  have hg_inv : ∀ a, g (g a) = a := by
    intro a
    funext i
    by_cases h : i = i₀
    · subst h
      rw [hg_apply_self, hg_apply_self]
      exact hadd1 _
    · rw [hg_apply _ _ h, hg_apply _ _ h]
  have hg_inj : Function.Injective g := Function.Involutive.injective hg_inv
  have hsum : ∀ a, dotF2 (g a) v = dotF2 a v + 1 := by
    intro a
    have e1 : g a i₀ * v i₀ + (∑ x ∈ Finset.univ.erase i₀, g a x * v x)
        = ∑ i, g a i * v i :=
      Finset.add_sum_erase _ (fun i => g a i * v i) (Finset.mem_univ i₀)
    have e2 : a i₀ * v i₀ + (∑ x ∈ Finset.univ.erase i₀, a x * v x)
        = ∑ i, a i * v i :=
      Finset.add_sum_erase _ (fun i => a i * v i) (Finset.mem_univ i₀)
    have herase : (∑ x ∈ Finset.univ.erase i₀, g a x * v x)
        = ∑ x ∈ Finset.univ.erase i₀, a x * v x :=
      Finset.sum_congr rfl (fun i hi => by rw [hg_apply _ _ (Finset.ne_of_mem_erase hi)])
    unfold dotF2
    rw [← e1, ← e2, herase, hg_apply_self, hvi0]
    ring
  have hmem : ∀ a, (dotF2 (g a) v = 0 ↔ dotF2 a v ≠ 0) := by
    intro a
    rw [hsum a]
    exact hflip _
  have hadd : (Finset.univ.filter (fun a => dotF2 a v = 0)).card
      + (Finset.univ.filter (fun a => ¬ dotF2 a v = 0)).card
      = (Finset.univ : Finset (Fin n → ZMod 2)).card :=
    Finset.card_filter_add_card_filter_not _
  have hcard : (Finset.univ.filter (fun a => dotF2 a v = 0)).card
      = (Finset.univ.filter (fun a => ¬ dotF2 a v = 0)).card := by
    apply Finset.card_bij (fun a _ => g a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact fun h => (hmem a).mp h ha
    · intro a₁ _ a₂ _ h
      exact hg_inj h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨g b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem b).mpr hb⟩, hg_inv b⟩
  have htot : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  omega

end
