/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

import MathlibExt.Data.Fintype.PrescribedFunctions

/-!
# Prescribed adjacency patterns

The number of adjacency functions realizing a prescribed
pattern on `k` distinct entries of one row. The zero-one
law limit argument is not included here.
-/

@[expose] public section

namespace MathlibExt.Probability.AdjPattern

private theorem card_fun_inj_prescribed {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (g : Fin k → α) (hg : Function.Injective g) (p : Fin k → Bool) :
    (Finset.univ.filter (fun f : α → Bool => ∀ i, f (g i) = p i)).card
      = 2 ^ (Fintype.card α - k) := by
  let q : α → Bool := fun x => if h : ∃ i, g i = x then p (Classical.choose h) else false
  have hq : ∀ i, q (g i) = p i := by
    intro i
    have hex : ∃ j, g j = g i := ⟨i, rfl⟩
    have hspec : g (Classical.choose hex) = g i := Classical.choose_spec hex
    have hci : Classical.choose hex = i := hg hspec
    calc q (g i) = p (Classical.choose hex) := dite_eq_left hex
      _ = p i := by rw [hci]
  have hiff : ∀ f : α → Bool, (∀ i, f (g i) = p i)
      ↔ (∀ x : {x // x ∈ Finset.univ.image g}, f x.1 = q x.1) := by
    intro f
    constructor
    · rintro H ⟨x, hx⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (H i).trans (hq i).symm
    · intro H i
      have hmem : g i ∈ Finset.univ.image g :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact (H ⟨g i, hmem⟩).trans (hq i)
  have ht : (Finset.univ.image g).card = k := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hcount :=
    Fintype.card_filter_univ_eqOn (κ := Bool) (Finset.univ.image g) (fun x => q x.1)
  rw [Fintype.card_bool, ht] at hcount
  rw [← hcount]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hiff f

/-- Prescribed adjacency values.
Fix distinct target vertices `e i` (for `i : Fin k`) and a
pattern `p`. The number of adjacency functions
`a : Fin n → Fin n → Bool` in which the row of a fixed
vertex `v` realizes `p` over the targets is `2 ^ (n * n - k)`:
the `k` prescribed entries are forced and all other entries
are free. A target may be `v` itself. -/
theorem card_adj_pattern {n k : ℕ} (v : Fin n)
    (e : Fin k → Fin n) (he : Function.Injective e) (p : Fin k → Bool) :
    (Finset.univ.filter
      (fun a : Fin n → Fin n → Bool => ∀ i, a v (e i) = p i)).card
      = 2 ^ (n * n - k) := by
  have hg : Function.Injective (fun i : Fin k => (v, e i)) :=
    fun i j h => he (congrArg Prod.snd h)
  have hcurry : (Finset.univ.filter
      (fun F : Fin n × Fin n → Bool => ∀ i, F (v, e i) = p i)).card
      = (Finset.univ.filter
      (fun a : Fin n → Fin n → Bool => ∀ i, a v (e i) = p i)).card :=
    Finset.card_equiv (Equiv.curry (Fin n) (Fin n) Bool) fun F => by
      simp [Equiv.curry, Function.curry_apply]
  rw [← hcurry, card_fun_inj_prescribed (fun i : Fin k => (v, e i)) hg p,
    Fintype.card_prod, Fintype.card_fin]

end MathlibExt.Probability.AdjPattern

end
