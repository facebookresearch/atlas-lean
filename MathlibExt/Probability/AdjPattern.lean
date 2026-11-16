/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

/-!
# Prescribed adjacency patterns

The number of adjacency functions realizing a prescribed
pattern on `k` distinct entries of one row. The zero-one
law limit argument is not included here.
-/

@[expose] public section


private theorem card_fun_prescribed {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (q : α → Bool) :
    (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ t, f x = q x)).card
      = 2 ^ (Fintype.card α - t.card) := by
  let E : { f : α → Bool // ∀ x ∈ t, f x = q x } ≃ (↥tᶜ → Bool) :=
    { toFun := fun f y => f.val y.val
      invFun := fun g =>
        ⟨fun x => if h : x ∈ t then q x else g ⟨x, Finset.mem_compl.mpr h⟩,
         fun x hx => by simp [hx]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        by_cases h : x ∈ t
        · simp [h, (f.property x h).symm]
        · simp [h]
      right_inv := by
        intro g
        funext y
        have hy : y.val ∉ t := Finset.mem_compl.mp y.property
        simp [hy] }
  have hcard : Fintype.card { f : α → Bool // ∀ x ∈ t, f x = q x }
      = Fintype.card (↥tᶜ → Bool) :=
    Fintype.card_congr E
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl] at hcard
  have hfilter : (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ t, f x = q x)).card
      = Fintype.card { f : α → Bool // ∀ x ∈ t, f x = q x } := by
    rw [← Fintype.card_subtype]
  exact hfilter.trans hcard

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
      ↔ (∀ x ∈ Finset.univ.image g, f x = q x) := by
    intro f
    constructor
    · intro H x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (H i).trans (hq i).symm
    · intro H i
      have hmem : g i ∈ Finset.univ.image g :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact (H (g i) hmem).trans (hq i)
  have hfilter_eq : Finset.univ.filter (fun f : α → Bool => ∀ i, f (g i) = p i)
      = Finset.univ.filter (fun f : α → Bool => ∀ x ∈ Finset.univ.image g, f x = q x) := by
    apply Finset.filter_congr
    intro f _
    exact hiff f
  rw [hfilter_eq, card_fun_prescribed]
  have ht : (Finset.univ.image g).card = k := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  rw [ht]

/-- Prescribed adjacency values (MOD-66 counting core).
Fix distinct target vertices `e i` (for `i : Fin k`) and a
pattern `p`. The number of adjacency functions
`a : Fin n → Fin n → Bool` in which the row of a fixed
vertex `v` realizes `p` over the targets (and `v` is not
itself a target) is `2 ^ (n * n - k)`: the `k` prescribed
entries are forced and all other entries are free. -/
theorem card_adj_pattern {n k : ℕ} (v : Fin n)
    (e : Fin k → Fin n) (he : Function.Injective e)
    (hv : ∀ i, e i ≠ v) (p : Fin k → Bool) :
    (Finset.univ.filter
      (fun a : Fin n → Fin n → Bool => ∀ i, a v (e i) = p i)).card
      = 2 ^ (n * n - k) := by
  have _hv' := hv
  have hg : Function.Injective (fun i : Fin k => (v, e i)) :=
    fun i j h => he (congrArg Prod.snd h)
  have hbase : (Finset.univ.filter
      (fun F : Fin n × Fin n → Bool => ∀ i, F (v, e i) = p i)).card
      = 2 ^ (Fintype.card (Fin n × Fin n) - k) :=
    card_fun_inj_prescribed (fun i : Fin k => (v, e i)) hg p
  have hEs : { F : Fin n × Fin n → Bool // ∀ i, F (v, e i) = p i }
      ≃ { a : Fin n → Fin n → Bool // ∀ i, a v (e i) = p i } :=
    { toFun := fun F => ⟨fun a b => F.val (a, b), fun i => F.property i⟩
      invFun := fun a => ⟨fun p => a.val p.1 p.2, fun i => a.property i⟩
      left_inv := by
        intro F
        apply Subtype.ext
        funext p
        obtain ⟨a, b⟩ := p
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        funext x y
        rfl }
  have hcard_sub : Fintype.card { a : Fin n → Fin n → Bool // ∀ i, a v (e i) = p i }
      = Fintype.card { F : Fin n × Fin n → Bool // ∀ i, F (v, e i) = p i } :=
    Fintype.card_congr hEs.symm
  have hcurried : (Finset.univ.filter
      (fun a : Fin n → Fin n → Bool => ∀ i, a v (e i) = p i)).card
      = Fintype.card { a : Fin n → Fin n → Bool // ∀ i, a v (e i) = p i } := by
    rw [← Fintype.card_subtype]
  have huncurried : (Finset.univ.filter
      (fun F : Fin n × Fin n → Bool => ∀ i, F (v, e i) = p i)).card
      = Fintype.card { F : Fin n × Fin n → Bool // ∀ i, F (v, e i) = p i } := by
    rw [← Fintype.card_subtype]
  have hexp : Fintype.card (Fin n × Fin n) = n * n := by
    rw [Fintype.card_prod, Fintype.card_fin]
  calc (Finset.univ.filter
        (fun a : Fin n → Fin n → Bool => ∀ i, a v (e i) = p i)).card
      = Fintype.card { a : Fin n → Fin n → Bool // ∀ i, a v (e i) = p i } := hcurried
    _ = Fintype.card { F : Fin n × Fin n → Bool // ∀ i, F (v, e i) = p i } := hcard_sub
    _ = (Finset.univ.filter
        (fun F : Fin n × Fin n → Bool => ∀ i, F (v, e i) = p i)).card := huncurried.symm
    _ = 2 ^ (Fintype.card (Fin n × Fin n) - k) := hbase
    _ = 2 ^ (n * n - k) := by rw [hexp]

end
