/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Percolation.FiniteTreeTripod

open Set SimpleGraph

namespace StatMech.Percolation




theorem tree_exterior_amalgam_separated
    {W V : Type*} (T : SimpleGraph W) (E U : SimpleGraph V)
    (embed : W → V) (hembed : Function.Injective embed)
    (hub : W) (leaf : Fin 3 → W)
    (hcut : ∀ i j, i ≠ j →
      ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j))
    (hEsep : ∀ i j, i ≠ j → ¬ E.Reachable (embed (leaf i)) (embed (leaf j)))
    (hEonly : ∀ z y, E.Adj (embed z) y → ∃ i, z = leaf i)
    (hUdecomp : ∀ {x y}, U.Adj x y →
      E.Adj x y ∨ ∃ a b, T.Adj a b ∧ embed a = x ∧ embed b = y) :
    ∀ i j, i ≠ j →
      ¬ (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (leaf i)) (embed (leaf j)) := by
  classical
  have exterior_embedded_eq : ∀ i z,
      E.Reachable (embed (leaf i)) (embed z) → z = leaf i := by
    intro i z hr
    by_cases hz : z = leaf i
    · exact hz
    obtain ⟨w⟩ := hr.symm
    have hne : embed z ≠ embed (leaf i) := fun h => hz (hembed h)
    obtain ⟨y, hzy, q, _⟩ := w.exists_eq_cons_of_ne hne
    obtain ⟨k, rfl⟩ := hEonly z y hzy
    have hki : k = i := by
      by_contra hneki
      exact hEsep i k (Ne.symm hneki) hr
    exact congrArg leaf hki
  let R : Fin 3 → V → Prop := fun i x =>
    E.Reachable (embed (leaf i)) x ∨
      ∃ z, embed z = x ∧ (T.deleteIncidenceSet hub).Reachable (leaf i) z
  have R_start : ∀ i, R i (embed (leaf i)) := fun i =>
    Or.inl (Reachable.refl _)
  have R_step : ∀ i {x y}, R i x →
      (U.deleteIncidenceSet (embed hub)).Adj x y → R i y := by
    intro i x y hx hxy
    have hUne : x ≠ embed hub ∧ y ≠ embed hub :=
      (deleteIncidenceSet_adj.mp hxy).2
    rcases hUdecomp (deleteIncidenceSet_adj.mp hxy).1 with hE | hT
    · rcases hx with hxE | ⟨z, hz, hzreach⟩
      · exact Or.inl (hxE.trans hE.reachable)
      · subst x
        obtain ⟨k, hzk⟩ := hEonly z y hE
        subst z
        have hki : k = i := by
          by_contra hne
          exact hcut i k (Ne.symm hne) hzreach
        subst k
        exact Or.inl hE.reachable
    · obtain ⟨a, b, hab, hax, hby⟩ := hT
      subst x
      subst y
      have ha : a ≠ hub := fun h => hUne.1 (h ▸ rfl)
      have hb : b ≠ hub := fun h => hUne.2 (h ▸ rfl)
      have habCut : (T.deleteIncidenceSet hub).Adj a b :=
        deleteIncidenceSet_adj.mpr ⟨hab, ha, hb⟩
      rcases hx with hxE | ⟨z, hz, hzreach⟩
      · have hai : a = leaf i := exterior_embedded_eq i a hxE
        subst a
        exact Or.inr ⟨b, rfl, habCut.reachable⟩
      · have hza : z = a := hembed hz
        subst z
        exact Or.inr ⟨b, rfl, hzreach.trans habCut.reachable⟩
  intro i j hij hr
  obtain ⟨w⟩ := hr
  have walk_R : ∀ {x y} (q : (U.deleteIncidenceSet (embed hub)).Walk x y),
      R i x → R i y := by
    intro x y q hx
    induction q with
    | nil => exact hx
    | cons h _ ih => exact ih (R_step i hx h)
  have Rend : R i (embed (leaf j)) := by
    exact walk_R w (R_start i)
  rcases Rend with hE | ⟨z, hz, hT⟩
  · exact hEsep i j hij hE
  · have hzj : z = leaf j := hembed hz
    subst z
    exact hcut i j hij hT

end StatMech.Percolation
