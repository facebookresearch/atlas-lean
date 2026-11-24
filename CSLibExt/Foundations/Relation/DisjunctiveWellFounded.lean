/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
import Cslib.Foundations.Combinatorics.InfiniteGraphRamsey
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Choose

/-! # Disjunctive well-foundedness

Mathematical source: Podelski and Rybalchenko, _Transition Invariants_,
LICS 2004, pp. 32-41.

This file formalizes the bare-relation soundness direction only: if
`Relation.TransGen R` is pointwise contained in a finite union of
well-founded relations, then `WellFounded R`.

No program syntax, initial or accessible states, liveness property, or
relative-completeness direction is formalized.
-/

@[expose] public section

namespace Cslib

/-- A stepwise chain yields transitive-closure edges pointing backwards. -/
private theorem transGen_of_succ_chain {α : Type*} (R : α → α → Prop)
    (f : ℕ → α) (h : ∀ n, R (f (n + 1)) (f n)) {a b : ℕ} (hab : a < b) :
    Relation.TransGen R (f b) (f a) := by
  have key : ∀ d, Relation.TransGen R (f (a + (d + 1))) (f a) := by
    intro d
    induction d with
    | zero => exact Relation.TransGen.single (h a)
    | succ d ih =>
      have hstep :
          Relation.TransGen R (f (a + (d + 1) + 1)) (f (a + (d + 1))) :=
        Relation.TransGen.single (h (a + (d + 1)))
      have heq : a + (d + 1 + 1) = a + (d + 1) + 1 := by omega
      rw [heq]
      exact hstep.trans ih
  have hb : b = a + ((b - a - 1) + 1) := by omega
  rw [hb]
  exact key (b - a - 1)

/-- Chain form: a covered relation has no infinite descending chain. -/
theorem not_forall_succ_of_transGen_subset_iUnion {α ι : Type*} [Finite ι]
    (R : α → α → Prop) (T : ι → α → α → Prop)
    (hT : ∀ i, WellFounded (T i))
    (hsub : ∀ x y, Relation.TransGen R x y → ∃ i, T i x y) :
    ∀ f : ℕ → α, ¬ ∀ n, R (f (n + 1)) (f n) := by
  intro f hR
  by_cases hι : Nonempty ι
  · have hdecomp :
        ∀ e : Finset ℕ, e.card = 2 → ∃ a b : ℕ, a < b ∧ e = {a, b} := by
      intro e he
      rw [Finset.card_eq_two] at he
      obtain ⟨x, y, hne, rfl⟩ := he
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨x, y, h, rfl⟩
      · exact ⟨y, x, h, Finset.pair_comm x y⟩
    choose lo hi hlt heq using hdecomp
    have hcover :
        ∀ e : Finset ℕ, ∀ h : e.card = 2,
          ∃ i, T i (f (hi e h)) (f (lo e h)) := by
      intro e h
      exact hsub _ _ (transGen_of_succ_chain R f hR (hlt e h))
    choose col hcol using hcover
    let color : Finset ℕ → ι :=
      fun e => dite (e.card = 2) (col e) (fun _ => Classical.choice hι)
    obtain ⟨i₀, s, hs_inf, hs_col⟩ := infinite_graph_ramsey color
    have hcofinal : ∀ N, ∃ n > N, n ∈ s := by
      intro N
      by_contra hcon
      have hsub' : s ⊆ ↑(Finset.range (N + 1)) := by
        intro m hm
        simp only [Finset.mem_coe, Finset.mem_range]
        by_contra hlt
        exact hcon ⟨m, by omega, hm⟩
      have hfin : s.Finite := (Finset.finite_toSet _).subset hsub'
      exact hs_inf hfin
    obtain ⟨g, hg_mono, hg_mem⟩ :=
      Nat.exists_strictMono_subsequence (P := fun n => n ∈ s) hcofinal
    have hcol_eq :
        ∀ e : Finset ℕ, ∀ h : e.card = 2, color e = col e h := by
      intro e h
      exact dite_eq_left h
    have hchain : ∀ n, T i₀ (f (g (n + 1))) (f (g n)) := by
      intro n
      have hlt' : g n < g (n + 1) := hg_mono (Nat.lt_succ_self n)
      have hne : g n ≠ g (n + 1) := ne_of_lt hlt'
      set e : Finset ℕ := {g n, g (n + 1)} with he
      have hcard : e.card = 2 := Finset.card_pair hne
      have hmem : ↑e ⊆ s := by
        intro x hx
        rw [he] at hx
        simp only [Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hg_mem n
        · exact hg_mem (n + 1)
      have hcolor := hs_col e hcard hmem
      have hi₀ : i₀ = col e hcard := hcolor.symm.trans (hcol_eq e hcard)
      have hTi : T i₀ (f (hi e hcard)) (f (lo e hcard)) := by
        rw [hi₀]
        exact hcol e hcard
      have hlo : lo e hcard = g n ∨ lo e hcard = g (n + 1) := by
        have hmem' : lo e hcard ∈ e := by
          have h1 : lo e hcard ∈ ({lo e hcard, hi e hcard} : Finset ℕ) := by
            simp
          rwa [← heq e hcard] at h1
        have hmem'' : lo e hcard ∈ ({g n, g (n + 1)} : Finset ℕ) := hmem'
        simpa using hmem''
      have hhi : hi e hcard = g n ∨ hi e hcard = g (n + 1) := by
        have hmem' : hi e hcard ∈ e := by
          have h1 : hi e hcard ∈ ({lo e hcard, hi e hcard} : Finset ℕ) := by
            simp
          rwa [← heq e hcard] at h1
        have hmem'' : hi e hcard ∈ ({g n, g (n + 1)} : Finset ℕ) := hmem'
        simpa using hmem''
      have hlt_e : lo e hcard < hi e hcard := hlt e hcard
      have hident : lo e hcard = g n ∧ hi e hcard = g (n + 1) := by
        rcases hlo with h1 | h1 <;> rcases hhi with h2 | h2
        · omega
        · exact ⟨h1, h2⟩
        · omega
        · omega
      obtain ⟨h1, h2⟩ := hident
      rw [h1, h2] at hTi
      exact hTi
    exact (wellFounded_iff_isEmpty_descending_chain.mp (hT i₀)).false
      ⟨fun n => f (g n), hchain⟩
  · obtain ⟨i, -⟩ := hsub _ _ (Relation.TransGen.single (hR 0))
    exact False.elim (hι ⟨i⟩)

/-- A relation whose transitive closure sits in a finite union of well-founded
relations is itself well-founded. -/
theorem wellFounded_of_transGen_subset_iUnion {α ι : Type*} [Finite ι]
    (R : α → α → Prop) (T : ι → α → α → Prop)
    (hT : ∀ i, WellFounded (T i))
    (hsub : ∀ x y, Relation.TransGen R x y → ∃ i, T i x y) :
    WellFounded R := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun x => ?_⟩
  obtain ⟨f, hf⟩ := x
  exact not_forall_succ_of_transGen_subset_iUnion R T hT hsub f hf

/-- Forward form: the same conclusion for a forward step relation, read
backwards. -/
theorem wellFounded_swap_of_transGen_subset_iUnion {α ι : Type*} [Finite ι]
    (step : α → α → Prop) (T : ι → α → α → Prop)
    (hT : ∀ i, WellFounded (fun y x => T i x y))
    (hsub : ∀ x y, Relation.TransGen step x y → ∃ i, T i x y) :
    WellFounded (fun y x => step x y) := by
  apply wellFounded_of_transGen_subset_iUnion _ _ hT
  intro x y h
  have h' : Relation.TransGen step y x := Relation.transGen_swap.mp h
  exact hsub y x h'

/-- A relation is disjunctively well-founded if it is a finite union of
well-founded relations. -/
def IsDisjunctivelyWellFounded {α : Type*} (S : α → α → Prop) : Prop :=
  ∃ n : ℕ, ∃ T : Fin n → α → α → Prop,
    (∀ i, WellFounded (T i)) ∧ S = fun x y => ∃ i, T i x y

/-- A relation whose transitive closure sits in a disjunctively well-founded
relation is itself well-founded. -/
theorem wellFounded_of_isDisjunctivelyWellFounded {α : Type*}
    (R S : α → α → Prop) (hS : IsDisjunctivelyWellFounded S)
    (hsub : ∀ x y, Relation.TransGen R x y → S x y) :
    WellFounded R := by
  obtain ⟨n, T, hT, rfl⟩ := hS
  exact wellFounded_of_transGen_subset_iUnion R T hT hsub

end Cslib
