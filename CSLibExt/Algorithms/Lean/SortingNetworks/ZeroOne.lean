/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.MinMax
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Comparator networks and the 0-1 principle

A comparator network on `n` wires (CLRS, second edition, Chapter 27; Knuth, *The Art of Computer
Programming*, Volume 3, Section 5.3.4) is a list of comparators `(i, j)`; a comparator replaces
the values on wires `i` and `j` by their minimum and maximum, the minimum on wire `i`
(`comparator`). `run net v` applies the comparators in order. A network *sorts* if its output
is monotone (wire order) on every input (`Sorts`).

Main results:

* `run_perm`: the output is a permutation of the input.
* `run_comp` (CLRS Lemma 27.1): a network commutes with every monotone map, `run net (f ∘ v) =
  f ∘ run net v`.
* `sorts_of_sorts_bool` (**the 0-1 principle**, CLRS Theorem 27.2; Knuth Theorem 5.3.4Z): a
  network that sorts every input of `0`s and `1`s (`Bool` vectors) sorts every input over every
  linear order.
* `sortsBool_eq_true_iff`, `sorts_of_sortsBool`: the 0-1 condition is decided by `sortsBool`,
  which runs the network on all `2 ^ n` Boolean inputs; so a concrete network is proved to sort by
  `decide` (the tests verify Knuth's 5-comparator network on 4 wires and the 9-comparator network
  on 5 wires).

## Cost model

No `TimeM` cost model: the measures of a network are its size (the number of comparators) and
its depth (`Network.DepthLE` in `Depth.lean`), which are properties of the comparator list rather
than of a computation charged here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks

variable {n : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A comparator network: the comparators `(i, j)`, applied in list order. -/
abbrev Network (n : ℕ) := List (Fin n × Fin n)

/-- The comparator `(i, j)`: the minimum of wires `i` and `j` goes to wire `i`, the maximum to
wire `j`. -/
def comparator (i j : Fin n) (v : Fin n → α) : Fin n → α :=
  fun k => if k = i then min (v i) (v j) else if k = j then max (v i) (v j) else v k

/-- Run a network on the input `v`. -/
def run (net : Network n) (v : Fin n → α) : Fin n → α :=
  net.foldl (fun w c => comparator c.1 c.2 w) v

/-- A network sorts inputs over `α` if every output is monotone in the wire order. -/
def Sorts (net : Network n) (α : Type*) [LinearOrder α] : Prop :=
  ∀ v : Fin n → α, Monotone (run net v)

/-- Comparators commute with monotone maps. -/
theorem comparator_comp {f : α → β} (hf : Monotone f) (i j : Fin n) (v : Fin n → α) :
    comparator i j (f ∘ v) = f ∘ comparator i j v := by
  funext k
  simp only [comparator, Function.comp_apply]
  split_ifs
  · exact (hf.map_min).symm
  · exact (hf.map_max).symm
  · rfl

/-- **Networks commute with monotone maps** (CLRS Lemma 27.1). -/
theorem run_comp {f : α → β} (hf : Monotone f) :
    ∀ (net : Network n) (v : Fin n → α), run net (f ∘ v) = f ∘ run net v
  | [], _ => rfl
  | c :: net, v => by
      simp only [run, List.foldl_cons] at *
      rw [comparator_comp hf]
      exact run_comp hf net _

/-- A comparator permutes its inputs. -/
theorem comparator_perm (i j : Fin n) (v : Fin n → α) :
    ∃ σ : Equiv.Perm (Fin n), comparator i j v = v ∘ σ := by
  by_cases hij : i = j
  · subst hij
    refine ⟨1, funext fun k => ?_⟩
    simp only [comparator, min_self, max_self, Equiv.Perm.coe_one, Function.comp_apply, id_eq]
    split_ifs with h <;> simp [h]
  · rcases le_total (v i) (v j) with h | h
    · refine ⟨1, funext fun k => ?_⟩
      simp only [comparator, min_eq_left h, max_eq_right h, Equiv.Perm.coe_one,
        Function.comp_apply, id_eq]
      split_ifs with h1 h2
      · subst h1; rfl
      · subst h2; rfl
      · rfl
    · refine ⟨Equiv.swap i j, funext fun k => ?_⟩
      simp only [comparator, min_eq_right h, max_eq_left h, Function.comp_apply]
      split_ifs with h1 h2
      · subst h1; simp
      · subst h2; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **The output is a permutation of the input.** -/
theorem run_perm : ∀ (net : Network n) (v : Fin n → α),
    ∃ σ : Equiv.Perm (Fin n), run net v = v ∘ σ
  | [], v => ⟨1, rfl⟩
  | c :: net, v => by
      obtain ⟨σ, hσ⟩ := comparator_perm c.1 c.2 v
      obtain ⟨τ, hτ⟩ := run_perm net (comparator c.1 c.2 v)
      refine ⟨σ * τ, ?_⟩
      simp only [run, List.foldl_cons] at hτ ⊢
      rw [hτ, hσ]
      rfl

/-- **The 0-1 principle** (CLRS Theorem 27.2): a network that sorts every Boolean input sorts
every input over every linear order. -/
theorem sorts_of_sorts_bool {net : Network n} (h : Sorts net Bool) (α : Type*) [LinearOrder α] :
    Sorts net α := by
  intro v
  by_contra hmono
  rw [Monotone] at hmono
  push Not at hmono
  obtain ⟨a, b, hab, hlt⟩ := hmono
  -- threshold at the larger value `run net v a`
  set t := run net v a
  let f : α → Bool := fun x => decide (t ≤ x)
  have hf : Monotone f := fun x y hxy => by
    simp only [f, decide_eq_true_eq, Bool.le_iff_imp]
    exact fun h => h.trans hxy
  have h01 := h (f ∘ v)
  rw [run_comp hf] at h01
  have := h01 hab
  simp only [Function.comp_apply, f, t, le_refl, decide_true] at this
  have hb : decide (run net v a ≤ run net v b) = false := by
    simp only [decide_eq_false_iff_not, not_le]; exact hlt
  rw [hb] at this
  exact absurd this (by decide)

/-- Decide whether a network sorts every Boolean input, by running it on all `2 ^ n` of them. -/
def sortsBool (net : Network n) : Bool :=
  decide (∀ v : Fin n → Bool, ∀ i j : Fin n, i ≤ j → run net v i ≤ run net v j)

/-- `sortsBool` decides whether a network sorts every Boolean input. -/
theorem sortsBool_eq_true_iff {net : Network n} : sortsBool net = true ↔ Sorts net Bool := by
  simp only [sortsBool, decide_eq_true_iff, Sorts, Monotone]

/-- **A network that passes `sortsBool` sorts every input over every linear order.** -/
theorem sorts_of_sortsBool {net : Network n} (h : sortsBool net = true) (α : Type*)
    [LinearOrder α] : Sorts net α :=
  sorts_of_sorts_bool (sortsBool_eq_true_iff.1 h) α

end Cslib.Algorithms.Lean.SortingNetworks
