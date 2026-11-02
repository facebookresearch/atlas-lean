/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring

@[expose] public section

open SimpleGraph

section
namespace MetaMathlibExt

/-! # Domino tilings and Fibonacci–Pell products
-/

-- Pell helpers (closed-form side): same pair recurrence as in the statement.
private def pellPair : ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun (_ : ℕ) => ℕ × ℕ) (0, 1)
    (fun (_ : ℕ) (ih : ℕ × ℕ) => (ih.2, 2 * ih.2 + ih.1))

private def pell (n : ℕ) : ℕ := (pellPair n).1

private theorem pell_eq_rec (n : ℕ) : pell n =
    ((Nat.rec (motive := fun (_ : ℕ) => ℕ × ℕ) (0, 1)
      (fun (_ : ℕ) (ih : ℕ × ℕ) => (ih.2, 2 * ih.2 + ih.1)) n).1) := rfl

private theorem pell_add_two (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := rfl

private theorem pell_vals :
    pell 0 = 0 ∧ pell 1 = 1 ∧ pell 2 = 2 ∧ pell 3 = 5 ∧ pell 4 = 12 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Compatibility with the canonical `pellNumber` sequence: same initial values
-- and same recurrence, hence equal at every index.
private theorem pell_eq_pellNumber : ∀ n : ℕ, pell n = pellNumber n := by
  suffices h : ∀ n : ℕ, pell n = pellNumber n ∧ pell (n + 1) = pellNumber (n + 1)
    from fun n => (h n).1
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e]
    have hp : pell (n + 2) = 2 * pell (n + 1) + pell n := pell_add_two n
    have hP : pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl
    rw [hp, hP, h1, h0]

-- d m = fib (m + 1) * pell (m + 1): closed form with n = m + 1.
private def dval (m : ℕ) : ℕ := Nat.fib (m + 1) * pell (m + 1)

private theorem dval_vals : dval 0 = 1 ∧ dval 1 = 2 ∧ dval 2 = 10 ∧ dval 3 = 36 := by
  refine ⟨rfl, rfl, by decide, by decide⟩

-- Order-4 recurrence for the product side, in ℤ (minus sign needs ℤ).
-- Its characteristic polynomial is x^4 - 2x^3 - 7x^2 - 2x + 1: the roots are the
-- four pairwise products of the roots of x^2 - x - 1 and x^2 - 2x - 1 (the
-- tensor product of the two companion matrices), not the roots of the polynomial
-- product (x^2 - x - 1)(x^2 - 2x - 1) = x^4 - 3x^3 + 3x + 1.
private theorem dval_recurrence (m : ℕ) :
    ((dval (m + 4) : ℕ) : ℤ) = 2 * (dval (m + 3) : ℤ) + 7 * (dval (m + 2) : ℤ)
      + 2 * (dval (m + 1) : ℤ) - (dval m : ℤ) := by
  unfold dval
  have hf2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have hf3 : Nat.fib (m + 3) = Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)) := by
    have h : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      have := @Nat.fib_add_two (m + 1); simpa [Nat.add_assoc] using this
    rw [h, hf2]
  have hf4 : Nat.fib (m + 4) =
      (Nat.fib m + Nat.fib (m + 1)) +
        (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) := by
    have h : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
      have := @Nat.fib_add_two (m + 2); simpa [Nat.add_assoc] using this
    rw [h, hf2, hf3]
  have hf5 : Nat.fib (m + 5) = (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) +
      ((Nat.fib m + Nat.fib (m + 1)) +
        (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)))) := by
    have h : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := by
      have := @Nat.fib_add_two (m + 3); simpa [Nat.add_assoc] using this
    rw [h, hf3, hf4]
  have hp2 : pell (m + 2) = 2 * pell (m + 1) + pell m := rfl
  have hp3 : pell (m + 3) = 2 * (2 * pell (m + 1) + pell m) + pell (m + 1) := by
    have : pell (m + 3) = 2 * pell (m + 2) + pell (m + 1) := rfl
    rw [this, hp2]
  have hp4 : pell (m + 4) = 2 * (2 * (2 * pell (m + 1) + pell m) + pell (m + 1)) +
      (2 * pell (m + 1) + pell m) := by
    have : pell (m + 4) = 2 * pell (m + 3) + pell (m + 2) := rfl
    rw [this, hp3, hp2]
  have hp5 : pell (m + 5) =
      2 * (2 * (2 * (2 * pell (m + 1) + pell m) + pell (m + 1)) +
        (2 * pell (m + 1) + pell m)) +
        (2 * (2 * pell (m + 1) + pell m) + pell (m + 1)) := by
    have : pell (m + 5) = 2 * pell (m + 4) + pell (m + 3) := rfl
    rw [this, hp4, hp3]
  have e1 : Nat.fib (m + 1 + 1) = Nat.fib m + Nat.fib (m + 1) := hf2
  have e2 : Nat.fib (m + 2 + 1) =
      Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)) := by simpa using hf3
  have e3 : Nat.fib (m + 3 + 1) = (Nat.fib m + Nat.fib (m + 1)) +
      (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) := by simpa using hf4
  have e4 : Nat.fib (m + 4 + 1) = (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1))) +
      ((Nat.fib m + Nat.fib (m + 1)) +
        (Nat.fib (m + 1) + (Nat.fib m + Nat.fib (m + 1)))) := by
    simpa using hf5
  rw [e1, e2, e3, e4, hp2, hp3, hp4, hp5]
  push_cast
  ring

-- Counting side setup: W_4 is K_4 minus the edge {0, 1}.
private def W4 : SimpleGraph (Fin 4) :=
  (SimpleGraph.completeGraph (Fin 4)).deleteEdges {Sym2.mk (0 : Fin 4) (1 : Fin 4)}

private theorem W4_adj (a b : Fin 4) :
    W4.Adj a b ↔ a ≠ b ∧ s(a, b) ≠ s((0 : Fin 4), (1 : Fin 4)) := by
  unfold W4
  rw [deleteEdges_adj, completeGraph_eq_top, top_adj]
  constructor
  · rintro ⟨hne, hmem⟩
    refine ⟨hne, ?_⟩
    simpa using hmem
  · rintro ⟨hne, hne2⟩
    refine ⟨hne, ?_⟩
    simpa using hne2

private instance : DecidableRel W4.Adj := fun a b =>
  decidable_of_iff' _ (W4_adj a b)

private theorem boxProd_adj_unfold (m : ℕ) (x y : Fin 4 × Fin m) :
    (W4 □ SimpleGraph.pathGraph m).Adj x y ↔
      (W4.Adj x.1 y.1 ∧ x.2 = y.2) ∨
        ((SimpleGraph.pathGraph m).Adj x.2 y.2 ∧ x.1 = y.1) :=
  boxProd_adj

-- Horizontal matchings on `U ⊆ Fin 4`: fixed-point-free involutions using `W4`-edges.
private def HorizPairing (U : Finset (Fin 4)) : Type :=
  { f : Fin 4 → Fin 4 //
    (∀ a ∈ U, f a ∈ U ∧ f (f a) = a ∧ f a ≠ a ∧ W4.Adj a (f a)) ∧
    ∀ a ∉ U, f a = a }

private instance horizFintype (U : Finset (Fin 4)) : Fintype (HorizPairing U) :=
  Subtype.fintype _

-- Explicit weight table: w(∅) = 1, w(univ) = 2, w(pair) = edge indicator, else 0.
private def wHoriz (U : Finset (Fin 4)) : ℕ :=
  if U = ∅ then 1
  else if U = Finset.univ then 2
  else if U.card = 2 then
    (if ∃ a b : Fin 4, U = {a, b} ∧ W4.Adj a b then 1 else 0)
  else 0

private theorem horiz_card :
    ∀ U : Finset (Fin 4), Fintype.card (HorizPairing U) = wHoriz U := by
  decide

-- Tilings of `m` layers with outgoing holes `S`: recursive transfer-matrix type.
private def Tiling : ℕ → Finset (Fin 4) → Type
  | 0, S => PLift (S = ∅)
  | (m + 1), S' =>
      Σ S : Finset (Fin 4),
        PLift (Disjoint S S') × Tiling m S × HorizPairing (Finset.univ \ (S ∪ S'))

private instance tilingFintype : ∀ (m : ℕ) (S : Finset (Fin 4)), Fintype (Tiling m S)
  | 0, _ => PLift.fintypeProp _
  | (m + 1), _ =>
      @Sigma.instFintype _ _ (fun S =>
        @instFintypeProd _ _ (PLift.fintypeProp _)
          (@instFintypeProd _ _ (tilingFintype m S) (horizFintype _))) inferInstance

private def Ncount (m : ℕ) (S : Finset (Fin 4)) : ℕ := Fintype.card (Tiling m S)

private theorem card_plift_prop (p : Prop) [Decidable p] :
    Fintype.card (PLift p) = (if p then 1 else 0) := by
  by_cases h : p
  · simp only [ite_eq_left h]
    have e : PLift p ≃ Unit :=
      ⟨fun _ => (), fun _ => ⟨h⟩, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
    calc Fintype.card (PLift p) = Fintype.card Unit := Fintype.card_congr e
      _ = 1 := Fintype.card_unit
  · simp only [ite_eq_right h]
    have e : PLift p ≃ Empty :=
      ⟨fun x => (h x.down).elim, fun x => x.elim,
        fun x => (h x.down).elim, fun x => x.elim⟩
    calc Fintype.card (PLift p) = Fintype.card Empty := Fintype.card_congr e
      _ = 0 := Fintype.card_empty

private theorem Ncount_zero (S : Finset (Fin 4)) :
    Ncount 0 S = (if S = ∅ then 1 else 0) := by
  unfold Ncount
  change Fintype.card (PLift (S = ∅)) = _
  exact card_plift_prop _

private theorem Ncount_succ (m : ℕ) (S' : Finset (Fin 4)) :
    Ncount (m + 1) S' = ∑ S : Finset (Fin 4),
      (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0) := by
  unfold Ncount
  change Fintype.card (Σ S : Finset (Fin 4),
      PLift (Disjoint S S') × Tiling m S × HorizPairing _) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, card_plift_prop, horiz_card _]
  by_cases h : Disjoint S S'
  · simp only [ite_eq_left h, one_mul]
  · simp only [ite_eq_right h, zero_mul]

-- Five aggregated boundary states.
private def Aval (m : ℕ) : ℕ := Ncount m ∅
private def Bval (m : ℕ) : ℕ :=
  Ncount m {0, 2} + Ncount m {0, 3} + Ncount m {1, 2} + Ncount m {1, 3}
private def Cval (m : ℕ) : ℕ := Ncount m {2, 3}
private def Dval (m : ℕ) : ℕ := Ncount m {0, 1}
private def Eval (m : ℕ) : ℕ := Ncount m Finset.univ

-- Restrict the transfer sum to an explicit support.
private theorem sum_support (m : ℕ) (S' : Finset (Fin 4)) (s : Finset (Finset (Fin 4)))
    (h : ∀ S : Finset (Fin 4),
      S ∉ s → (¬Disjoint S S' ∨ wHoriz (Finset.univ \ (S ∪ S')) = 0)) :
    (∑ S : Finset (Fin 4),
        (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0))
      = ∑ S ∈ s,
        (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0) := by
  have hsub : s ⊆ Finset.univ := Finset.subset_univ s
  have h0 : ∀ S ∈ (Finset.univ : Finset (Finset (Fin 4))), S ∉ s →
      (if Disjoint S S' then Ncount m S * wHoriz (Finset.univ \ (S ∪ S')) else 0) = 0 := by
    intro S _ hmem
    obtain (hdisj | hw) := h S hmem
    · simp only [ite_eq_right hdisj]
    · by_cases hdisj : Disjoint S S'
      · simp only [ite_eq_left hdisj, hw, mul_zero]
      · simp only [ite_eq_right hdisj]
  exact (Finset.sum_subset hsub h0).symm

private theorem Aval_succ (m : ℕ) :
    Aval (m + 1) = 2 * Aval m + Bval m + Dval m + Eval m := by
  unfold Aval Bval Dval Eval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {0, 1}, Finset.univ} :
        Finset (Finset (Fin 4))) →
        (¬Disjoint S ∅ ∨ wHoriz (Finset.univ \ (S ∪ ∅)) = 0) := by decide
  rw [sum_support m ∅ _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) ∅ := by decide
  have hd1 : Disjoint ({0, 2} : Finset (Fin 4)) ∅ := by decide
  have hd2 : Disjoint ({0, 3} : Finset (Fin 4)) ∅ := by decide
  have hd3 : Disjoint ({1, 2} : Finset (Fin 4)) ∅ := by decide
  have hd4 : Disjoint ({1, 3} : Finset (Fin 4)) ∅ := by decide
  have hd5 : Disjoint ({0, 1} : Finset (Fin 4)) ∅ := by decide
  have hd6 : Disjoint (Finset.univ : Finset (Fin 4)) ∅ := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ ∅)) = 2 := by decide
  have hw1 : wHoriz (Finset.univ \ (({0, 2} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw2 : wHoriz (Finset.univ \ (({0, 3} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw3 : wHoriz (Finset.univ \ (({1, 2} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw4 : wHoriz (Finset.univ \ (({1, 3} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw5 : wHoriz (Finset.univ \ (({0, 1} : Finset (Fin 4)) ∪ ∅)) = 1 := by decide
  have hw6 : wHoriz (Finset.univ \ (Finset.univ ∪ (∅ : Finset (Fin 4)))) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, ite_eq_left hd2, ite_eq_left hd3,
    ite_eq_left hd4, ite_eq_left hd5, ite_eq_left hd6, hw0, hw1, hw2, hw3, hw4, hw5, hw6]
  ring

private theorem mixed02_succ (m : ℕ) :
    Ncount (m + 1) {0, 2} = Ncount m ∅ + Ncount m {1, 3} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅, {1, 3}} : Finset (Finset (Fin 4))) →
        (¬Disjoint S {0, 2} ∨ wHoriz (Finset.univ \ (S ∪ {0, 2})) = 0) := by decide
  rw [sum_support m {0, 2} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {0, 2} := by decide
  have hd1 : Disjoint ({1, 3} : Finset (Fin 4)) {0, 2} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {0, 2})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({1, 3} : Finset (Fin 4)) ∪ {0, 2})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

private theorem mixed03_succ (m : ℕ) :
    Ncount (m + 1) {0, 3} = Ncount m ∅ + Ncount m {1, 2} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅, {1, 2}} : Finset (Finset (Fin 4))) →
        (¬Disjoint S {0, 3} ∨ wHoriz (Finset.univ \ (S ∪ {0, 3})) = 0) := by decide
  rw [sum_support m {0, 3} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {0, 3} := by decide
  have hd1 : Disjoint ({1, 2} : Finset (Fin 4)) {0, 3} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {0, 3})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({1, 2} : Finset (Fin 4)) ∪ {0, 3})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

private theorem mixed12_succ (m : ℕ) :
    Ncount (m + 1) {1, 2} = Ncount m ∅ + Ncount m {0, 3} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅, {0, 3}} : Finset (Finset (Fin 4))) →
        (¬Disjoint S {1, 2} ∨ wHoriz (Finset.univ \ (S ∪ {1, 2})) = 0) := by decide
  rw [sum_support m {1, 2} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {1, 2} := by decide
  have hd1 : Disjoint ({0, 3} : Finset (Fin 4)) {1, 2} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {1, 2})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({0, 3} : Finset (Fin 4)) ∪ {1, 2})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

private theorem mixed13_succ (m : ℕ) :
    Ncount (m + 1) {1, 3} = Ncount m ∅ + Ncount m {0, 2} := by
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅, {0, 2}} : Finset (Finset (Fin 4))) →
        (¬Disjoint S {1, 3} ∨ wHoriz (Finset.univ \ (S ∪ {1, 3})) = 0) := by decide
  rw [sum_support m {1, 3} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {1, 3} := by decide
  have hd1 : Disjoint ({0, 2} : Finset (Fin 4)) {1, 3} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {1, 3})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({0, 2} : Finset (Fin 4)) ∪ {1, 3})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

private theorem Bval_succ (m : ℕ) : Bval (m + 1) = 4 * Aval m + Bval m := by
  unfold Bval Aval
  rw [mixed02_succ, mixed03_succ, mixed12_succ, mixed13_succ]
  ring

private theorem Cval_succ (m : ℕ) : Cval (m + 1) = Dval m := by
  unfold Cval Dval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({{0, 1}} : Finset (Finset (Fin 4))) →
        (¬Disjoint S {2, 3} ∨ wHoriz (Finset.univ \ (S ∪ {2, 3})) = 0) := by decide
  rw [sum_support m {2, 3} _ hsup]
  have hd0 : Disjoint ({0, 1} : Finset (Fin 4)) {2, 3} := by decide
  have hw0 : wHoriz (Finset.univ \ (({0, 1} : Finset (Fin 4)) ∪ {2, 3})) = 1 := by decide
  rw [Finset.sum_singleton]
  simp only [ite_eq_left hd0, hw0, mul_one]

private theorem Dval_succ (m : ℕ) : Dval (m + 1) = Aval m + Cval m := by
  unfold Dval Aval Cval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅, {2, 3}} : Finset (Finset (Fin 4))) →
        (¬Disjoint S {0, 1} ∨ wHoriz (Finset.univ \ (S ∪ {0, 1})) = 0) := by decide
  rw [sum_support m {0, 1} _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) {0, 1} := by decide
  have hd1 : Disjoint ({2, 3} : Finset (Fin 4)) {0, 1} := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ {0, 1})) = 1 := by decide
  have hw1 : wHoriz (Finset.univ \ (({2, 3} : Finset (Fin 4)) ∪ {0, 1})) = 1 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [ite_eq_left hd0, ite_eq_left hd1, hw0, hw1]
  ring

private theorem Eval_succ (m : ℕ) : Eval (m + 1) = Aval m := by
  unfold Eval Aval
  rw [Ncount_succ]
  have hsup : ∀ S : Finset (Fin 4),
      S ∉ ({∅} : Finset (Finset (Fin 4))) →
        (¬Disjoint S Finset.univ ∨ wHoriz (Finset.univ \ (S ∪ Finset.univ)) = 0) := by
    decide
  rw [sum_support m Finset.univ _ hsup]
  have hd0 : Disjoint (∅ : Finset (Fin 4)) Finset.univ := by decide
  have hw0 : wHoriz (Finset.univ \ ((∅ : Finset (Fin 4)) ∪ Finset.univ)) = 1 := by decide
  rw [Finset.sum_singleton]
  simp only [ite_eq_left hd0, hw0, mul_one]

private theorem Aval_zero : Aval 0 = 1 := by decide
private theorem Bval_zero : Bval 0 = 0 := by decide
private theorem Cval_zero : Cval 0 = 0 := by decide
private theorem Dval_zero : Dval 0 = 0 := by decide
private theorem Eval_zero : Eval 0 = 0 := by decide

private theorem Aval_recurrence (m : ℕ) :
    ((Aval (m + 4) : ℕ) : ℤ) = 2 * (Aval (m + 3) : ℤ) + 7 * (Aval (m + 2) : ℤ)
      + 2 * (Aval (m + 1) : ℤ) - (Aval m : ℤ) := by
  have hA0 : Aval (m + 1) = 2 * Aval m + Bval m + Dval m + Eval m := Aval_succ m
  have hA1 : Aval (m + 2) = 2 * Aval (m + 1) + Bval (m + 1) + Dval (m + 1) + Eval (m + 1) :=
    Aval_succ (m + 1)
  have hA2 : Aval (m + 3) = 2 * Aval (m + 2) + Bval (m + 2) + Dval (m + 2) + Eval (m + 2) :=
    Aval_succ (m + 2)
  have hA3 : Aval (m + 4) = 2 * Aval (m + 3) + Bval (m + 3) + Dval (m + 3) + Eval (m + 3) :=
    Aval_succ (m + 3)
  have hB0 : Bval (m + 1) = 4 * Aval m + Bval m := Bval_succ m
  have hB1 : Bval (m + 2) = 4 * Aval (m + 1) + Bval (m + 1) := Bval_succ (m + 1)
  have hB2 : Bval (m + 3) = 4 * Aval (m + 2) + Bval (m + 2) := Bval_succ (m + 2)
  have hC0 : Cval (m + 1) = Dval m := Cval_succ m
  have hC1 : Cval (m + 2) = Dval (m + 1) := Cval_succ (m + 1)
  have hC2 : Cval (m + 3) = Dval (m + 2) := Cval_succ (m + 2)
  have hD0 : Dval (m + 1) = Aval m + Cval m := Dval_succ m
  have hD1 : Dval (m + 2) = Aval (m + 1) + Cval (m + 1) := Dval_succ (m + 1)
  have hD2 : Dval (m + 3) = Aval (m + 2) + Cval (m + 2) := Dval_succ (m + 2)
  have hE0 : Eval (m + 1) = Aval m := Eval_succ m
  have hE1 : Eval (m + 2) = Aval (m + 1) := Eval_succ (m + 1)
  have hE2 : Eval (m + 3) = Aval (m + 2) := Eval_succ (m + 2)
  omega

private theorem Aval_one : Aval 1 = 2 := by
  have hA0 : Aval 1 = 2 * Aval 0 + Bval 0 + Dval 0 + Eval 0 := Aval_succ 0
  have ha0 := Aval_zero
  have hb0 := Bval_zero
  have hd0 := Dval_zero
  have he0 := Eval_zero
  omega

private theorem Aval_two : Aval 2 = 10 := by
  have hA0 : Aval 1 = 2 * Aval 0 + Bval 0 + Dval 0 + Eval 0 := Aval_succ 0
  have hA1 : Aval 2 = 2 * Aval 1 + Bval 1 + Dval 1 + Eval 1 := Aval_succ 1
  have hB0 : Bval 1 = 4 * Aval 0 + Bval 0 := Bval_succ 0
  have hD0 : Dval 1 = Aval 0 + Cval 0 := Dval_succ 0
  have hE0 : Eval 1 = Aval 0 := Eval_succ 0
  have ha0 := Aval_zero
  have hb0 := Bval_zero
  have hc0 := Cval_zero
  have hd0 := Dval_zero
  have he0 := Eval_zero
  omega

private theorem Aval_three : Aval 3 = 36 := by
  have hA0 : Aval 1 = 2 * Aval 0 + Bval 0 + Dval 0 + Eval 0 := Aval_succ 0
  have hA1 : Aval 2 = 2 * Aval 1 + Bval 1 + Dval 1 + Eval 1 := Aval_succ 1
  have hA2 : Aval 3 = 2 * Aval 2 + Bval 2 + Dval 2 + Eval 2 := Aval_succ 2
  have hB0 : Bval 1 = 4 * Aval 0 + Bval 0 := Bval_succ 0
  have hB1 : Bval 2 = 4 * Aval 1 + Bval 1 := Bval_succ 1
  have hC0 : Cval 1 = Dval 0 := Cval_succ 0
  have hD0 : Dval 1 = Aval 0 + Cval 0 := Dval_succ 0
  have hD1 : Dval 2 = Aval 1 + Cval 1 := Dval_succ 1
  have hE0 : Eval 1 = Aval 0 := Eval_succ 0
  have hE1 : Eval 2 = Aval 1 := Eval_succ 1
  have ha0 := Aval_zero
  have hb0 := Bval_zero
  have hc0 := Cval_zero
  have hd0 := Dval_zero
  have he0 := Eval_zero
  omega

private theorem Aval_eq_dval : ∀ m : ℕ, Aval m = dval m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : m < 4
    · have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · have ha := Aval_zero
        have hd := dval_vals.1
        omega
      · have ha := Aval_one
        have hd := dval_vals.2.1
        omega
      · have ha := Aval_two
        have hd := dval_vals.2.2.1
        omega
      · have ha := Aval_three
        have hd := dval_vals.2.2.2
        omega
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      have ih0 := ih k (by omega)
      have ih1 := ih (k + 1) (by omega)
      have ih2 := ih (k + 2) (by omega)
      have ih3 := ih (k + 3) (by omega)
      have hA := Aval_recurrence k
      have hD := dval_recurrence k
      have hz : ((Aval (k + 4) : ℕ) : ℤ) = ((dval (k + 4) : ℕ) : ℤ) := by omega
      exact_mod_cast hz

-- Partner function of a perfect matching.
private noncomputable def partner (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : Fin 4 × Fin m → Fin 4 × Fin m :=
  fun v => Classical.choose ((Subgraph.isPerfectMatching_iff.mp hM v).exists)

private theorem partner_spec (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v : Fin 4 × Fin m) :
    M.Adj v (partner m M hM v) := by
  unfold partner
  exact Classical.choose_spec _

private theorem partner_unique (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v w : Fin 4 × Fin m) (h : M.Adj v w) :
    w = partner m M hM v := by
  have hex := Subgraph.isPerfectMatching_iff.mp hM v
  exact hex.unique h (partner_spec m M hM v)

private theorem partner_classify (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i : Fin m) :
    let p := partner m M hM (a, i)
    (W4.Adj a p.1 ∧ i = p.2) ∨ (pathGraph m).Adj i p.2 ∧ a = p.1 := by
  have hadj := partner_spec m M hM (a, i)
  have hg := M.adj_sub hadj
  rw [boxProd_adj] at hg
  exact hg

private theorem partner_symm (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v : Fin 4 × Fin m) :
    partner m M hM (partner m M hM v) = v := by
  have h1 := partner_spec m M hM v
  have h2 := h1.symm
  have h3 := partner_unique m M hM (partner m M hM v) v h2
  exact h3.symm

-- Vertical edges at boundary `j` (between layers `j` and `j+1`), seen from below.
private noncomputable def vertSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun a =>
    ∃ i k : Fin m, i.val = j ∧ k.val = j + 1 ∧ partner m M hM (a, i) = (a, k))

private theorem vertSet_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (a : Fin 4) :
    a ∈ vertSet m M hM j ↔
      ∃ i k : Fin m, i.val = j ∧ k.val = j + 1 ∧ partner m M hM (a, i) = (a, k) := by
  unfold vertSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem partner_pair_symm (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i k : Fin m)
    (heq : partner m M hM (a, i) = (a, k)) :
    partner m M hM (a, k) = (a, i) := by
  have hps := partner_symm m M hM (a, i)
  rw [heq] at hps
  exact hps

-- Horizontal partner within layer `j`, or `a` itself if matched vertically.
private noncomputable def horizFunNat (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Fin 4 → Fin 4 :=
  fun a =>
    if h : j < m then
      let i : Fin m := ⟨j, h⟩
      let p := partner m M hM (a, i)
      if p.2 = i then p.1 else a
    else a

private theorem pathGraph_irrefl (m : ℕ) (i : Fin m) : ¬(pathGraph m).Adj i i := by
  rw [pathGraph_adj]
  omega

private theorem partner_same_layer_horiz (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i : Fin m)
    (h : (partner m M hM (a, i)).2 = i) : W4.Adj a (partner m M hM (a, i)).1 := by
  have hc := partner_classify m M hM a i
  simp only at hc
  rcases hc with ⟨hW, -⟩ | ⟨hpath, -⟩
  · exact hW
  · rw [h] at hpath
    exact absurd hpath (pathGraph_irrefl m i)

private theorem partner_ne_layer_vert (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i : Fin m)
    (h : (partner m M hM (a, i)).2 ≠ i) :
    (partner m M hM (a, i)).1 = a ∧ (pathGraph m).Adj i (partner m M hM (a, i)).2 := by
  have hc := partner_classify m M hM a i
  simp only at hc
  rcases hc with ⟨-, heq⟩ | ⟨hpath, haeq⟩
  · exact absurd heq.symm h
  · exact ⟨haeq.symm, hpath⟩

private noncomputable def belowSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ℕ → Finset (Fin 4)
  | 0 => ∅
  | (j + 1) => vertSet m M hM j

private noncomputable def aboveSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  vertSet m M hM j

private noncomputable def leftoverSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  Finset.univ \ (belowSet m M hM j ∪ aboveSet m M hM j)

private theorem above_mem_up (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (hmem : a ∈ aboveSet m M hM j) :
    ∃ k : Fin m, k.val = j + 1 ∧ partner m M hM (a, ⟨j, hj⟩) = (a, k) := by
  unfold aboveSet at hmem
  rw [vertSet_mem] at hmem
  obtain ⟨i, k, hi, hk, heq⟩ := hmem
  have hieq : i = (⟨j, hj⟩ : Fin m) := Fin.ext hi
  rw [hieq] at heq
  exact ⟨k, hk, heq⟩

private theorem below_mem_down (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (hj0 : j ≠ 0) (a : Fin 4)
    (hmem : a ∈ belowSet m M hM j) :
    ∃ k : Fin m, k.val + 1 = j ∧ partner m M hM (a, ⟨j, hj⟩) = (a, k) := by
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  change a ∈ vertSet m M hM j' at hmem
  rw [vertSet_mem] at hmem
  obtain ⟨i, k, hi, hk, heq⟩ := hmem
  have hkeq : k = (⟨j' + 1, hj⟩ : Fin m) := by
    apply Fin.ext
    change k.val = j' + 1
    omega
  have hsym := partner_pair_symm m M hM a i k heq
  rw [hkeq] at hsym
  exact ⟨i, by omega, hsym⟩

private theorem below_above_disjoint (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    Disjoint (belowSet m M hM j) (aboveSet m M hM j) := by
  rw [Finset.disjoint_left]
  intro a hb ha
  by_cases hj0 : j = 0
  · subst hj0
    unfold belowSet at hb
    exact (Finset.notMem_empty a) hb
  · obtain ⟨k1, hk1, heq1⟩ := above_mem_up m M hM j hj a ha
    obtain ⟨k2, hk2, heq2⟩ := below_mem_down m M hM j hj hj0 a hb
    have heq : (a, k1) = (a, k2) := heq1.symm.trans heq2
    have hkk : k1 = k2 := congrArg Prod.snd heq
    have hval : k1.val = k2.val := congrArg Fin.val hkk
    omega

private theorem leftover_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (a : Fin 4) :
    a ∈ leftoverSet m M hM j ↔ a ∉ (belowSet m M hM j ∪ aboveSet m M hM j) := by
  unfold leftoverSet
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]

private theorem leftover_not_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (a : Fin 4) :
    a ∉ leftoverSet m M hM j ↔ a ∈ (belowSet m M hM j ∪ aboveSet m M hM j) := by
  unfold leftoverSet
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

private theorem not_mem_union_same_layer (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (h : a ∉ (belowSet m M hM j ∪ aboveSet m M hM j)) :
    (partner m M hM (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ := by
  by_contra hne
  have ⟨haeq, hpath⟩ := partner_ne_layer_vert m M hM a ⟨j, hj⟩ hne
  have hpeq : partner m M hM (a, ⟨j, hj⟩) = (a, (partner m M hM (a, ⟨j, hj⟩)).2) := by
    ext
    · simp only [haeq]
    · rfl
  rw [pathGraph_adj] at hpath
  have hupdown : j + 1 = (partner m M hM (a, ⟨j, hj⟩)).2.val ∨
      (partner m M hM (a, ⟨j, hj⟩)).2.val + 1 = j := hpath
  rcases hupdown with hup | hdown
  · have hmem : a ∈ aboveSet m M hM j := by
      unfold aboveSet
      rw [vertSet_mem]
      exact ⟨⟨j, hj⟩, (partner m M hM (a, ⟨j, hj⟩)).2, rfl, hup.symm, hpeq⟩
    have : a ∈ (belowSet m M hM j ∪ aboveSet m M hM j) :=
      Finset.mem_union_right _ hmem
    exact h this
  · by_cases hj0 : j = 0
    · subst hj0
      omega
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hmem : a ∈ belowSet m M hM j'.succ := by
        change a ∈ vertSet m M hM j'
        rw [vertSet_mem]
        have hsym := partner_pair_symm m M hM a ⟨j'.succ, hj⟩
          (partner m M hM (a, ⟨j'.succ, hj⟩)).2 hpeq
        refine ⟨(partner m M hM (a, ⟨j'.succ, hj⟩)).2, ⟨j'.succ, hj⟩, ?_, rfl, hsym⟩
        · omega
      have : a ∈ (belowSet m M hM j'.succ ∪ aboveSet m M hM j'.succ) :=
        Finset.mem_union_left _ hmem
      exact h this

private theorem horizFunNat_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4) :
    horizFunNat m M hM j a =
      (if (partner m M hM (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ then
        (partner m M hM (a, ⟨j, hj⟩)).1 else a) := by
  unfold horizFunNat
  simp only [dite_eq_left hj]

private theorem horizFunNat_of_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (hmem : a ∈ leftoverSet m M hM j) :
    horizFunNat m M hM j a = (partner m M hM (a, ⟨j, hj⟩)).1 := by
  rw [horizFunNat_eq m M hM j hj a]
  have hnot : a ∉ (belowSet m M hM j ∪ aboveSet m M hM j) :=
    (leftover_mem m M hM j a).mp hmem
  have hsame := not_mem_union_same_layer m M hM j hj a hnot
  simp only [ite_eq_left hsame]

private theorem horizFunNat_of_not_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (hmem : a ∉ leftoverSet m M hM j) : horizFunNat m M hM j a = a := by
  rw [horizFunNat_eq m M hM j hj a]
  have hmemK : a ∈ (belowSet m M hM j ∪ aboveSet m M hM j) :=
    (leftover_not_mem m M hM j a).mp hmem
  have hne : (partner m M hM (a, ⟨j, hj⟩)).2 ≠ ⟨j, hj⟩ := by
    rw [Finset.mem_union] at hmemK
    rcases hmemK with hb | ha
    · by_cases hj0 : j = 0
      · subst hj0
        unfold belowSet at hb
        exact absurd hb (Finset.notMem_empty a)
      · obtain ⟨k, hk, heq⟩ := below_mem_down m M hM j hj hj0 a hb
        intro hcon
        have h1 : (partner m M hM (a, ⟨j, hj⟩)).2 = k := congrArg Prod.snd heq
        have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans hcon
        have hval : k.val = j := congrArg Fin.val hkk
        omega
    · obtain ⟨k, hk, heq⟩ := above_mem_up m M hM j hj a ha
      intro hcon
      have h1 : (partner m M hM (a, ⟨j, hj⟩)).2 = k := congrArg Prod.snd heq
      have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans hcon
      have hval : k.val = j := congrArg Fin.val hkk
      omega
  simp only [ite_eq_right hne]

private noncomputable def horizPairingOf (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    HorizPairing (leftoverSet m M hM j) := by
  refine ⟨horizFunNat m M hM j, ?_, ?_⟩
  · intro a hmem
    have hnot : a ∉ (belowSet m M hM j ∪ aboveSet m M hM j) :=
      (leftover_mem m M hM j a).mp hmem
    have hsame := not_mem_union_same_layer m M hM j hj a hnot
    have hfa : horizFunNat m M hM j a = (partner m M hM (a, ⟨j, hj⟩)).1 :=
      horizFunNat_of_mem m M hM j hj a hmem
    have hW : W4.Adj a (partner m M hM (a, ⟨j, hj⟩)).1 :=
      partner_same_layer_horiz m M hM a ⟨j, hj⟩ hsame
    have hW' : W4.Adj a (horizFunNat m M hM j a) := by rw [hfa]; exact hW
    have hne : a ≠ horizFunNat m M hM j a := ((W4_adj a _).mp hW').1
    have hne' : horizFunNat m M hM j a ≠ a := Ne.symm hne
    have hpeq : partner m M hM (a, ⟨j, hj⟩) =
        (horizFunNat m M hM j a, ⟨j, hj⟩) :=
      Prod.ext hfa.symm hsame
    have hsym : partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩) = (a, ⟨j, hj⟩) := by
      have hps := partner_symm m M hM (a, ⟨j, hj⟩)
      rw [hpeq] at hps
      exact hps
    have hbmem : horizFunNat m M hM j a ∈ leftoverSet m M hM j := by
      rw [leftover_mem]
      intro hcon
      rw [Finset.mem_union] at hcon
      rcases hcon with hb | ha
      · by_cases hj0 : j = 0
        · subst hj0
          unfold belowSet at hb
          exact (Finset.notMem_empty _) hb
        · obtain ⟨k, hk, heq⟩ := below_mem_down m M hM j hj hj0 _ hb
          have h1 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = k :=
            congrArg Prod.snd heq
          have h2 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ :=
            congrArg Prod.snd hsym
          have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans h2
          have hval : k.val = j := congrArg Fin.val hkk
          omega
      · obtain ⟨k, hk, heq⟩ := above_mem_up m M hM j hj _ ha
        have h1 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = k :=
          congrArg Prod.snd heq
        have h2 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ :=
          congrArg Prod.snd hsym
        have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans h2
        have hval : k.val = j := congrArg Fin.val hkk
        omega
    have hfb : horizFunNat m M hM j (horizFunNat m M hM j a) = a := by
      have hfb' : horizFunNat m M hM j (horizFunNat m M hM j a) =
          (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).1 :=
        horizFunNat_of_mem m M hM j hj _ hbmem
      rw [hfb']
      have : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).1 = a :=
        congrArg Prod.fst hsym
      exact this
    exact ⟨hbmem, hfb, hne', hW'⟩
  · intro a hmem
    exact horizFunNat_of_not_mem m M hM j hj a hmem

-- Top holes for the prefix of length `k`: empty at 0, else the boundary below.
private noncomputable def topHoles (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ℕ → Finset (Fin 4)
  | 0 => ∅
  | (k + 1) => vertSet m M hM k

private theorem below_eq_topHoles (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (k : ℕ) :
    belowSet m M hM k = topHoles m M hM k :=
  rfl

private theorem above_eq_topHoles_succ (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (k : ℕ) :
    aboveSet m M hM k = topHoles m M hM (k + 1) := by
  unfold aboveSet topHoles
  rfl

private theorem vertSet_top_empty (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : m ≤ j + 1) :
    vertSet m M hM j = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a hmem
  rw [vertSet_mem] at hmem
  obtain ⟨i, k, hi, hk, -⟩ := hmem
  have hlt : k.val < m := k.isLt
  omega

private noncomputable def buildTiling (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ∀ k : ℕ, k ≤ m → Tiling k (topHoles m M hM k)
  | 0, _ => ⟨rfl⟩
  | (k + 1), hk =>
    have hk' : k ≤ m := by omega
    have hkm : k < m := by omega
    have ih := buildTiling m M hM k hk'
    have hdisj : Disjoint (topHoles m M hM k) (topHoles m M hM (k + 1)) :=
      below_above_disjoint m M hM k hkm
    have hhor : HorizPairing (Finset.univ \ (topHoles m M hM k ∪ topHoles m M hM (k + 1))) :=
      horizPairingOf m M hM k hkm
    ⟨topHoles m M hM k, ⟨hdisj⟩, ih, hhor⟩

private noncomputable def fwdTiling (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : Tiling m ∅ := by
  cases m with
  | zero =>
    have htop : topHoles 0 M hM 0 = ∅ := rfl
    exact htop.rec (buildTiling 0 M hM 0 (by omega))
  | succ m =>
    have htop : topHoles (m + 1) M hM (m + 1) = ∅ := by
      change vertSet (m + 1) M hM m = ∅
      apply vertSet_top_empty
      omega
    exact htop.rec (buildTiling (m + 1) M hM (m + 1) (by omega))

-- Unpack vertical boundaries from a tiling: above of layer `j`.
private def getS : ∀ (m : ℕ) (S' : Finset (Fin 4)), Tiling m S' → ℕ → Finset (Fin 4)
  | 0, _, _, _ => ∅
  | (m + 1), S', ⟨S, _, t, _⟩, j => if j = m then S' else getS m S t j

-- Unpack horizontal functions from a tiling.
private def getF : ∀ (m : ℕ) (S' : Finset (Fin 4)), Tiling m S' → ℕ → (Fin 4 → Fin 4)
  | 0, _, _, _ => id
  | (m + 1), _, ⟨_, _, t, h⟩, j => if j = m then h.val else getF m _ t j

private theorem getS_top (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S') :
    getS (m + 1) S' t m = S' := by
  cases t with
  | mk S snd =>
    cases snd with
    | mk _ rest =>
      simp only [getS, ite_true]

private theorem getS_recurse (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S')
    (j : ℕ) (hj : j ≠ m) :
    getS (m + 1) S' t j = getS m (t.1) (t.2.2.1) j := by
  cases t with
  | mk S snd =>
    cases snd with
    | mk _ rest =>
      cases rest with
      | mk t _ =>
        simp only [getS, ite_eq_right hj]

private theorem getF_top (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S') :
    getF (m + 1) S' t m = (t.2.2.2).val := by
  cases t with
  | mk _ snd =>
    cases snd with
    | mk _ rest =>
      cases rest with
      | mk _ h =>
        simp only [getF, ite_true]

private theorem getF_recurse (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling (m + 1) S')
    (j : ℕ) (hj : j ≠ m) :
    getF (m + 1) S' t j = getF m (t.1) (t.2.2.1) j := by
  cases t with
  | mk _ snd =>
    cases snd with
    | mk _ rest =>
      cases rest with
      | mk t _ =>
        simp only [getF, ite_eq_right hj]

private def HorizProps (f : Fin 4 → Fin 4) (U : Finset (Fin 4)) : Prop :=
  (∀ a ∈ U, f a ∈ U ∧ f (f a) = a ∧ f a ≠ a ∧ W4.Adj a (f a)) ∧ ∀ a ∉ U, f a = a

private theorem horizPairing_props (U : Finset (Fin 4)) (h : HorizPairing U) :
    HorizProps h.val U :=
  h.property

private theorem tiling_props : ∀ (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling m S')
    (j : ℕ) (_hj : j < m),
    Disjoint (if j = 0 then ∅ else getS m S' t (j - 1)) (getS m S' t j) ∧
    HorizProps (getF m S' t j)
      (Finset.univ \ ((if j = 0 then ∅ else getS m S' t (j - 1)) ∪ getS m S' t j)) := by
  intro m
  induction m with
  | zero =>
    intro S' t j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro S' t j _hj
    cases t with
    | mk S snd =>
      cases snd with
      | mk hd rest =>
        cases rest with
        | mk tm h =>
          by_cases hjm : j = m
          · rw [hjm]
            have hSe : getS (m + 1) S' ⟨S, hd, tm, h⟩ m = S' := by
              simp only [getS, ite_true]
            have hFe : getF (m + 1) S' ⟨S, hd, tm, h⟩ m = h.val := by
              simp only [getF, ite_true]
            have hbelow : (if m = 0 then ∅ else getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1)) = S := by
              by_cases hm0 : m = 0
              · subst hm0
                simp only [ite_true]
                have : S = ∅ := tm.down
                exact this.symm
              · have h1 : (if m = 0 then ∅ else getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1)) =
                    getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1) := by
                  simp only [ite_eq_right hm0]
                rw [h1]
                have hne : m - 1 ≠ m := by omega
                have h2 : getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1) = getS m S tm (m - 1) := by
                  simp only [getS, ite_eq_right hne]
                rw [h2]
                cases m with
                | zero => exact absurd rfl hm0
                | succ m' =>
                  have hsub : m' + 1 - 1 = m' := rfl
                  rw [hsub]
                  have : getS (m' + 1) S tm m' = S := by
                    cases tm with
                    | mk _ _ =>
                      simp only [getS, ite_true]
                  exact this
            rw [hbelow, hSe, hFe]
            have hU : Finset.univ \ (S ∪ S') = Finset.univ \ (S ∪ S') := rfl
            refine ⟨?_, ?_⟩
            · have : Disjoint S S' := hd.down
              exact this
            · have hp := h.property
              exact hp
          · have hjm' : j < m := by omega
            have hSj : getS (m + 1) S' ⟨S, hd, tm, h⟩ j = getS m S tm j := by
              simp only [getS, ite_eq_right hjm]
            have hFj : getF (m + 1) S' ⟨S, hd, tm, h⟩ j = getF m S tm j := by
              simp only [getF, ite_eq_right hjm]
            have hSlow : (if j = 0 then ∅ else getS (m + 1) S' ⟨S, hd, tm, h⟩ (j - 1)) =
                (if j = 0 then ∅ else getS m S tm (j - 1)) := by
              by_cases hj0 : j = 0
              · simp only [hj0, ite_true]
              · have hne : j - 1 ≠ m := by omega
                simp only [ite_eq_right hj0]
                have : getS (m + 1) S' ⟨S, hd, tm, h⟩ (j - 1) = getS m S tm (j - 1) := by
                  simp only [getS, ite_eq_right hne]
                rw [this]
            rw [hSlow, hSj, hFj]
            exact ih S tm j hjm'

private theorem getS_out_empty : ∀ (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling m S')
    (j : ℕ), m ≤ j → getS m S' t j = ∅
  | 0, _, _, _, _ => rfl
  | (m + 1), S', t, j, hj => by
    have hne : j ≠ m := by omega
    have hrec : getS (m + 1) S' t j = getS m (t.1) (t.2.2.1) j :=
      getS_recurse m S' t j hne
    rw [hrec]
    exact getS_out_empty m _ _ j (by omega)

private theorem getS_top_empty (m : ℕ) (t : Tiling (m + 1) ∅) :
    getS (m + 1) ∅ t m = ∅ :=
  getS_top m ∅ t

private theorem getS_pred_top_empty (m : ℕ) (t : Tiling m ∅) (hm : 0 < m) :
    getS m ∅ t (m - 1) = ∅ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsub : m' + 1 - 1 = m' := rfl
  rw [hsub]
  exact getS_top m' ∅ t

private noncomputable def partnerT (m : ℕ) (t : Tiling m ∅) :
    Fin 4 × Fin m → Fin 4 × Fin m :=
  fun v =>
    let a := v.1
    let i := v.2
    let j := i.val
    let above := getS m ∅ t j
    let below := if j = 0 then ∅ else getS m ∅ t (j - 1)
    if h_up : a ∈ above then
      have hj1 : j + 1 < m := by
        have hjlt : j < m := i.isLt
        by_cases hm0 : m = 0
        · subst hm0
          have hempty : above = ∅ := by
            unfold above
            have : getS 0 ∅ t j = ∅ := rfl
            exact this
          rw [hempty] at h_up
          exact absurd h_up (Finset.notMem_empty a)
        · by_contra hcon
          have hle : m ≤ j + 1 := by omega
          have heq : j + 1 = m := by omega
          have hjpred : j = m - 1 := by omega
          have hempty : above = ∅ := by
            unfold above
            rw [hjpred]
            exact getS_pred_top_empty m t (by omega)
          rw [hempty] at h_up
          exact absurd h_up (Finset.notMem_empty a)
      (a, ⟨j + 1, hj1⟩)
    else if h_down : a ∈ below then
      have hj0 : j ≠ 0 := by
        intro hcon
        have hbelow_eq : below = ∅ := by
          unfold below
          simp only [ite_eq_left hcon]
        rw [hbelow_eq] at h_down
        exact absurd h_down (Finset.notMem_empty a)
      have hj1 : j - 1 < m := by
        have : j < m := i.isLt
        omega
      (a, ⟨j - 1, hj1⟩)
    else
      (getF m ∅ t j a, i)

private theorem partnerT_up (m : ℕ) (t : Tiling m ∅) (a : Fin 4) (i : Fin m)
    (h : a ∈ getS m ∅ t i.val) :
    (partnerT m t (a, i)).1 = a ∧ (partnerT m t (a, i)).2.val = i.val + 1 := by
  have hup : a ∈ getS m ∅ t i.val := h
  unfold partnerT
  rw [dite_eq_left hup]
  refine ⟨rfl, rfl⟩

private theorem partnerT_down (m : ℕ) (t : Tiling m ∅) (a : Fin 4) (i : Fin m)
    (h1 : a ∉ getS m ∅ t i.val)
    (h2 : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))) :
    (partnerT m t (a, i)).1 = a ∧ (partnerT m t (a, i)).2.val + 1 = i.val := by
  unfold partnerT
  rw [dite_eq_right h1, dite_eq_left h2]
  have hj0 : i.val ≠ 0 := by
    intro hcon
    have hempty : (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) = ∅ := by
      simp only [ite_eq_left hcon]
    rw [hempty] at h2
    exact absurd h2 (Finset.notMem_empty a)
  refine ⟨rfl, ?_⟩
  change (i.val - 1) + 1 = i.val
  omega

private theorem partnerT_horiz (m : ℕ) (t : Tiling m ∅) (a : Fin 4) (i : Fin m)
    (h1 : a ∉ getS m ∅ t i.val)
    (h2 : a ∉ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))) :
    partnerT m t (a, i) = (getF m ∅ t i.val a, i) := by
  unfold partnerT
  rw [dite_eq_right h1, dite_eq_right h2]

private theorem mem_above_up_lt (m : ℕ) (t : Tiling m ∅) (j : ℕ) (hj : j < m)
    (a : Fin 4) (h : a ∈ getS m ∅ t j) : j + 1 < m := by
  by_cases hm0 : m = 0
  · subst hm0
    exact absurd hj (Nat.not_lt_zero j)
  · by_contra hcon
    have heq : j + 1 = m := by omega
    have hjpred : j = m - 1 := by omega
    have hempty : getS m ∅ t j = ∅ := by
      rw [hjpred]
      exact getS_pred_top_empty m t (by omega)
    rw [hempty] at h
    exact absurd h (Finset.notMem_empty a)

private theorem mem_below_ne_zero (m : ℕ) (t : Tiling m ∅) (j : ℕ) (a : Fin 4)
    (h : a ∈ (if j = 0 then ∅ else getS m ∅ t (j - 1))) : j ≠ 0 := by
  intro hcon
  have hempty : (if j = 0 then ∅ else getS m ∅ t (j - 1)) = ∅ := by
    simp only [ite_eq_left hcon]
  rw [hempty] at h
  exact absurd h (Finset.notMem_empty a)

private theorem partnerT_involutive (m : ℕ) (t : Tiling m ∅) :
    Function.Involutive (partnerT m t) := by
  intro v
  obtain ⟨a, i⟩ := v
  have hjlt : i.val < m := i.isLt
  by_cases h_up : a ∈ getS m ∅ t i.val
  · have hj1 : i.val + 1 < m := mem_above_up_lt m t i.val hjlt a h_up
    have hpu := partnerT_up m t a i h_up
    have hp_eq : partnerT m t (a, i) = (a, ⟨i.val + 1, hj1⟩) :=
      Prod.ext hpu.1 (Fin.ext hpu.2)
    rw [hp_eq]
    have hvalk : (⟨i.val + 1, hj1⟩ : Fin m).val = i.val + 1 := rfl
    have hnot_up : a ∉ getS m ∅ t (⟨i.val + 1, hj1⟩ : Fin m).val := by
      rw [hvalk]
      have hdisj := (tiling_props m ∅ t (i.val + 1) hj1).1
      have hbelow_eq : (if i.val + 1 = 0 then ∅ else getS m ∅ t (i.val + 1 - 1)) =
          getS m ∅ t i.val := by
        have hne : i.val + 1 ≠ 0 := Nat.succ_ne_zero i.val
        simp only [ite_eq_right hne]
        have hsub : i.val + 1 - 1 = i.val := rfl
        rw [hsub]
      rw [Finset.disjoint_left] at hdisj
      have hmem : a ∈ (if i.val + 1 = 0 then ∅ else getS m ∅ t (i.val + 1 - 1)) := by
        rw [hbelow_eq]
        exact h_up
      exact hdisj hmem
    have hdown_mem : a ∈ (if (⟨i.val + 1, hj1⟩ : Fin m).val = 0 then ∅ else
        getS m ∅ t ((⟨i.val + 1, hj1⟩ : Fin m).val - 1)) := by
      rw [hvalk]
      have hne : i.val + 1 ≠ 0 := Nat.succ_ne_zero i.val
      simp only [ite_eq_right hne]
      have hsub : i.val + 1 - 1 = i.val := rfl
      rw [hsub]
      exact h_up
    have hpd := partnerT_down m t a ⟨i.val + 1, hj1⟩ hnot_up hdown_mem
    have h1 : (partnerT m t (a, ⟨i.val + 1, hj1⟩)).1 = a := hpd.1
    have h2 : (partnerT m t (a, ⟨i.val + 1, hj1⟩)).2 = i := by
      apply Fin.ext
      have hval : (partnerT m t (a, ⟨i.val + 1, hj1⟩)).2.val + 1 =
          (⟨i.val + 1, hj1⟩ : Fin m).val := hpd.2
      rw [hvalk] at hval
      omega
    exact Prod.ext h1 h2
  · by_cases h_down : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))
    · have hj0 : i.val ≠ 0 := mem_below_ne_zero m t i.val a h_down
      have hpd := partnerT_down m t a i h_up h_down
      have hmemS : a ∈ getS m ∅ t (i.val - 1) := by
        have heq : (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) =
            getS m ∅ t (i.val - 1) := by
          simp only [ite_eq_right hj0]
        rw [heq] at h_down
        exact h_down
      have hkval : (partnerT m t (a, i)).2.val + 1 = i.val := hpd.2
      have h1k : (partnerT m t (a, i)).1 = a := hpd.1
      have hp_eq : partnerT m t (a, i) = (a, ⟨i.val - 1, by omega⟩) := by
        apply Prod.ext
        · exact h1k
        · apply Fin.ext
          change (partnerT m t (a, i)).2.val = i.val - 1
          omega
      rw [hp_eq]
      have hvalk : (⟨i.val - 1, by omega⟩ : Fin m).val = i.val - 1 := rfl
      have hup_mem : a ∈ getS m ∅ t (⟨i.val - 1, by omega⟩ : Fin m).val := by
        rw [hvalk]
        exact hmemS
      have hpu2 := partnerT_up m t a ⟨i.val - 1, by omega⟩ hup_mem
      have h1 : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).1 = a := hpu2.1
      have h2 : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2 = i := by
        apply Fin.ext
        have hval : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2.val =
            (⟨i.val - 1, by omega⟩ : Fin m).val + 1 := hpu2.2
        rw [hvalk] at hval
        have : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2.val = i.val := by omega
        calc (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2.val = i.val := this
          _ = i.val := rfl
      exact Prod.ext h1 h2
    · have hhor := partnerT_horiz m t a i h_up h_down
      rw [hhor]
      have hprops := (tiling_props m ∅ t i.val hjlt).2
      have hUmem : a ∈ Finset.univ \ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
          getS m ∅ t i.val) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
        exact fun hcon => hcon.elim h_down h_up
      obtain ⟨hbmem, hinv, _, _⟩ := hprops.1 a hUmem
      have hbmem' : getF m ∅ t i.val a ∉
          ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪ getS m ∅ t i.val) := by
        have : getF m ∅ t i.val a ∈ Finset.univ \ ((if i.val = 0 then ∅ else
            getS m ∅ t (i.val - 1)) ∪ getS m ∅ t i.val) := hbmem
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
        exact this
      have hup2 : getF m ∅ t i.val a ∉ getS m ∅ t i.val := by
        intro hcon
        have : getF m ∅ t i.val a ∈ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
            getS m ∅ t i.val) := Finset.mem_union_right _ hcon
        exact absurd this hbmem'
      have hdown2 : getF m ∅ t i.val a ∉
          (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) := by
        intro hcon
        have : getF m ∅ t i.val a ∈ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
            getS m ∅ t i.val) := Finset.mem_union_left _ hcon
        exact absurd this hbmem'
      have hhor2 := partnerT_horiz m t (getF m ∅ t i.val a) i hup2 hdown2
      rw [hhor2]
      have : getF m ∅ t i.val (getF m ∅ t i.val a) = a := hinv
      simp only [this]

private theorem partnerT_adj (m : ℕ) (t : Tiling m ∅) (v : Fin 4 × Fin m) :
    (W4 □ pathGraph m).Adj v (partnerT m t v) := by
  obtain ⟨a, i⟩ := v
  have hjlt : i.val < m := i.isLt
  by_cases h_up : a ∈ getS m ∅ t i.val
  · have hpu := partnerT_up m t a i h_up
    have hp_eq : partnerT m t (a, i) = (a, ⟨i.val + 1, mem_above_up_lt m t i.val hjlt a h_up⟩) :=
      Prod.ext hpu.1 (Fin.ext hpu.2)
    rw [hp_eq, boxProd_adj]
    refine Or.inr ⟨?_, rfl⟩
    rw [pathGraph_adj]
    exact Or.inl rfl
  · by_cases h_down : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))
    · have hpd := partnerT_down m t a i h_up h_down
      have hj0 : i.val ≠ 0 := mem_below_ne_zero m t i.val a h_down
      have hp_eq : partnerT m t (a, i) = (a, ⟨i.val - 1, by omega⟩) := by
        apply Prod.ext
        · exact hpd.1
        · apply Fin.ext
          change (partnerT m t (a, i)).2.val = i.val - 1
          omega
      rw [hp_eq, boxProd_adj]
      refine Or.inr ⟨?_, rfl⟩
      rw [pathGraph_adj]
      have hval : (⟨i.val - 1, by omega⟩ : Fin m).val + 1 = i.val := by
        change (i.val - 1) + 1 = i.val
        omega
      exact Or.inr hval
    · have hhor := partnerT_horiz m t a i h_up h_down
      rw [hhor, boxProd_adj]
      refine Or.inl ⟨?_, rfl⟩
      have hprops := (tiling_props m ∅ t i.val hjlt).2
      have hUmem : a ∈ Finset.univ \ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
          getS m ∅ t i.val) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
        exact fun hcon => hcon.elim h_down h_up
      obtain ⟨_, _, _, hW⟩ := hprops.1 a hUmem
      exact hW

private noncomputable def bwdSubgraph (m : ℕ) (t : Tiling m ∅) :
    (W4 □ pathGraph m).Subgraph where
  verts := Set.univ
  Adj v w := w = partnerT m t v
  adj_sub h := by
    rw [h]
    exact partnerT_adj _ _ _
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun {v w} h => by
    have hinv := partnerT_involutive m t v
    have h2 : partnerT m t w = v := by
      rw [h]
      exact hinv
    exact h2.symm⟩

private theorem bwdSubgraph_perfect (m : ℕ) (t : Tiling m ∅) :
    (bwdSubgraph m t).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  exact ⟨partnerT m t v, rfl, fun w hw => hw⟩

private noncomputable def bwdTiling (m : ℕ) (t : Tiling m ∅) :
    { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } :=
  ⟨bwdSubgraph m t, bwdSubgraph_perfect m t⟩

private theorem partner_bwd_eq (m : ℕ) (t : Tiling m ∅) (v : Fin 4 × Fin m) :
    partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t) v = partnerT m t v := by
  have hAdj : (bwdSubgraph m t).Adj v (partnerT m t v) := rfl
  have huniq := partner_unique m (bwdSubgraph m t) (bwdSubgraph_perfect m t) v
    (partnerT m t v) hAdj
  exact huniq.symm

private theorem getS_build_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ∀ (k : ℕ) (hk : k ≤ m) (j : ℕ) (_hj : j < k),
    getS k (topHoles m M hM k) (buildTiling m M hM k hk) j = vertSet m M hM j := by
  intro k
  induction k with
  | zero =>
    intro hk j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro hk j _hj
    by_cases hjm : j = k
    · rw [hjm]
      have htop : getS (k + 1) (topHoles m M hM (k + 1))
          (buildTiling m M hM (k + 1) hk) k = topHoles m M hM (k + 1) := by
        have := getS_top k (topHoles m M hM (k + 1)) (buildTiling m M hM (k + 1) hk)
        exact this
      rw [htop]
      rfl
    · have hjk : j < k := by omega
      have hk' : k ≤ m := by omega
      have hrec : getS (k + 1) (topHoles m M hM (k + 1))
          (buildTiling m M hM (k + 1) hk) j =
          getS k ((buildTiling m M hM (k + 1) hk).1)
            ((buildTiling m M hM (k + 1) hk).2.2.1) j :=
        getS_recurse k _ _ j hjm
      rw [hrec]
      exact ih hk' j hjk

private theorem vertSet_bwd_eq (m : ℕ) (t : Tiling m ∅) (j : ℕ) :
    vertSet m (bwdSubgraph m t) (bwdSubgraph_perfect m t) j = getS m ∅ t j := by
  ext a
  rw [vertSet_mem]
  constructor
  · rintro ⟨i, k, hi, hk, heq⟩
    have hpeq := partner_bwd_eq m t (a, i)
    rw [hpeq] at heq
    have hjlt : j < m := by omega
    have hup : a ∈ getS m ∅ t j := by
      have h2 : (partnerT m t (a, i)).2 = k := congrArg Prod.snd heq
      have hkval : k.val = j + 1 := hk
      have hival : i.val = j := hi
      have hpval : (partnerT m t (a, i)).2.val = j + 1 := by
        rw [h2, hkval]
      by_cases hmem : a ∈ getS m ∅ t i.val
      · have : i.val = j := hival
        rw [this] at hmem
        exact hmem
      · by_cases hdown : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))
        · have hpd := partnerT_down m t a i hmem hdown
          have : (partnerT m t (a, i)).2.val + 1 = i.val := hpd.2
          omega
        · have hhor := partnerT_horiz m t a i hmem hdown
          have : (partnerT m t (a, i)).2 = i := congrArg Prod.snd hhor
          have : (partnerT m t (a, i)).2.val = i.val := congrArg Fin.val this
          omega
    exact hup
  · intro hmem
    have hjlt : j < m := by
      by_contra hcon
      have hle : m ≤ j := by omega
      have hempty : getS m ∅ t j = ∅ := getS_out_empty m ∅ t j hle
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty a)
    have hj1 : j + 1 < m := mem_above_up_lt m t j hjlt a hmem
    refine ⟨⟨j, hjlt⟩, ⟨j + 1, hj1⟩, rfl, rfl, ?_⟩
    have hpeq := partner_bwd_eq m t (a, ⟨j, hjlt⟩)
    rw [hpeq]
    have hpu := partnerT_up m t a ⟨j, hjlt⟩ hmem
    have h1 : (partnerT m t (a, ⟨j, hjlt⟩)).1 = a := hpu.1
    have h2 : (partnerT m t (a, ⟨j, hjlt⟩)).2.val = j + 1 := hpu.2
    have h3 : (partnerT m t (a, ⟨j, hjlt⟩)).2 = (⟨j + 1, hj1⟩ : Fin m) := Fin.ext h2
    exact Prod.ext h1 h3

private theorem getF_build_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ∀ (k : ℕ) (hk : k ≤ m) (j : ℕ) (_hj : j < k),
    getF k (topHoles m M hM k) (buildTiling m M hM k hk) j = horizFunNat m M hM j := by
  intro k
  induction k with
  | zero =>
    intro hk j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro hk j _hj
    by_cases hjm : j = k
    · rw [hjm]
      have htop : getF (k + 1) (topHoles m M hM (k + 1))
          (buildTiling m M hM (k + 1) hk) k =
          ((buildTiling m M hM (k + 1) hk).2.2.2).val :=
        getF_top k _ _
      rw [htop]
      rfl
    · have hjk : j < k := by omega
      have hk' : k ≤ m := by omega
      have hrec : getF (k + 1) (topHoles m M hM (k + 1))
          (buildTiling m M hM (k + 1) hk) j =
          getF k ((buildTiling m M hM (k + 1) hk).1)
            ((buildTiling m M hM (k + 1) hk).2.2.1) j :=
        getF_recurse k _ _ j hjm
      rw [hrec]
      exact ih hk' j hjk

private theorem tiling_ext_of_getSF_eq (m : ℕ) (S' : Finset (Fin 4))
    (t1 t2 : Tiling m S')
    (hS : ∀ j, j < m → getS m S' t1 j = getS m S' t2 j)
    (hF : ∀ j, j < m → getF m S' t1 j = getF m S' t2 j) :
    t1 = t2 := by
  induction m generalizing S' with
  | zero =>
    cases t1
    cases t2
    rfl
  | succ m ih =>
    obtain ⟨S1, hd1, tm1, h1⟩ := t1
    obtain ⟨S2, hd2, tm2, h2⟩ := t2
    cases m with
    | zero =>
      have e1 : S1 = ∅ := tm1.down
      have e2 : S2 = ∅ := tm2.down
      have hSeq : S1 = S2 := e1.trans e2.symm
      subst hSeq
      have htm : tm1 = tm2 := by
        cases tm1
        cases tm2
        rfl
      subst htm
      have eF := hF 0 (by omega)
      have g1 : getF (0 + 1) S' ⟨S1, hd1, tm1, h1⟩ 0 = h1.val :=
        getF_top 0 S' _
      have g2 : getF (0 + 1) S' ⟨S1, hd2, tm1, h2⟩ 0 = h2.val :=
        getF_top 0 S' _
      have hval : h1.val = h2.val := g1.symm.trans (eF.trans g2)
      have hh : h1 = h2 := Subtype.ext hval
      subst hh
      have hhd : hd1 = hd2 := by
        cases hd1
        cases hd2
        rfl
      cases hhd
      rfl
    | succ m' =>
      have eS := hS m' (by omega)
      have r1 : getS ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ m' =
          getS (m' + 1) S1 tm1 m' :=
        getS_recurse (m' + 1) S' _ m' (by omega)
      have r2 : getS ((m' + 1) + 1) S' ⟨S2, hd2, tm2, h2⟩ m' =
          getS (m' + 1) S2 tm2 m' :=
        getS_recurse (m' + 1) S' _ m' (by omega)
      have t1 : getS (m' + 1) S1 tm1 m' = S1 := getS_top m' S1 tm1
      have t2 : getS (m' + 1) S2 tm2 m' = S2 := getS_top m' S2 tm2
      have hSeq : S1 = S2 := t1.symm.trans (r1.symm.trans (eS.trans (r2.trans t2)))
      subst hSeq
      have hS' : ∀ j, j < m' + 1 →
          getS (m' + 1) S1 tm1 j = getS (m' + 1) S1 tm2 j := by
        intro j hj
        have e := hS j (by omega)
        have rr1 : getS ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ j =
            getS (m' + 1) S1 tm1 j :=
          getS_recurse (m' + 1) S' _ j (by omega)
        have rr2 : getS ((m' + 1) + 1) S' ⟨S1, hd2, tm2, h2⟩ j =
            getS (m' + 1) S1 tm2 j :=
          getS_recurse (m' + 1) S' _ j (by omega)
        exact rr1.symm.trans (e.trans rr2)
      have hF' : ∀ j, j < m' + 1 →
          getF (m' + 1) S1 tm1 j = getF (m' + 1) S1 tm2 j := by
        intro j hj
        have e := hF j (by omega)
        have rr1 : getF ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ j =
            getF (m' + 1) S1 tm1 j :=
          getF_recurse (m' + 1) S' _ j (by omega)
        have rr2 : getF ((m' + 1) + 1) S' ⟨S1, hd2, tm2, h2⟩ j =
            getF (m' + 1) S1 tm2 j :=
          getF_recurse (m' + 1) S' _ j (by omega)
        exact rr1.symm.trans (e.trans rr2)
      have htm : tm1 = tm2 := ih S1 tm1 tm2 hS' hF'
      subst htm
      have eF := hF (m' + 1) (by omega)
      have g1 : getF ((m' + 1) + 1) S' ⟨S1, hd1, tm1, h1⟩ (m' + 1) = h1.val :=
        getF_top (m' + 1) S' _
      have g2 : getF ((m' + 1) + 1) S' ⟨S1, hd2, tm1, h2⟩ (m' + 1) = h2.val :=
        getF_top (m' + 1) S' _
      have hval : h1.val = h2.val := g1.symm.trans (eF.trans g2)
      have hh : h1 = h2 := Subtype.ext hval
      subst hh
      have hhd : hd1 = hd2 := by
        cases hd1
        cases hd2
        rfl
      cases hhd
      rfl

private theorem horizFunNat_bwd_eq (m : ℕ) (t : Tiling m ∅) (j : ℕ) (hj : j < m)
    (a : Fin 4) :
    horizFunNat m (bwdSubgraph m t) (bwdSubgraph_perfect m t) j a =
      getF m ∅ t j a := by
  rw [horizFunNat_eq m _ _ j hj a]
  have hpeq := partner_bwd_eq m t (a, ⟨j, hj⟩)
  by_cases h_up : a ∈ getS m ∅ t j
  · have hpu := partnerT_up m t a ⟨j, hj⟩ h_up
    have hne : (partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t)
        (a, ⟨j, hj⟩)).2 ≠ ⟨j, hj⟩ := by
      rw [hpeq]
      intro hcon
      have hval : (partnerT m t (a, ⟨j, hj⟩)).2.val = j :=
        congrArg Fin.val hcon
      omega
    rw [ite_eq_right hne]
    have hprops := (tiling_props m ∅ t j hj).2
    have hmemU : a ∈ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
        getS m ∅ t j) :=
      Finset.mem_union_right _ h_up
    have hU : a ∉ Finset.univ \ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
        getS m ∅ t j) := by
      intro hcon
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hcon
      exact hcon hmemU
    have hfa : getF m ∅ t j a = a := hprops.2 a hU
    exact hfa.symm
  · by_cases h_down : a ∈ (if j = 0 then ∅ else getS m ∅ t (j - 1))
    · have hpd := partnerT_down m t a ⟨j, hj⟩ h_up h_down
      have hne : (partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t)
          (a, ⟨j, hj⟩)).2 ≠ ⟨j, hj⟩ := by
        rw [hpeq]
        intro hcon
        have hval : (partnerT m t (a, ⟨j, hj⟩)).2.val = j :=
          congrArg Fin.val hcon
        omega
      rw [ite_eq_right hne]
      have hprops := (tiling_props m ∅ t j hj).2
      have hmemU : a ∈ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
          getS m ∅ t j) :=
        Finset.mem_union_left _ h_down
      have hU : a ∉ Finset.univ \ ((if j = 0 then ∅ else getS m ∅ t (j - 1)) ∪
          getS m ∅ t j) := by
        intro hcon
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hcon
        exact hcon hmemU
      have hfa : getF m ∅ t j a = a := hprops.2 a hU
      exact hfa.symm
    · have hhor := partnerT_horiz m t a ⟨j, hj⟩ h_up h_down
      have h2 : (partnerT m t (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ :=
        congrArg Prod.snd hhor
      have hsame : (partner m (bwdSubgraph m t) (bwdSubgraph_perfect m t)
          (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ := by
        rw [hpeq, h2]
      rw [ite_eq_left hsame]
      rw [hpeq, hhor]

private theorem getS_rec_eq (m : ℕ) (S1 : Finset (Fin 4)) (build : Tiling m S1)
    (htop : S1 = ∅) (j : ℕ) :
    getS m ∅ (htop.rec build) j = getS m S1 build j := by
  cases htop
  rfl

private theorem getF_rec_eq (m : ℕ) (S1 : Finset (Fin 4)) (build : Tiling m S1)
    (htop : S1 = ∅) (j : ℕ) :
    getF m ∅ (htop.rec build) j = getF m S1 build j := by
  cases htop
  rfl

private theorem fwd_bwd_eq (m : ℕ) (t : Tiling m ∅) :
    fwdTiling m (bwdSubgraph m t) (bwdSubgraph_perfect m t) = t := by
  apply tiling_ext_of_getSF_eq
  · intro j hj
    cases m with
    | zero => exact absurd hj (Nat.not_lt_zero j)
    | succ m' =>
      have htop : topHoles (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) (m' + 1) = ∅ := by
        change vertSet (m' + 1) _ _ m' = ∅
        apply vertSet_top_empty
        omega
      have hfwd : fwdTiling (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) =
          htop.rec (buildTiling (m' + 1) (bwdSubgraph (m' + 1) t)
            (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega)) := rfl
      rw [hfwd, getS_rec_eq]
      have hbuild := getS_build_eq (m' + 1) (bwdSubgraph (m' + 1) t)
        (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega) j hj
      rw [hbuild]
      exact vertSet_bwd_eq (m' + 1) t j
  · intro j hj
    cases m with
    | zero => exact absurd hj (Nat.not_lt_zero j)
    | succ m' =>
      have htop : topHoles (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) (m' + 1) = ∅ := by
        change vertSet (m' + 1) _ _ m' = ∅
        apply vertSet_top_empty
        omega
      have hfwd : fwdTiling (m' + 1) (bwdSubgraph (m' + 1) t)
          (bwdSubgraph_perfect (m' + 1) t) =
          htop.rec (buildTiling (m' + 1) (bwdSubgraph (m' + 1) t)
            (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega)) := rfl
      rw [hfwd, getF_rec_eq]
      have hbuild := getF_build_eq (m' + 1) (bwdSubgraph (m' + 1) t)
        (bwdSubgraph_perfect (m' + 1) t) (m' + 1) (by omega) j hj
      rw [hbuild]
      funext a
      exact horizFunNat_bwd_eq (m' + 1) t j hj a

private theorem getS_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    getS m ∅ (fwdTiling m M hM) j = vertSet m M hM j := by
  cases m with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ m' =>
    have htop : topHoles (m' + 1) M hM (m' + 1) = ∅ := by
      change vertSet (m' + 1) _ _ m' = ∅
      apply vertSet_top_empty
      omega
    have hfwd : fwdTiling (m' + 1) M hM =
        htop.rec (buildTiling (m' + 1) M hM (m' + 1) (by omega)) := rfl
    rw [hfwd, getS_rec_eq]
    exact getS_build_eq (m' + 1) M hM (m' + 1) (by omega) j hj

private theorem getF_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    getF m ∅ (fwdTiling m M hM) j = horizFunNat m M hM j := by
  cases m with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ m' =>
    have htop : topHoles (m' + 1) M hM (m' + 1) = ∅ := by
      change vertSet (m' + 1) _ _ m' = ∅
      apply vertSet_top_empty
      omega
    have hfwd : fwdTiling (m' + 1) M hM =
        htop.rec (buildTiling (m' + 1) M hM (m' + 1) (by omega)) := rfl
    rw [hfwd, getF_rec_eq]
    exact getF_build_eq (m' + 1) M hM (m' + 1) (by omega) j hj

private theorem partnerT_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v : Fin 4 × Fin m) :
    partnerT m (fwdTiling m M hM) v = partner m M hM v := by
  obtain ⟨a, i⟩ := v
  have hj : i.val < m := i.isLt
  by_cases hsame : (partner m M hM (a, i)).2 = i
  · have hUp : a ∉ getS m ∅ (fwdTiling m M hM) i.val := by
      intro hcon
      rw [getS_fwd_eq m M hM i.val hj] at hcon
      have hmem : a ∈ aboveSet m M hM i.val := hcon
      obtain ⟨k, hk, heq⟩ := above_mem_up m M hM i.val hj a hmem
      have hi : (⟨i.val, hj⟩ : Fin m) = i := Fin.ext rfl
      have h1 : (partner m M hM (a, i)).2 = k := by
        have h := congrArg Prod.snd heq
        rw [hi] at h
        exact h
      have hkk : k = i := h1.symm.trans hsame
      have hval : k.val = i.val := congrArg Fin.val hkk
      omega
    have hDown : a ∉ (if i.val = 0 then ∅ else
        getS m ∅ (fwdTiling m M hM) (i.val - 1)) := by
      by_cases hj0 : i.val = 0
      · simp only [ite_eq_left hj0]
        exact Finset.notMem_empty a
      · simp only [ite_eq_right hj0]
        intro hcon
        have hj1 : i.val - 1 < m := by omega
        rw [getS_fwd_eq m M hM (i.val - 1) hj1] at hcon
        rw [vertSet_mem] at hcon
        obtain ⟨i', k', hi', hk', heq⟩ := hcon
        have hkk' : k' = i := by
          apply Fin.ext
          omega
        have hsym := partner_pair_symm m M hM a i' k' heq
        rw [hkk'] at hsym
        have h2 : (partner m M hM (a, i)).2 = i' := congrArg Prod.snd hsym
        rw [hsame] at h2
        have hval : i.val = i'.val := congrArg Fin.val h2
        omega
    have hhor := partnerT_horiz m (fwdTiling m M hM) a i hUp hDown
    have hF := getF_fwd_eq m M hM i.val hj
    have hmem : a ∈ leftoverSet m M hM i.val := by
      rw [leftover_mem]
      intro hcon
      rw [Finset.mem_union] at hcon
      rcases hcon with hb | ha
      · by_cases hj0 : i.val = 0
        · have hbs : belowSet m M hM i.val = ∅ := by rw [hj0]; rfl
          rw [hbs] at hb
          exact (Finset.notMem_empty a) hb
        · have hj1 : i.val - 1 < m := by omega
          have hbs : belowSet m M hM i.val = vertSet m M hM (i.val - 1) := by
            obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
            rw [hj']
            rfl
          rw [hbs] at hb
          have hget := getS_fwd_eq m M hM (i.val - 1) hj1
          simp only [ite_eq_right hj0] at hDown
          rw [hget] at hDown
          exact hDown hb
      · have hget := getS_fwd_eq m M hM i.val hj
        rw [hget] at hUp
        exact hUp ha
    have hfa : horizFunNat m M hM i.val a = (partner m M hM (a, i)).1 := by
      have hi : (⟨i.val, hj⟩ : Fin m) = i := Fin.ext rfl
      have h := horizFunNat_of_mem m M hM i.val hj a hmem
      rw [hi] at h
      exact h
    rw [hhor]
    have hFa : getF m ∅ (fwdTiling m M hM) i.val a =
        horizFunNat m M hM i.val a :=
      congrFun hF a
    rw [hFa, hfa]
    exact Prod.ext rfl hsame.symm
  · have ⟨haeq, hpath⟩ := partner_ne_layer_vert m M hM a i hsame
    rw [pathGraph_adj] at hpath
    rcases hpath with hup | hdown
    · have hmemV : a ∈ vertSet m M hM i.val := by
        rw [vertSet_mem]
        refine ⟨i, (partner m M hM (a, i)).2, rfl, hup.symm, ?_⟩
        exact Prod.ext haeq rfl
      have hmemG : a ∈ getS m ∅ (fwdTiling m M hM) i.val := by
        rw [getS_fwd_eq m M hM i.val hj]
        exact hmemV
      have hpu := partnerT_up m (fwdTiling m M hM) a i hmemG
      have h1 : (partnerT m (fwdTiling m M hM) (a, i)).1 = a := hpu.1
      have h2 : (partnerT m (fwdTiling m M hM) (a, i)).2 =
          (partner m M hM (a, i)).2 := by
        apply Fin.ext
        have hval : (partnerT m (fwdTiling m M hM) (a, i)).2.val =
            i.val + 1 := hpu.2
        omega
      exact Prod.ext (h1.trans haeq.symm) h2
    · have hj0 : i.val ≠ 0 := by omega
      have hUp : a ∉ getS m ∅ (fwdTiling m M hM) i.val := by
        intro hcon
        rw [getS_fwd_eq m M hM i.val hj] at hcon
        have hmem : a ∈ aboveSet m M hM i.val := hcon
        obtain ⟨k, hk, heq⟩ := above_mem_up m M hM i.val hj a hmem
        have hi : (⟨i.val, hj⟩ : Fin m) = i := Fin.ext rfl
        have h1 : (partner m M hM (a, i)).2 = k := by
          have h := congrArg Prod.snd heq
          rw [hi] at h
          exact h
        have hval : (partner m M hM (a, i)).2.val = k.val :=
          congrArg Fin.val h1
        omega
      have hDown : a ∈ (if i.val = 0 then ∅ else
          getS m ∅ (fwdTiling m M hM) (i.val - 1)) := by
        simp only [ite_eq_right hj0]
        have hj1 : i.val - 1 < m := by omega
        rw [getS_fwd_eq m M hM (i.val - 1) hj1]
        rw [vertSet_mem]
        have hpeq : partner m M hM (a, i) =
            (a, (partner m M hM (a, i)).2) :=
          Prod.ext haeq rfl
        have hsym := partner_pair_symm m M hM a i
          (partner m M hM (a, i)).2 hpeq
        refine ⟨(partner m M hM (a, i)).2, i, by omega, by omega, hsym⟩
      have hpd := partnerT_down m (fwdTiling m M hM) a i hUp hDown
      have h1 : (partnerT m (fwdTiling m M hM) (a, i)).1 = a := hpd.1
      have h2 : (partnerT m (fwdTiling m M hM) (a, i)).2 =
          (partner m M hM (a, i)).2 := by
        apply Fin.ext
        have hval : (partnerT m (fwdTiling m M hM) (a, i)).2.val + 1 =
            i.val := hpd.2
        omega
      exact Prod.ext (h1.trans haeq.symm) h2

private theorem bwd_fwd_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) :
    bwdSubgraph m (fwdTiling m M hM) = M := by
  have hMverts : M.verts = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    exact M.edge_vert (partner_spec m M hM v)
  have hverts : (bwdSubgraph m (fwdTiling m M hM)).verts = M.verts := by
    have hbwd : (bwdSubgraph m (fwdTiling m M hM)).verts = Set.univ := rfl
    rw [hbwd, hMverts]
  have hAdj : ∀ v w, (bwdSubgraph m (fwdTiling m M hM)).Adj v w ↔ M.Adj v w := by
    intro v w
    have hPT := partnerT_fwd_eq m M hM v
    constructor
    · intro h
      have heq : w = partnerT m (fwdTiling m M hM) v := h
      rw [hPT] at heq
      rw [heq]
      exact partner_spec m M hM v
    · intro h
      have heq : w = partner m M hM v := partner_unique m M hM v w h
      have h2 : w = partnerT m (fwdTiling m M hM) v := heq.trans hPT.symm
      exact h2
  have hAdjEq : (bwdSubgraph m (fwdTiling m M hM)).Adj = M.Adj :=
    funext fun v => funext fun w => propext (hAdj v w)
  exact Subgraph.ext hverts hAdjEq

/--
**Sellers' domino tiling theorem.** Let $W_4$ be the complete graph $K_4$ with one edge
removed and $P_{n-1}$ the path graph on $n - 1$ vertices. For every natural number $n \ge 2$,
the number of perfect matchings (domino tilings) of the Cartesian product $W_4 \square P_{n-1}$
equals $f_n p_n$, where $f_n$ is the $n$-th Fibonacci number ($f_0 = 0$, $f_1 = 1$) and $p_n$ is
the $n$-th Pell number ($p_0 = 0$, $p_1 = 1$, $p_{k+2} = 2 p_{k+1} + p_k$).
-/
theorem boxProd_tiling_card_eq_fib_mul_pellNumber :
    ∀ (n : ℕ) (_hn : 2 ≤ n),
      Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
        {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
        SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
        Nat.fib n * pellNumber n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hclosed : Nat.fib (m + 1) * pellNumber (m + 1) = dval m := by
    unfold dval
    rw [pell_eq_pellNumber]
  rw [hclosed]
  have hsub : m + 1 - 1 = m := rfl
  rw [hsub]
  have hAval : Aval m = dval m := Aval_eq_dval m
  rw [←hAval]
  unfold Aval Ncount
  change Nat.card { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } =
    Fintype.card (Tiling m ∅)
  have e : { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } ≃
      Tiling m ∅ :=
    { toFun := fun M => fwdTiling m M.val M.property
      invFun := fun t => ⟨bwdSubgraph m t, bwdSubgraph_perfect m t⟩
      left_inv := fun M => by
        have h : bwdSubgraph m (fwdTiling m M.val M.property) = M.val :=
          bwd_fwd_eq m M.val M.property
        exact Subtype.ext h
      right_inv := fun t => fwd_bwd_eq m t }
  calc Nat.card { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching }
      = Nat.card (Tiling m ∅) := Nat.card_congr e
    _ = Fintype.card (Tiling m ∅) := Nat.card_eq_fintype_card

/--
**Sellers' domino tiling theorem, recursive Pell form.** Let $W_4$ be the complete graph
$K_4$ with one edge removed and $P_{n-1}$ the path graph on $n - 1$ vertices. For every natural
number $n \ge 2$, the number of perfect matchings (domino tilings) of the Cartesian product
$W_4 \square P_{n-1}$ equals $f_n p_n$, where $f_n$ is the $n$-th Fibonacci number
($f_0 = 0$, $f_1 = 1$) and $p_n$ is defined by $p_0 = 0$, $p_1 = 1$ and
$p_{k+2} = 2 p_{k+1} + p_k$.

The Cartesian product $\square$ is the paper's $\times$, following Faase. The paper writes
$c_n$ for this number of tilings; its values $c_2 = 2$, $c_3 = 10$, $c_4 = 36$ match $f_n p_n$.

Source: James A. Sellers, "Domino Tilings and Products of Fibonacci and
Pell Numbers," Journal of Integer Sequences 5 (2002), Article 02.1.2,
Theorem (label mainresult), lines 105–108,
https://cs.uwaterloo.ca/journals/JIS/VOL5/Sellers/sellers4.tex
-/
theorem boxProd_tiling_card_eq_fib_mul_pell :
    ∀ (n : ℕ) (_hn : 2 ≤ n),
      Nat.card { M : (((SimpleGraph.completeGraph (Fin 4)).deleteEdges
        {Sym2.mk (0 : Fin 4) (1 : Fin 4)} □
        SimpleGraph.pathGraph (n - 1)).Subgraph) // M.IsPerfectMatching } =
        Nat.fib n *
          ((Nat.rec (motive := fun (_ : ℕ) => ℕ × ℕ) (0, 1)
            (fun (_ : ℕ) (ih : ℕ × ℕ) => (ih.2, 2 * ih.2 + ih.1)) n).1) := by
  intro n hn
  have h := boxProd_tiling_card_eq_fib_mul_pellNumber n hn
  rw [h]
  congr 1
  exact (pell_eq_pellNumber n).symm

end MetaMathlibExt
end
