/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.List.Cycle
public import Mathlib.Tactic.FinCases

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 29, Combinatorics 30, Combinatorics 54, Combinatorics 55, Combinatorics 56, Combinatorics 462, Combinatorics 463, Combinatorics 465, Combinatorics 464

-- Combinatorics 29: Lattice Path with Prescribed Steps
def LatticePath (d : ℕ)
    (D : Set (Fin d → ℤ))
    (p q : Fin d → ℤ) :=
  { l : List (Fin d → ℤ) //
    l.head? = some p ∧
    l.getLast? = some q ∧
    List.IsChain
      (fun a b => b - a ∈ D) l
  }

-- Combinatorics 30: Fixed-Length Necklace
def Necklace (A : Type*) (n : ℕ) :=
  {c : Cycle A // c.length = n}

-- Combinatorics 54: Lucas Number Sequence
def Nat.lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => Nat.lucas (n + 1) + Nat.lucas n

-- Combinatorics 55: Motzkin Number Sequence
def Nat.motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    Nat.motzkin n +
      Finset.sum Finset.univ fun k : Fin n =>
        Nat.motzkin k.val *
          Nat.motzkin (n - 1 - k.val)

-- Combinatorics 56: Delannoy Numbers
def Nat.delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 =>
    Nat.delannoy m (n + 1) +
      Nat.delannoy (m + 1) n +
        Nat.delannoy m n

-- Combinatorics 462: Southeast Path
def SoutheastPath (p q : ℕ × ℕ) :=
  { l : List (ℕ × ℕ) //
    l.head? = some p ∧ l.getLast? = some q ∧
    l.IsChain fun a b =>
      b = (a.1 + 1, a.2) ∨ a = (b.1, b.2 + 1) }

-- Combinatorics 463: Southeast Path Weight
def SoutheastPath.weight {p q : ℕ × ℕ} {R : Type*}
    [CommMonoid R] (x : ℕ → R)
    (l : SoutheastPath p q) : R :=
  ((l.1.zip l.1.tail).map fun c =>
    if c.2 = (c.1.1 + 1, c.1.2) then x c.1.2 else 1).prod

-- Combinatorics 465: Nonintersecting Path Family
def IsNonintersectingPathFamily {n : ℕ}
    {p q : Fin n → ℕ × ℕ}
    (L : (i : Fin n) → SoutheastPath (p i) (q i)) :
    Prop :=
  Pairwise fun i j => ∀ v ∈ (L i).1, v ∉ (L j).1

-- Combinatorics 464: Nonintersecting Path Weight Sum
noncomputable def nonintersectingPathWeightSum {n : ℕ}
    {R : Type*} [CommSemiring R] (x : ℕ → R)
    (p q : Fin n → ℕ × ℕ) : R :=
  ∑ᶠ L : {L : (i : Fin n) → SoutheastPath (p i) (q i) //
      IsNonintersectingPathFamily L},
    ∏ i, (L.1 i).weight x

-- Combinatorics 29: Lattice Path with Prescribed Steps (sanity check)
theorem latticePath_one_step :
    Nonempty
      (LatticePath 1
        ({1} : Set (Fin 1 → ℤ)) 0 1) := by
  exact ⟨⟨[0, 1], by simp⟩⟩

-- Combinatorics 30: Fixed-Length Necklace (sanity check)
def redBlueNecklace : Necklace String 2 :=
  ⟨Quotient.mk
      (List.IsRotated.setoid String)
      ["red", "blue"],
    by simp⟩

theorem redBlueNecklace_rotation :
    redBlueNecklace =
      ⟨Quotient.mk
          (List.IsRotated.setoid String)
          ["blue", "red"],
        by simp⟩ := by
  apply Subtype.ext
  exact Quotient.sound
    List.IsRotated.cons_append_singleton

-- Combinatorics 54: Lucas Number Sequence (sanity check)
theorem Lucas_two :
    Nat.lucas 2 = 3 := by
  decide

-- Combinatorics 55: Motzkin Number Sequence (sanity check)
theorem Motzkin_two :
    Nat.motzkin 2 = 2 := by
  simp [Nat.motzkin]

-- Combinatorics 56: Delannoy Numbers (sanity check)
theorem Delannoy_one_one :
    Nat.delannoy 1 1 = 3 := by
  simp [Nat.delannoy]

-- Combinatorics 462: Southeast Path (sanity check)
theorem SoutheastPath_nonempty_isEmpty :
    Nonempty (SoutheastPath (0, 1) (2, 0)) ∧
      IsEmpty (SoutheastPath (0, 0) (0, 1)) := by
  refine ⟨⟨⟨[(0,1), (1,1), (1,0), (2,0)], by simp⟩⟩, ?_⟩
  constructor
  rintro ⟨l, hh, hl, hc⟩
  have key : ∀ m : List (ℕ × ℕ),
      (m.IsChain fun a b =>
        b = (a.1 + 1, a.2) ∨ a = (b.1, b.2 + 1)) →
      ∀ u v, m.head? = some u → m.getLast? = some v →
        v.2 ≤ u.2 := by
    intro m hm
    induction hm with
    | nil => simp
    | singleton a => intro u v hu hv; simp_all
    | cons_cons hr h ih =>
      intro u v hu hv
      simp only [List.head?_cons, Option.some.injEq] at hu
      rw [List.getLast?_cons_cons] at hv
      have h2 := ih _ v rfl hv
      subst hu
      rcases hr with hr | hr
      · rw [hr] at h2; simpa using h2
      · rw [hr]; simp; omega
  have := key l hc _ _ hh hl
  simp at this

-- Combinatorics 463: Southeast Path Weight (sanity check)
theorem SoutheastPath.weight_eastSouthEast
    {R : Type*} [CommMonoid R] (x : ℕ → R) :
    SoutheastPath.weight x
      (⟨[(0,1),(1,1),(1,0),(2,0)], by decide⟩ :
        SoutheastPath (0,1) (2,0)) = x 1 * x 0 := by
  simp [SoutheastPath.weight]

-- Combinatorics 465: Nonintersecting Path Family (sanity check)
theorem isNonintersectingPathFamily_twoPaths :
    IsNonintersectingPathFamily
        (p := ![(0, 1), (0, 3)])
        (q := ![(1, 0), (1, 2)])
        (fun i => ⟨![[(0, 1), (1, 1), (1, 0)],
          [(0, 3), (1, 3), (1, 2)]] i,
          by fin_cases i <;> decide⟩) ∧
      ¬ IsNonintersectingPathFamily
        (p := ![(0, 1), (1, 2)])
        (q := ![(2, 1), (1, 0)])
        (fun i => ⟨![[(0, 1), (1, 1), (2, 1)],
          [(1, 2), (1, 1), (1, 0)]] i,
          by fin_cases i <;> decide⟩) := by
  unfold IsNonintersectingPathFamily Pairwise
  exact ⟨by decide, by decide⟩

-- Combinatorics 464: Nonintersecting Path Weight Sum (sanity check)
theorem nonintersectingPathWeightSum_two
    {R : Type*} [CommSemiring R] (x : ℕ → R) :
    nonintersectingPathWeightSum x ![(0, 0), (0, 1)]
        ![(1, 0), (1, 1)] = x 0 * x 1 ∧
      nonintersectingPathWeightSum x ![(0, 0), (0, 0)]
        ![(1, 0), (1, 0)] = 0 := by
  have key : ∀ m : List (ℕ × ℕ),
      (m.IsChain fun a b =>
        b = (a.1 + 1, a.2) ∨ a = (b.1, b.2 + 1)) →
      ∀ u v, m.head? = some u → m.getLast? = some v →
        m.length + u.1 + v.2 = v.1 + u.2 + 1 := by
    intro m hm
    induction hm with
    | nil => simp
    | singleton a =>
      intro u v hu hv
      simp only [List.head?_cons, List.getLast?_singleton,
        Option.some.injEq] at hu hv
      subst hu hv
      simp only [List.length_singleton]
      omega
    | cons_cons hr h ih =>
      intro u v hu hv
      simp only [List.head?_cons, Option.some.injEq] at hu
      rw [List.getLast?_cons_cons] at hv
      have h2 := ih _ v rfl hv
      subst hu
      simp only [List.length_cons] at h2 ⊢
      rcases hr with hr | hr
      · rw [hr] at h2; simp only at h2; omega
      · rw [hr]; simp only at h2 ⊢; omega
  have hp : ∀ a b : ℕ, ∀ l : SoutheastPath (a, b) (a + 1, b),
      l.1 = [(a, b), (a + 1, b)] := by
    intro a b
    rintro ⟨l, hh, hl, hc⟩
    have hlen := key l hc _ _ hh hl
    obtain ⟨u, v, rfl⟩ :=
      List.length_eq_two.mp (show l.length = 2 by omega)
    simp only [List.head?_cons, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some.injEq] at hh hl
    subst_vars
    rfl
  constructor
  · unfold nonintersectingPathWeightSum
    let L0 : {L : (i : Fin 2) →
        SoutheastPath (![(0, 0), (0, 1)] i)
          (![(1, 0), (1, 1)] i) //
        IsNonintersectingPathFamily L} :=
      ⟨fun i => ⟨![[(0, 0), (1, 0)], [(0, 1), (1, 1)]] i,
        by fin_cases i <;> decide⟩,
        by unfold IsNonintersectingPathFamily Pairwise; decide⟩
    have hall : ∀ L : {L : (i : Fin 2) →
        SoutheastPath (![(0, 0), (0, 1)] i)
          (![(1, 0), (1, 1)] i) //
        IsNonintersectingPathFamily L}, L = L0 := by
      intro L
      refine Subtype.ext (funext fun i => ?_)
      fin_cases i
      · exact Subtype.ext
          ((hp 0 0 (L.1 0)).trans (hp 0 0 (L0.1 0)).symm)
      · exact Subtype.ext
          ((hp 0 1 (L.1 1)).trans (hp 0 1 (L0.1 1)).symm)
    rw [finsum_eq_single _ L0
      (fun L hL => absurd (hall L) hL)]
    simp [L0, SoutheastPath.weight, Fin.prod_univ_two]
  · unfold nonintersectingPathWeightSum
    haveI : IsEmpty {L : (i : Fin 2) →
        SoutheastPath (![(0, 0), (0, 0)] i)
          (![(1, 0), (1, 0)] i) //
        IsNonintersectingPathFamily L} := by
      refine ⟨fun L => ?_⟩
      have h0 := hp 0 0 (L.1 0)
      have h1 := hp 0 0 (L.1 1)
      have hne := L.2 (show (0 : Fin 2) ≠ 1 by decide)
      exact hne (0, 0) (by simp [h0]) (by simp [h1])
    exact finsum_of_isEmpty _

end
