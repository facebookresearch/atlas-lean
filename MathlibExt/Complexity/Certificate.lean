/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Insert

/-!
# Certificates from decision-tree paths

For a query decision tree, the variables queried along the
computation path of an input `x` form a certificate: any
input agreeing on them evaluates the same, and there are at
most `depth` of them. This is the `C(f) ≤ D(f)` inequality
at one input.
-/

@[expose] public section

/-- Query decision trees for Boolean functions (core of
MOD-65): leaves output a bit, internal nodes query a variable. -/
inductive QTree (n : ℕ) : Type
  | leaf (b : Bool) : QTree n
  | query (i : Fin n) (l r : QTree n) : QTree n

/-- Evaluate on an input. -/
def QTree.eval {n : ℕ} : QTree n → (Fin n → Bool) → Bool
  | .leaf b, _ => b
  | .query i l r, x => if x i then r.eval x else l.eval x

/-- Depth of the tree. -/
def QTree.depth {n : ℕ} : QTree n → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max l.depth r.depth

/-- Certificate from the computation path: for every input
`x` there is a set `S` of at most `depth` coordinates such
that every `y` agreeing with `x` on `S` evaluates the same.
Since a computing tree gives `eval = f`, this is `C(f) ≤ D(f)`
at the queried input. -/
theorem QTree.exists_certificate {n : ℕ} (t : QTree n)
    (x : Fin n → Bool) :
    ∃ S : Finset (Fin n), S.card ≤ t.depth ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → t.eval y = t.eval x := by
  induction t generalizing x with
  | leaf b =>
    exact ⟨∅, by simp [QTree.depth], fun y _ => rfl⟩
  | query i l r ihl ihr =>
    cases hxi : x i with
    | true =>
      obtain ⟨S, hcard, hcert⟩ := ihr x
      by_cases hi : i ∈ S
      · refine ⟨S, ?_, ?_⟩
        · simp only [QTree.depth]
          have hmax : r.depth ≤ max l.depth r.depth := Nat.le_max_right _ _
          omega
        · intro y hy
          have hyi : y i = x i := hy i hi
          rw [hxi] at hyi
          have hr := hcert y (fun j hj => hy j hj)
          simp [QTree.eval, hxi, hyi, hr]
      · refine ⟨insert i S, ?_, ?_⟩
        · simp only [QTree.depth]
          have hins : (insert i S).card ≤ S.card + 1 := Finset.card_insert_le _ _
          have hmax : r.depth ≤ max l.depth r.depth := Nat.le_max_right _ _
          omega
        · intro y hy
          have hyi : y i = x i := hy i (Finset.mem_insert_self i S)
          rw [hxi] at hyi
          have hSr : ∀ j ∈ S, y j = x j := fun j hj => hy j (Finset.mem_insert_of_mem hj)
          have hr := hcert y hSr
          simp [QTree.eval, hxi, hyi, hr]
    | false =>
      obtain ⟨S, hcard, hcert⟩ := ihl x
      by_cases hi : i ∈ S
      · refine ⟨S, ?_, ?_⟩
        · simp only [QTree.depth]
          have hmax : l.depth ≤ max l.depth r.depth := Nat.le_max_left _ _
          omega
        · intro y hy
          have hyi : y i = x i := hy i hi
          rw [hxi] at hyi
          have hl := hcert y (fun j hj => hy j hj)
          simp [QTree.eval, hxi, hyi, hl]
      · refine ⟨insert i S, ?_, ?_⟩
        · simp only [QTree.depth]
          have hins : (insert i S).card ≤ S.card + 1 := Finset.card_insert_le _ _
          have hmax : l.depth ≤ max l.depth r.depth := Nat.le_max_left _ _
          omega
        · intro y hy
          have hyi : y i = x i := hy i (Finset.mem_insert_self i S)
          rw [hxi] at hyi
          have hSl : ∀ j ∈ S, y j = x j := fun j hj => hy j (Finset.mem_insert_of_mem hj)
          have hl := hcert y hSl
          simp [QTree.eval, hxi, hyi, hl]

end
