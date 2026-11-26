/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
public import MathlibExt.GameTheory.EuclidGameCalkinWilf
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Number of arch tops in a row of the Calkin–Wilf tree

The number of left arch tops in row `k` satisfies the integer formula
`3 * Tₖ = 2 ^ (k - 2) + 2 * (-1) ^ k` for `2 ≤ k`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.7.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem swap (a b : ℕ) : euclidPPosition a b = euclidPPosition b a := by
  suffices h : ∀ f a b, euclidPPositionAux f a b = euclidPPositionAux f b a by
    simpa only [euclidPPosition, Nat.add_comm b a] using h (a + b) a b
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro a b
    simp only [euclidPPositionAux]
    split_ifs <;> first | rfl | omega | (congr 1; funext k; rw [ih])

private theorem add_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    euclidPPosition (a + b) b = true ↔
      ∀ k : ℕ, k * b < a → ¬euclidPPosition (a - k * b) b = true := by
  rw [euclidPPosition_eq_true_iff, SpragueGrundy.isP_iff euclidGame (a + b, b)]
  change (∀ q ∈ euclidMoves (a + b, b), ¬SpragueGrundy.IsP euclidGame q) ↔ _
  rw [euclidMoves, ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega)]
  simp only [Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, euclidPPosition_eq_true_iff]
  refine forall_congr' fun k => ?_
  have bound : k < (a + b - 1) / b ↔ k * b < a := by
    change k + 1 ≤ (a + b - 1) / b ↔ _
    rw [Nat.le_div_iff_mul_le hb, Nat.add_one_mul]
    omega
  simp only [bound, Nat.add_one_mul, Nat.add_sub_add_right]

private theorem forced (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    euclidPPosition a b = true ↔ ¬euclidPPosition (a + b) b = true := by
  suffices h : euclidPPosition (a + b) b = true ↔ ¬euclidPPosition a b = true by
    simp only [h, not_not]
  rw [add_iff a b ha (by omega)]
  constructor
  · intro h
    simpa using h 0 (by simpa)
  · intro h k hk
    cases k with
    | zero => simpa using h
    | succ k => rw [Nat.succ_mul] at hk; omega

private theorem twice (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬euclidPPosition (a + b + b) b = true := by
  rw [add_iff (a + b) b (by omega) hb]
  intro h
  have hparent : ¬euclidPPosition (a + b) b = true := by
    simpa using h 0 (by simp; omega)
  apply hparent
  apply (add_iff a b ha hb).2
  intro k hk
  simpa only [Nat.succ_mul, Nat.add_sub_add_right] using
    h (k + 1) (by rw [Nat.succ_mul]; omega)

private def children (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(p.1, p.1 + p.2), (p.1 + p.2, p.2)]

private def grandchildren (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  (children p).flatMap children

private abbrev outcome (p : ℕ × ℕ) : Bool := euclidPPosition p.1 p.2

private theorem row_pos (k : ℕ) (p : ℕ × ℕ) (h : p ∈ calkinWilfRow k) :
    0 < p.1 ∧ 0 < p.2 := by
  induction k generalizing p with
  | zero =>
    simp only [calkinWilfRow, List.mem_singleton] at h
    subst p
    decide
  | succ k ih =>
    obtain ⟨q, hq, h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> have hp := ih q hq <;> dsimp <;> omega

private theorem row_succ (k : ℕ) :
    calkinWilfRow (k + 1) = (calkinWilfRow k).flatMap children := rfl

private theorem row_two (k : ℕ) :
    calkinWilfRow (k + 2) = (calkinWilfRow k).flatMap grandchildren := by
  rw [row_succ, row_succ, List.flatMap_assoc]
  rfl

private theorem children_length (l : List (ℕ × ℕ)) :
    (l.flatMap children).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [children, ih]; omega

private theorem row_length (k : ℕ) : (calkinWilfRow k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [row_succ, children_length, ih, pow_succ]; omega

private theorem count_grandchildren (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) :
    (grandchildren p).countP outcome + (children p).countP outcome = 2 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨ha, hb⟩ := hp
  have hss : euclidPPosition a (a + (a + b)) = false := by
    have h := twice b a hb ha
    rw [swap] at h
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Bool.not_eq_true] using h
  have hdd : euclidPPosition (a + b + b) b = false := by
    simpa only [Bool.not_eq_true] using twice a b ha hb
  have hsd := forced a (a + b) ha (by omega)
  have hds := forced b (a + b) hb (by omega)
  rw [swap b (a + b), Nat.add_comm b (a + b), swap (a + b + b) (a + b)] at hds
  simp only [grandchildren, children, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.countP_cons, List.countP_nil, outcome]
  simp only [hss, hdd, Bool.false_eq_true, ↓reduceIte]
  by_cases hs : euclidPPosition a (a + b) = true <;>
    by_cases hd : euclidPPosition (a + b) b = true <;> simp_all

private theorem count_two (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, 0 < p.1 ∧ 0 < p.2) :
    (l.flatMap grandchildren).countP outcome + (l.flatMap children).countP outcome =
      2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp := count_grandchildren p (hl p (by simp))
    have ht := ih (fun q hq => hl q (by simp [hq]))
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    omega

private theorem row_count_step (k : ℕ) :
    (calkinWilfRow (k + 2)).countP outcome + (calkinWilfRow (k + 1)).countP outcome =
      2 * 2 ^ k := by
  rw [row_two, row_succ, ← row_length]
  exact count_two _ (row_pos k)

private theorem row_count_sum (k : ℕ) :
    (calkinWilfRow (k + 1)).countP outcome + (calkinWilfRow k).countP outcome = 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := row_count_step k
    change (calkinWilfRow (k + 2)).countP outcome +
      (calkinWilfRow (k + 1)).countP outcome = 2 ^ (k + 1)
    rw [pow_succ]
    omega

private theorem row_count_formula (k : ℕ) :
    3 * ((calkinWilfRow k).countP outcome : ℤ) = 2 ^ k + 2 * (-1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := congrArg (fun n : ℕ => (n : ℤ)) (row_count_sum k)
    push_cast at h
    rw [pow_succ, pow_succ]
    linarith

private def archPredicate (l : List (ℕ × ℕ)) (p : ℕ × ℕ) : Bool :=
  l.any fun V => outcome V && p == (2 * V.1 + V.2, V.1 + V.2)

private theorem arch_iff (l : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    archPredicate l p = true ↔
      ∃ V ∈ l, outcome V = true ∧ p = (2 * V.1 + V.2, V.1 + V.2) := by
  simp [archPredicate, List.any_eq_true]

private theorem arch_bounds (l : List (ℕ × ℕ))
    (hl : ∀ V ∈ l, 0 < V.1 ∧ 0 < V.2) (p : ℕ × ℕ)
    (hp : archPredicate l p = true) : p.2 < p.1 ∧ p.1 < 2 * p.2 := by
  obtain ⟨V, hV, _, rfl⟩ := (arch_iff l p).1 hp
  have hv := hl V hV
  dsimp
  omega

private theorem arch_grandchildren_count (l : List (ℕ × ℕ))
    (hl : ∀ V ∈ l, 0 < V.1 ∧ 0 < V.2) (p : ℕ × ℕ) (hp : p ∈ l) :
    (grandchildren p).countP (archPredicate l) = if outcome p then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  have hab := hl (a, b) hp
  have excluded (q : ℕ × ℕ) (hq : q.1 ≤ q.2 ∨ 2 * q.2 ≤ q.1) :
      archPredicate l q = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hbound := arch_bounds l hl q h
    omega
  have hss := excluded (a, a + (a + b)) (by dsimp; omega)
  have hds := excluded (a + b, a + b + b) (by dsimp; omega)
  have hdd := excluded (a + b + b, b) (by dsimp; omega)
  have hsd : archPredicate l (a + (a + b), a + b) = outcome (a, b) := by
    apply Bool.eq_iff_iff.mpr
    rw [arch_iff]
    constructor
    · rintro ⟨V, _, hV, he⟩
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      have hv : V = (a, b) := by
        apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> omega
      simpa only [hv] using hV
    · intro h
      refine ⟨(a, b), hp, h, ?_⟩
      apply Prod.ext <;> dsimp; omega
  simp only [grandchildren, children, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.countP_cons, List.countP_nil]
  simp [hss, hds, hdd, hsd]

private theorem arch_flatMap_count (l r : List (ℕ × ℕ))
    (hl : ∀ V ∈ l, 0 < V.1 ∧ 0 < V.2) (hr : ∀ p ∈ r, p ∈ l) :
    (r.flatMap grandchildren).countP (archPredicate l) = r.countP outcome := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    have hp := arch_grandchildren_count l hl p (hr p (by simp))
    have ht := ih (fun q hq => hr q (by simp [hq]))
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons, hp, ht]
    omega

private theorem arch_count (k : ℕ) :
    (calkinWilfRow (k + 2)).countP (archPredicate (calkinWilfRow k)) =
      (calkinWilfRow k).countP outcome := by
  rw [row_two]
  exact arch_flatMap_count _ _ (row_pos k) (fun _ h => h)

/-- **Number of arch tops in a row of the Calkin–Wilf tree.** For $k \ge 2$ let $T_k$ be the
number of vertices of row $k$ of the Calkin–Wilf tree of the form $(2m+n)/(m+n)$ with $m/n$ a
P-position of Euclid in row $k - 2$. Then $3T_k = 2^{k-2} + 2(-1)^k$, that is,
$T_k = 2^{k-2}/3 + 2(-1)^k/3$.

The vertex $(2m+n)/(m+n)$ is the son's daughter of $m/n$, the left top of the arch below $m/n$;
the daughter's son $(m+n)/(m+2n)$ is the right top, so $T_k$ counts the arches whose tops lie in
row $k$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.7. -/
public theorem count_arch_tops_calkinWilfRow (k : ℕ) (hk : 2 ≤ k) :
    3 * (((calkinWilfRow k).countP fun p => (calkinWilfRow (k - 2)).any fun V =>
        euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) =
      2 ^ (k - 2) + 2 * (-1) ^ k
    := by
  have h : k = (k - 2) + 2 := by omega
  change 3 * ((calkinWilfRow k).countP (archPredicate (calkinWilfRow (k - 2))) : ℤ) = _
  have hc : (calkinWilfRow k).countP (archPredicate (calkinWilfRow (k - 2))) =
      (calkinWilfRow (k - 2)).countP outcome := by
    conv_lhs => arg 2; rw [h]
    exact arch_count (k - 2)
  have he : (-1 : ℤ) ^ k = (-1) ^ (k - 2) := by
    conv_lhs => rw [h, pow_add]
    norm_num
  rw [hc, row_count_formula, he]

end

end MetaMathlibExt
