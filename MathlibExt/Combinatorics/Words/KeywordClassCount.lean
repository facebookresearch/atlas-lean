/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.KeywordSubstitutionClasses
public import MathlibExt.NumberTheory.Recurrences.MStepFibonacciPartialSums
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Card

/-!
# Counting binary keyword substitution classes

The number of classes of length-`n` words is the partial sum of the `m`-step Fibonacci
numbers through index `n`. Prefixing a fixed bit embeds the classes of length `n - 1`.
When the keyword fits, the two images meet along a copy of the classes of length `n - m - 1`.
-/

namespace MetaMathlibExt
namespace card_quot_keywordEquiv_eq_sum_mStepFibonacci

private abbrev Word (n : ℕ) := Fin n → Bool
private abbrev Classes {m : ℕ} (a : Word (m + 1)) (n : ℕ) := Quot (KeywordEquiv (n := n) a)

variable {m n k : ℕ} (a : Word (m + 1))

private abbrev cls (u : Word n) : Classes a n := Quot.mk _ u

/-- An observable on words descends to classes if each single substitution preserves it. -/
private def lift {α : Type*} (f : Word n → α)
    (hf : ∀ i u, f (keywordSimpleMap a i u) = f u) : Classes a n → α :=
  Quot.lift f fun _ _ h => by
    induction h with
    | refl => rfl
    | tail _ h ih =>
      obtain ⟨i, rfl⟩ := h
      exact ih.trans (hf i _).symm

private theorem applicable_cons (i : ℕ) (b : Bool) (u : Word n) :
    KeywordApplicable a (i + 1) (Fin.cons b u) ↔ KeywordApplicable a i u := by
  have letter (t : Fin (m + 1)) (h : i + t.val < n) :
      Fin.cons (α := fun _ => Bool) b u ⟨i + 1 + t.val, by omega⟩ = u ⟨i + t.val, h⟩ := by
    have he : (⟨i + 1 + t.val, by omega⟩ : Fin (n + 1)) = (⟨i + t.val, h⟩ : Fin n).succ :=
      Fin.ext (by dsimp; omega)
    rw [he, Fin.cons_succ]
  constructor <;> rintro ⟨h, hp | hp⟩ <;> refine ⟨by omega, ?_⟩
  · left; intro t; rw [← letter]; exact hp t
  · right; intro t; rw [← letter]; exact hp t
  · left; intro t; rw [letter t (by have := t.isLt; omega)]; exact hp t
  · right; intro t; rw [letter t (by have := t.isLt; omega)]; exact hp t

private theorem step_cons (i : ℕ) (b : Bool) (u : Word n) :
    keywordSimpleMap a (i + 1) (Fin.cons b u) = Fin.cons b (keywordSimpleMap a i u) := by
  classical
  funext j
  refine Fin.cases ?_ (fun t => ?_) j
  · by_cases h : KeywordApplicable a i u <;> simp [keywordSimpleMap, applicable_cons, h]
  · by_cases h : KeywordApplicable a i u <;>
      simp [keywordSimpleMap, applicable_cons, h, Nat.succ_add]

private def consClass (b : Bool) : Classes a n → Classes a (n + 1) :=
  lift a (fun u => cls a (Fin.cons b u)) fun i u => by
    rw [← step_cons]
    exact (Quot.sound (Relation.ReflTransGen.single ⟨i + 1, rfl⟩)).symm

/-- Prepend a word, using the length convention that recurses on the prefix. -/
private def prepend {r : ℕ} (p : Word r) (u : Word k) : Word (k + r) :=
  fun j => if h : j.val < r then p ⟨j, h⟩ else u ⟨j.val - r, by have := j.isLt; omega⟩

private theorem prepend_succ {r : ℕ} (p : Word (r + 1)) (u : Word k) :
    prepend p u = Fin.cons (p 0) (prepend (Fin.tail p) u) := by
  funext j
  refine Fin.cases ?_ (fun t => ?_) j
  · simp [prepend]
  · simp [prepend, Fin.tail]

private def prefixClass : {r : ℕ} → Word r → Classes a k → Classes a (k + r)
  | 0, _ => id
  | r + 1, p => consClass a (p 0) ∘ prefixClass (r := r) (Fin.tail p)

private theorem prefixClass_mk {r : ℕ} (p : Word r) (u : Word k) :
    prefixClass a p (cls a u) = cls a (prepend p u) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [prepend_succ, prefixClass, Function.comp_apply, ih]
    rfl

/-- The keyword or its complement, selected by its first bit. -/
private def pattern (b : Bool) : Word (m + 1) :=
  if b = a 0 then a else fun t => !a t

private theorem pattern_zero (b : Bool) : pattern a b 0 = b := by
  cases h : a 0 <;> cases b <;> simp [pattern, h]

private theorem pattern_flip (b : Bool) (t : Fin (m + 1)) :
    pattern a (!b) t = !pattern a b t := by
  cases h : a 0 <;> cases b <;> simp [pattern, h]

/-- Prepend the last `m` bits of the orientation of the keyword starting with `b`. -/
private abbrev branch (b : Bool) : Classes a k → Classes a (k + m) :=
  prefixClass a (Fin.tail (pattern a b))

private theorem step_pattern (b : Bool) (v : Word k) :
    keywordSimpleMap a 0 (prepend (pattern a b) v) = prepend (pattern a (!b)) v := by
  have ha : KeywordApplicable a 0 (prepend (pattern a b) v) := by
    refine ⟨by omega, ?_⟩
    by_cases h : b = a 0
    · left; intro t; simp [prepend, pattern, h, t.isLt]
    · right; intro t; simp [prepend, pattern, h, t.isLt]
  funext j
  rw [keywordSimpleMap_apply_of_applicable _ _ _ ha]
  by_cases h : j.val < m + 1
  · simp [prepend, h, show j.val ≤ m by omega, pattern_flip]
  · simp [prepend, h, show ¬j.val ≤ m by omega]

private theorem eq_prepend_of_applicable (u : Word (k + m + 1)) (ha : KeywordApplicable a 0 u) :
    ∃ v : Word k, u = prepend (pattern a (u 0)) v := by
  obtain ⟨_, ha⟩ := ha
  refine ⟨fun t => u ⟨m + 1 + t, by have := t.isLt; omega⟩, ?_⟩
  funext j
  by_cases hj : j.val < m + 1
  · rcases ha with h | h
    · have h0 : u 0 = a 0 := h 0
      simpa [prepend, hj, pattern, h0] using h ⟨j, hj⟩
    · have h0 : u 0 = !a 0 := h 0
      have hne : u 0 ≠ a 0 := by rw [h0]; simp
      simpa [prepend, hj, pattern, hne] using h ⟨j, hj⟩
  · simp only [prepend, hj, ↓reduceDIte]
    exact congrArg u (Fin.ext (by dsimp; omega))

private theorem consClass_branch (b : Bool) (z : Classes a k) :
    consClass a b (branch a b z) = consClass a (!b) (branch a (!b) z) := by
  induction z using Quot.ind with
  | _ v =>
    have mk (c : Bool) :
        consClass a c (branch a c (cls a v)) = cls a (prepend (pattern a c) v) := by
      rw [branch, prefixClass_mk, prepend_succ, pattern_zero]
      rfl
    rw [mk, mk]
    exact Quot.sound (Relation.ReflTransGen.single ⟨0, step_pattern a b v⟩)

/-- Observables on the two first-bit classes glue when they agree across a substitution
at the first position. -/
private def liftSides {α : Type*} (f : Bool → Classes a (k + m) → α)
    (hf : ∀ b z, f b (branch a b z) = f (!b) (branch a (!b) z)) :
    Classes a (k + m + 1) → α :=
  lift a (fun u => f (u 0) (cls a (Fin.tail u))) fun i u => by
    cases i with
    | zero =>
      by_cases ha : KeywordApplicable a 0 u
      · obtain ⟨v, hv⟩ := eq_prepend_of_applicable a u ha
        generalize hb : u 0 = b at hv
        rw [hv, step_pattern]
        simp only [prepend_succ (pattern a _), pattern_zero, Fin.cons_zero, Fin.tail_cons]
        simpa only [branch, prefixClass_mk] using (hf b (cls a v)).symm
      · rw [keywordSimpleMap_of_not_applicable _ _ _ ha]
    | succ i =>
      obtain ⟨b, v, rfl⟩ : ∃ b v, u = Fin.cons b v := ⟨_, _, (Fin.cons_self_tail u).symm⟩
      rw [step_cons]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact congrArg (f b) (Quot.sound (Relation.ReflTransGen.single ⟨i, rfl⟩)).symm

private theorem liftSides_cons {α : Type*} (f : Bool → Classes a (k + m) → α) (hf)
    (b : Bool) (q : Classes a (k + m)) :
    liftSides a f hf (consClass a b q) = f b q := by
  induction q using Quot.ind with
  | _ u =>
    simp [liftSides, consClass, lift, cls]

/-- On the side with head `b`, record the tail class. From the opposite side, record the
tail classes reachable by a substitution across the head. -/
private def tailsOn (b d : Bool) (y : Classes a (k + m)) : Set (Classes a (k + m)) :=
  if d = b then {y} else {x | ∃ z, branch a d z = y ∧ branch a b z = x}

private theorem tailsOn_glue (hb : ∀ b, Function.Injective (branch (k := k) a b)) (b d : Bool)
    (z : Classes a k) :
    tailsOn a b d (branch a d z) = tailsOn a b (!d) (branch a (!d) z) := by
  ext x
  cases b <;> cases d <;> simp [tailsOn, (hb _).eq_iff, eq_comm]

/-- Before the keyword fits, every class is a singleton. -/
private def shortEquiv (h : n ≤ m) : Classes a n ≃ Word n where
  toFun := lift a id fun i u => keywordSimpleMap_of_not_applicable _ _ _ fun ⟨_, _⟩ => by omega
  invFun := cls a
  left_inv := Quot.ind fun _ => rfl
  right_inv _ := rfl

private theorem prefixClass_injective {r : ℕ} (p : Word r)
    (ih : ∀ s < k + r, ∀ b, Function.Injective (consClass (n := s) a b)) :
    Function.Injective (prefixClass (k := k) a p) := by
  induction r with
  | zero => exact Function.injective_id
  | succ r hr =>
    exact (ih (k + r) (by omega) (p 0)).comp
      (hr (Fin.tail p) fun s hs => ih s (by omega))

/-- Prefixing a bit is injective: the invariant `tailsOn` recovers the original tail
class. Its invariance uses prefix injectivity only at shorter lengths. -/
private theorem consClass_injective (n : ℕ) (b : Bool) :
    Function.Injective (consClass (n := n) a b) := by
  induction n using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    by_cases h : n < m
    · intro x y hxy
      induction x using Quot.ind with
      | _ u =>
        induction y using Quot.ind with
        | _ v =>
          have huv : Fin.cons (α := fun _ => Bool) b u = Fin.cons b v :=
            congrArg (shortEquiv a (by omega : n + 1 ≤ m)) hxy
          exact congrArg (cls a) (Fin.cons_right_injective (α := fun _ => Bool) b huv)
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
      have hb (c : Bool) : Function.Injective (branch (k := k) a c) :=
        prefixClass_injective a _ ih
      intro x y hxy
      have he := congrArg (liftSides a (tailsOn a b) (tailsOn_glue a hb b)) hxy
      simpa [liftSides_cons, tailsOn] using he

private theorem union_ranges :
    Set.range (consClass (n := n) a false) ∪ Set.range (consClass a true) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quot.ind with
  | _ u =>
    have hu : consClass a (u 0) (cls a (Fin.tail u)) = cls a u :=
      congrArg (cls a) (Fin.cons_self_tail u)
    cases h : u 0
    · exact Or.inl ⟨_, h ▸ hu⟩
    · exact Or.inr ⟨_, h ▸ hu⟩

private theorem inter_ranges :
    Set.range (consClass (n := k + m) a false) ∩ Set.range (consClass a true) =
      Set.range (consClass a false ∘ branch (k := k) a false) := by
  have hb (b : Bool) : Function.Injective (branch (k := k) a b) :=
    prefixClass_injective a _ fun s _ => consClass_injective a s
  ext q
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    have he := congrArg (liftSides a (tailsOn a false) (tailsOn_glue a hb false)) hy
    rw [liftSides_cons, liftSides_cons] at he
    have hx : x ∈ tailsOn a false true y := by rw [he]; simp [tailsOn]
    obtain ⟨z, _, hz⟩ := hx
    exact ⟨z, congrArg (consClass a false) hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, (consClass_branch a false z).symm⟩⟩

private theorem count_recurrence :
    Nat.card (Classes a (k + m + 1)) + Nat.card (Classes a k) =
      2 * Nat.card (Classes a (k + m)) := by
  have h := Set.ncard_union_add_ncard_inter (Set.range (consClass (n := k + m) a false))
    (Set.range (consClass a true))
  rw [union_ranges, Set.ncard_univ, inter_ranges,
    Set.ncard_range_of_injective ((consClass_injective a _ false).comp
      (prefixClass_injective a _ fun s _ => consClass_injective a s)),
    Set.ncard_range_of_injective (consClass_injective a _ false),
    Set.ncard_range_of_injective (consClass_injective a _ true)] at h
  simpa [two_mul] using h

end card_quot_keywordEquiv_eq_sum_mStepFibonacci

open card_quot_keywordEquiv_eq_sum_mStepFibonacci in
set_option linter.unusedVariables false in
/-- **Keyword classes are counted by partial sums of $m$-step Fibonacci numbers.** Let
$m, n \ge 1$ and let $F_0, F_1, F_2, \dots$ be the $m$-step Fibonacci numbers: $F_0 = 1$,
$F_k = 2^{k-1}$ for $1 \le k \le m - 1$, and $F_k = F_{k-1} + F_{k-2} + \dots + F_{k-m}$ for
$k \ge m$. Then for every binary keyword $a$ of length $m + 1$, the number of equivalence
classes of the relation $\sim_a$ on binary words of length $n$ is $F_0 + F_1 + \dots + F_n$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Theorem 1
(`jis-2025-25.6.6-thm-1`). -/
public theorem card_quot_keywordEquiv_eq_sum_mStepFibonacci
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (F : ℕ → ℕ) (hF0 : F 0 = 1)
    (hFinit : ∀ k, 1 ≤ k → k ≤ m - 1 → F k = 2 ^ (k - 1))
    (hFrec : ∀ k, m ≤ k → F k = ∑ t ∈ Finset.Icc 1 m, F (k - t))
    (a : Fin (m + 1) → Bool) :
    Nat.card (Quot (KeywordEquiv (n := n) a)) = ∑ j ∈ Finset.range (n + 1), F j := by
  let S (k : ℕ) : ℝ := Nat.card (Classes a k)
  have hS := (sum_mStepFibonacci_iff_recurrence m hm F hF0 hFinit hFrec S).2
  have hinit (k : ℕ) (hk : k ≤ m) : S k = 2 ^ k := by
    simp [S, Nat.card_congr (shortEquiv a hk), Word, Nat.card_eq_fintype_card]
  have hrec (k : ℕ) (hk : m + 1 ≤ k) : S k = 2 * S (k - 1) - S (k - m - 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, k = r + m + 1 := ⟨k - m - 1, by omega⟩
    have h : S (r + m + 1) + S r = 2 * S (r + m) := by
      dsimp [S]
      exact_mod_cast count_recurrence (k := r) a
    rw [show r + m + 1 - m - 1 = r by omega, Nat.add_sub_cancel]
    exact eq_sub_of_add_eq h
  have h := hS ⟨hinit, hrec⟩ n
  dsimp [S] at h
  exact_mod_cast h

end MetaMathlibExt
