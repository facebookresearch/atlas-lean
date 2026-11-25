/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MulticommodityFlow

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rapid mixing yields a low-congestion flow

The main result is `exists_multicommodityFlow_load_le_sixteen_mul`: if a stochastic
matrix `P` satisfies detailed balance with respect to a positive probability vector `π` and
every row of `Pᵗ` is within total variation distance `1/4` of `π` for all `t ≥ τ`, then some
multicommodity flow routing `π(x) π(y)` from `x` to `y` puts at most `16 τ · π(u) P(u, v)`
on every oriented edge `(u, v)`.

Sinclair's Theorem 8 states that the resistance is at most `16 τ`. Its key step, Lemma 7,
is proved as `MathlibExt.Probability.Flows.div_eight_le_pow_apply`; the flow built from
the `2τ`-step trajectories of the chain, with cycles bypassed, is proved here.

Sinclair concludes from this and Cheeger's inequality (`MathlibExt.Probability.MarkovChainCheeger`),
with Theorems 3, 5 and 5′ (`MathlibExt.Probability.CanonicalPaths` and
`MathlibExt.Probability.MulticommodityFlow`), that a reversible chain mixes rapidly if and only
if it supports a flow of polynomially bounded congestion, if and only if its conductance is at
least an inverse polynomial. The mixing-time estimate also depends on the smallest eigenvalue
(handled, for instance, by making the chain lazy) and on
`log(1/π(x))` for the starting state `x`.

## References

* A. Sinclair, "Improved bounds for mixing rates of Markov chains and multicommodity flow",
  *Combinatorics, Probability and Computing* **1** (1992), 351–370: Theorem 2, Lemma 7,
  Theorem 8.
* A. Sinclair and M. Jerrum, "Approximate counting, uniform generation and rapidly mixing Markov
  chains", *Information and Computation* **82** (1989), 93–133: Lemma 3.3.
-/

@[expose] public section

open Finset Matrix
open MathlibExt.Probability.CanonicalPaths MathlibExt.Probability.MarkovMixing
open MathlibExt.Probability.Flows ProbabilityTheory

namespace MathlibExt.Probability.MulticommodityFlowWanted

/-- The suffix of `l` starting at its first occurrence of `x`. -/
private def suffixFrom {S : Type*} [DecidableEq S] : S → List S → List S
  | _, [] => []
  | x, v :: l => if v = x then v :: l else suffixFrom x l

/-- The suffix of `l` starting at `x` is a sublist of `l`. -/
private theorem suffixFrom_sublist {S : Type*} [DecidableEq S] (x : S) (l : List S) :
    List.Sublist (suffixFrom x l) l := by
  induction l with
  | nil => simp [suffixFrom]
  | cons v l ih =>
    simp only [suffixFrom]
    split_ifs with h
    · exact List.Sublist.refl _
    · exact ih.cons _

/-- If `x` occurs in `l`, the suffix starting at `x` starts with `x`. -/
private theorem suffixFrom_eq_of_mem {S : Type*} [DecidableEq S] (x : S) :
    ∀ l : List S, x ∈ l → ∃ t, suffixFrom x l = x :: t := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons v l ih =>
    intro h
    simp only [suffixFrom]
    split_ifs with hv
    · exact ⟨l, by rw [hv]⟩
    · have hx : x ∈ l := by
        simp only [List.mem_cons] at h; exact h.resolve_left (fun e => hv e.symm)
      obtain ⟨t, ht⟩ := ih hx
      exact ⟨t, ht⟩

/-- A suffix of a nodup list is nodup. -/
private theorem suffixFrom_nodup_of_nodup {S : Type*} [DecidableEq S] {x : S} {l : List S}
    (h : l.Nodup) : (suffixFrom x l).Nodup :=
  h.sublist (suffixFrom_sublist x l)

/-- A pair occurring in `pathEdges` cannot start at a state absent from the tail. -/
private theorem not_mem_pathEdges_of_not_mem {S : Type*} {x v : S} {l : List S}
    (h1 : x ∉ v :: l) : ∀ {b : S}, x ∉ b :: l → (x, v) ∉ pathEdges b l := by
  induction l with
  | nil => intro b _; simp [pathEdges]
  | cons w l ih =>
    intro b h2 hmem
    simp only [pathEdges, List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · rw [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact h2 (by simp)
    · have h1' : x ∉ v :: l := fun hm => h1 (by
        simp only [List.mem_cons] at hm ⊢
        rcases hm with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hm))
      have h2' : x ∉ w :: l := fun hm => h2 (List.mem_cons_of_mem b hm)
      exact ih h1' h2' hmem

/-- The edges of a simple path are distinct. -/
private theorem pathEdges_nodup {S : Type*} {x : S} {l : List S} (h : (x :: l).Nodup) :
    (pathEdges x l).Nodup := by
  induction l generalizing x with
  | nil => simp [pathEdges]
  | cons v l ih =>
    have h1 : (v :: l).Nodup := (List.nodup_cons.mp h).2
    have h2 : x ∉ v :: l := (List.nodup_cons.mp h).1
    simp only [pathEdges, List.nodup_cons]
    exact ⟨not_mem_pathEdges_of_not_mem h2 h2, ih h1⟩

/-- Bypassing cycles preserves the endpoint of a path. -/
private theorem pathEnd_suffixFrom {S : Type*} [DecidableEq S] {x : S} :
    ∀ {a : S} {s : List S}, x ∈ a :: s →
    pathEnd x (suffixFrom x (a :: s)).tail = pathEnd a s := by
  intro a s
  induction s generalizing a with
  | nil =>
    intro hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    simp [suffixFrom]
  | cons b s ih =>
    intro hx
    have hstep : suffixFrom x (a :: b :: s) =
        if a = x then a :: b :: s else suffixFrom x (b :: s) := rfl
    rw [hstep]
    split_ifs with hav
    · subst hav; rfl
    · have hx' : x ∈ b :: s := by
        simp only [List.mem_cons] at hx ⊢
        rcases hx with h | h
        · exact absurd h.symm hav
        · exact h
      exact ih hx'

/-- The edges of a suffix of a path are edges of the path. -/
private theorem pathEdges_suffixFrom_subset {S : Type*} [DecidableEq S] {x : S} :
    ∀ {a : S} {s : List S}, x ∈ a :: s →
    ∀ e ∈ pathEdges x (suffixFrom x (a :: s)).tail, e ∈ pathEdges a s := by
  intro a s
  induction s generalizing a with
  | nil =>
    intro hx e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    rw [show suffixFrom x [x] = [x] by simp [suffixFrom]] at he
    exact (List.not_mem_nil he).elim
  | cons b s ih =>
    intro hx e he
    have hstep : suffixFrom x (a :: b :: s) =
        if a = x then a :: b :: s else suffixFrom x (b :: s) := rfl
    rw [hstep] at he
    split_ifs at he with hav
    · subst hav
      exact he
    · have hx' : x ∈ b :: s := by
        simp only [List.mem_cons] at hx ⊢
        rcases hx with h | h
        · exact absurd h.symm hav
        · exact h
      have he' := ih hx' e he
      simp only [pathEdges, List.mem_cons]
      exact Or.inr he'

/-- Bypass cycles in a path, scanning from the end and dropping the segment between
two occurrences of the same state. -/
private def cycleBypass {S : Type*} [DecidableEq S] : S → List S → List S
  | _, [] => []
  | x, v :: l =>
      if x ∈ v :: cycleBypass v l then
        (suffixFrom x (v :: cycleBypass v l)).tail
      else v :: cycleBypass v l

/-- Cycle bypassing yields a simple path with the same endpoint and a subset of the edges. -/
private theorem cycleBypass_spec {S : Type*} [DecidableEq S] :
    ∀ (x : S) (l : List S),
    (x :: cycleBypass x l).Nodup ∧ pathEnd x (cycleBypass x l) = pathEnd x l ∧
      ∀ e ∈ pathEdges x (cycleBypass x l), e ∈ pathEdges x l := by
  intro x l
  induction l generalizing x with
  | nil => simp [cycleBypass, pathEdges, pathEnd]
  | cons v l ih =>
    obtain ⟨hnod, hend, hedge⟩ := ih (x := v)
    by_cases hx : x ∈ v :: cycleBypass v l
    · obtain ⟨t, ht⟩ := suffixFrom_eq_of_mem x (v :: cycleBypass v l) hx
      have hred : cycleBypass x (v :: l) = t := by
        change (if x ∈ v :: cycleBypass v l then
            (suffixFrom x (v :: cycleBypass v l)).tail else v :: cycleBypass v l) = t
        simp only [hx, ↓reduceIte, ht, List.tail_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [hred, ← ht]
        exact suffixFrom_nodup_of_nodup hnod
      · rw [hred]
        have htail : (suffixFrom x (v :: cycleBypass v l)).tail = t := by
          rw [ht, List.tail_cons]
        calc pathEnd x t = pathEnd v (cycleBypass v l) := by
              rw [← htail]; exact pathEnd_suffixFrom hx
          _ = pathEnd v l := hend
          _ = pathEnd x (v :: l) := rfl
      · intro e he
        rw [hred] at he
        have htail : (suffixFrom x (v :: cycleBypass v l)).tail = t := by
          rw [ht, List.tail_cons]
        rw [← htail] at he
        have he1 := pathEdges_suffixFrom_subset hx e he
        have he2 := hedge e he1
        simp only [pathEdges, List.mem_cons]
        exact Or.inr he2
    · have hred : cycleBypass x (v :: l) = v :: cycleBypass v l := by
        change (if x ∈ v :: cycleBypass v l then
            (suffixFrom x (v :: cycleBypass v l)).tail else v :: cycleBypass v l) =
          v :: cycleBypass v l
        simp only [hx, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rw [hred]; exact List.nodup_cons.mpr ⟨hx, hnod⟩
      · rw [hred]; exact hend
      · intro e he
        rw [hred] at he
        simp only [pathEdges, List.mem_cons] at he ⊢
        rcases he with he | he
        · exact Or.inl he
        · exact Or.inr (hedge e he)

/-- All lists of length `n` over `S`. -/
private def walkFinset {S : Type*} [Fintype S] [DecidableEq S] : ℕ → Finset (List S)
  | 0 => {[]}
  | n + 1 => (Finset.univ : Finset S).biUnion
      fun v => (walkFinset n).image (fun l => v :: l)

/-- A list is a walk of length `n` exactly when it has length `n`. -/
private theorem mem_walkFinset {S : Type*} [Fintype S] [DecidableEq S] :
    ∀ {n : ℕ} {l : List S}, l ∈ walkFinset (S := S) n ↔ l.length = n := by
  intro n
  induction n with
  | zero => intro l; simp [walkFinset]
  | succ n ih =>
    intro l
    constructor
    · intro h
      simp only [walkFinset, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
        true_and] at h
      obtain ⟨v, l', hl', rfl⟩ := h
      simp [ih.mp hl']
    · intro h
      cases l with
      | nil => simp at h
      | cons v l =>
        simp only [List.length_cons, Nat.succ.injEq] at h
        simp only [walkFinset, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact ⟨v, l, ih.mpr h, rfl⟩

/-- Splitting the walks of length `n + 1` by their first step. -/
private theorem sum_walkFinset_succ {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}
    (F : List S → ℝ) :
    ∑ l ∈ walkFinset (S := S) (n + 1), F l = ∑ v, ∑ l ∈ walkFinset n, F (v :: l) := by
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset S) : Set S)
      fun v => (walkFinset (S := S) n).image (fun l => v :: l) := by
    intro v _ w _ hvw
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro l hl1 hl2
    simp only [Finset.mem_image] at hl1 hl2
    obtain ⟨l1, _, h1⟩ := hl1
    obtain ⟨l2, _, h2⟩ := hl2
    exact hvw (List.cons.inj (h1.trans h2.symm)).1
  have hdef : walkFinset (S := S) (n + 1) =
      (Finset.univ : Finset S).biUnion
        (fun v : S => (walkFinset (S := S) n).image (fun l => v :: l)) := rfl
  calc ∑ l ∈ walkFinset (S := S) (n + 1), F l
      = ∑ l ∈ (Finset.univ : Finset S).biUnion
          (fun v : S => (walkFinset (S := S) n).image (fun l => v :: l)), F l := by
        rw [hdef]
    _ = ∑ v, ∑ l ∈ (walkFinset (S := S) n).image (fun l => v :: l), F l :=
        Finset.sum_biUnion hdisj
    _ = ∑ v, ∑ l ∈ walkFinset (S := S) n, F (v :: l) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact (List.cons.inj hab).2

/-- The probability of a walk. -/
private def walkProb {S : Type*} (P : Matrix S S ℝ) : S → List S → ℝ
  | _, [] => 1
  | x, v :: l => P x v * walkProb P v l

/-- Walk probabilities are nonnegative when the transition probabilities are. -/
private theorem walkProb_nonneg {S : Type*} {P : Matrix S S ℝ}
    (hP : ∀ x y, 0 ≤ P x y) : ∀ (x : S) (l : List S), 0 ≤ walkProb P x l := by
  intro x l
  induction l generalizing x with
  | nil => simp [walkProb]
  | cons v l ih => simp only [walkProb]; exact mul_nonneg (hP x v) (ih v)

/-- A walk using a zero-probability edge has probability zero. -/
private theorem walkProb_eq_zero_of_mem {S : Type*} {P : Matrix S S ℝ} {x : S}
    {l : List S} {e : S × S} (he : e ∈ pathEdges x l) (h0 : P e.1 e.2 = 0) :
    walkProb P x l = 0 := by
  induction l generalizing x with
  | nil => exact (List.not_mem_nil he).elim
  | cons v l ih =>
    simp only [pathEdges, List.mem_cons] at he
    rcases he with he | he
    · rw [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [walkProb, h0, zero_mul]
    · have hzero := ih he
      simp only [walkProb, hzero, mul_zero]

/-- The walk probabilities from any start sum to one. -/
private theorem sum_walkProb_eq_one {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) :
    ∀ (n : ℕ) (x : S), ∑ l ∈ walkFinset (S := S) n, walkProb P x l = 1 := by
  intro n
  induction n with
  | zero => intro x; simp [walkFinset, walkProb]
  | succ n ih =>
    intro x
    rw [sum_walkFinset_succ]
    calc ∑ v, ∑ l ∈ walkFinset (S := S) n, walkProb P x (v :: l)
        = ∑ v, P x v * 1 := Finset.sum_congr rfl fun v _ => by
          simp only [walkProb]
          rw [← Finset.mul_sum, ih v, mul_one]
      _ = 1 := by simp [sum_row_of_mem_rowStochastic hP x]

/-- A matrix power is the sum of the probabilities of the walks with the given endpoint. -/
private theorem pow_eq_sum_walkProb {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} :
    ∀ (n : ℕ) (x y : S),
      (P ^ n) x y =
        ∑ l ∈ walkFinset (S := S) n,
          if pathEnd x l = y then walkProb P x l else 0 := by
  intro n
  induction n with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [h, walkFinset, walkProb, pathEnd]
  | succ n ih =>
    intro x y
    rw [sum_walkFinset_succ]
    have hstep : ∀ v, (∑ l ∈ walkFinset (S := S) n,
        (if pathEnd x (v :: l) = y then walkProb P x (v :: l) else 0)) =
        P x v * (P ^ n) v y := by
      intro v
      calc ∑ l ∈ walkFinset (S := S) n,
            (if pathEnd x (v :: l) = y then walkProb P x (v :: l) else 0)
          = ∑ l ∈ walkFinset (S := S) n,
              P x v * (if pathEnd v l = y then walkProb P v l else 0) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            simp only [walkProb, pathEnd]
            by_cases h : pathEnd v l = y <;> simp [h]
        _ = P x v * ∑ l ∈ walkFinset (S := S) n,
              (if pathEnd v l = y then walkProb P v l else 0) :=
            (Finset.mul_sum ..).symm
        _ = P x v * (P ^ n) v y := by rw [ih v y]
    rw [Finset.sum_congr rfl fun v _ => hstep v]
    rw [pow_succ', Matrix.mul_apply]

/-- Whether the `k`-th edge of a path from `x` is `(u, v)`. -/
private def edgeAt {S : Type*} [DecidableEq S] : S → List S → ℕ → S → S → Bool
  | _, [], _, _, _ => false
  | x, v :: _, 0, u, w => decide (x = u ∧ v = w)
  | _, v :: l, k + 1, u, w => edgeAt v l k u w

/-- An edge of a path is its `k`-th edge for some `k`. -/
private theorem edgeAt_mem_of_mem_pathEdges {S : Type*} [DecidableEq S] {x : S}
    {l : List S} {e : S × S} (he : e ∈ pathEdges x l) :
    ∃ k, k < l.length ∧ edgeAt x l k e.1 e.2 = true := by
  induction l generalizing x with
  | nil => exact (List.not_mem_nil he).elim
  | cons v l ih =>
    simp only [pathEdges, List.mem_cons] at he
    rcases he with he | he
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp he
      exact ⟨0, by simp, by simp [edgeAt]⟩
    · obtain ⟨k, hk, hke⟩ := ih he
      exact ⟨k + 1, by simpa using Nat.succ_lt_succ hk, hke⟩

/-- An edge occurring at position `k` in a path is an edge of the path. -/
private theorem mem_pathEdges_of_edgeAt {S : Type*} [DecidableEq S] :
    ∀ {x : S} {l : List S} {k : ℕ} {u v : S},
    edgeAt x l k u v = true → (u, v) ∈ pathEdges x l := by
  intro x l k u v
  induction l generalizing x k with
  | nil => intro h; simp [edgeAt] at h
  | cons w l ih =>
    intro h
    cases k with
    | zero =>
      simp only [pathEdges, List.mem_cons]
      have hdec : decide (x = u ∧ w = v) = true := h
      rw [decide_eq_true_eq] at hdec
      exact Or.inl (Prod.ext hdec.1.symm hdec.2.symm)
    | succ k =>
      simp only [pathEdges, List.mem_cons]
      exact Or.inr (ih h)

/-- The probability that the `k`-th step of a walk is `(u, v)`. -/
private theorem sum_edgeAt {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP : P ∈ rowStochastic ℝ S) :
    ∀ (k N : ℕ) (x : S), k < N → ∀ (u v : S),
      ∑ l ∈ walkFinset (S := S) N,
          (if edgeAt x l k u v then walkProb P x l else 0) =
        (P ^ k) x u * P u v := by
  intro k
  induction k with
  | zero =>
    intro N x hN u v
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [sum_walkFinset_succ]
    have hinner : ∀ w : S, (∑ l ∈ walkFinset (S := S) m,
        (if edgeAt x (w :: l) 0 u v then walkProb P x (w :: l) else 0)) =
        if w = v then (if x = u then P x v else 0) else 0 := by
      intro w
      by_cases h : x = u ∧ w = v
      · have hed : ∀ l : List S, edgeAt x (w :: l) 0 u v = true := fun l => by
          exact decide_eq_true h
        calc ∑ l ∈ walkFinset (S := S) m,
              (if edgeAt x (w :: l) 0 u v then walkProb P x (w :: l) else 0)
            = ∑ l ∈ walkFinset (S := S) m, walkProb P x (w :: l) :=
              Finset.sum_congr rfl fun l _ => by simp [hed l]
          _ = P x w := by
              simp only [walkProb]
              rw [← Finset.mul_sum, sum_walkProb_eq_one hP m w, mul_one]
          _ = if w = v then (if x = u then P x v else 0) else 0 := by
              simp [h.1, h.2]
      · have hzero : ∀ l ∈ walkFinset (S := S) m,
            (if edgeAt x (w :: l) 0 u v then walkProb P x (w :: l) else 0) = 0 := by
          intro l _
          have hed : edgeAt x (w :: l) 0 u v = false := decide_eq_false h
          simp [hed]
        rw [Finset.sum_congr rfl hzero]
        by_cases hw : w = v
        · simp [hw, show x ≠ u from fun hx => h ⟨hx, hw⟩]
        · simp [hw]
    rw [Finset.sum_congr rfl fun w _ => hinner w]
    by_cases hx : x = u
    · subst hx
      simp [Finset.mem_univ]
    · have hz : ∀ w : S,
          (if w = v then (if x = u then P x v else 0) else 0) = 0 := by
        intro w; by_cases hw : w = v <;> simp [hw, hx]
      rw [Finset.sum_congr rfl fun w _ => hz w]
      simp [hx, pow_zero]
  | succ k ih =>
    intro N x hN u v
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [sum_walkFinset_succ]
    have hinner : ∀ w : S, (∑ l ∈ walkFinset (S := S) m,
        (if edgeAt x (w :: l) (k + 1) u v then walkProb P x (w :: l) else 0)) =
        P x w * ((P ^ k) w u * P u v) := by
      intro w
      calc ∑ l ∈ walkFinset (S := S) m,
            (if edgeAt x (w :: l) (k + 1) u v then walkProb P x (w :: l) else 0)
          = ∑ l ∈ walkFinset (S := S) m,
              (if edgeAt w l k u v then P x w * walkProb P w l else 0) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            change (if edgeAt w l k u v then walkProb P x (w :: l) else 0) =
              (if edgeAt w l k u v then P x w * walkProb P w l else 0)
            simp only [walkProb]
        _ = P x w * ∑ l ∈ walkFinset (S := S) m,
              (if edgeAt w l k u v then walkProb P w l else 0) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by
              by_cases h : edgeAt w l k u v <;> simp [h]
        _ = P x w * ((P ^ k) w u * P u v) := by
            rw [ih m w (by omega) u v]
    rw [Finset.sum_congr rfl fun w _ => hinner w]
    calc ∑ w, P x w * ((P ^ k) w u * P u v)
        = (∑ w, P x w * (P ^ k) w u) * P u v := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun w _ => by ring
      _ = (P ^ (k + 1)) x u * P u v := by
          rw [pow_succ', Matrix.mul_apply]

/-- The total probability of the `N`-step walks from `x` to `y` that use the edge
`(u, v)`. -/
private noncomputable def walkUseSum {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (N : ℕ) (x y u v : S) : ℝ :=
  ∑ l ∈ (walkFinset (S := S) N).filter (fun l => pathEnd x l = y),
    walkProb P x l * (if (u, v) ∈ pathEdges x l then 1 else 0)

/-- Summing the walk-use sums over all endpoints counts every walk once. -/
private theorem sum_walkUseSum {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} {N : ℕ} {x u v : S} :
    ∑ y, walkUseSum P N x y u v =
      ∑ l ∈ walkFinset (S := S) N,
        walkProb P x l * (if (u, v) ∈ pathEdges x l then 1 else 0) := by
  have hfib := Finset.sum_fiberwise_eq_sum_filter (walkFinset (S := S) N) Finset.univ
    (pathEnd x)
    (fun l => walkProb P x l * (if (u, v) ∈ pathEdges x l then 1 else 0))
  rw [Finset.filter_true_of_mem (fun l _ => Finset.mem_univ (pathEnd x l))] at hfib
  simp only [walkUseSum]
  exact hfib

/-- The walks using an edge are covered by the walks whose `k`-th step is that edge. -/
private theorem walkUseSum_le_stepSum {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {x u v : S} :
    ∑ y, walkUseSum P N x y u v ≤
      ∑ k ∈ Finset.range N, (P ^ k) x u * P u v := by
  rw [sum_walkUseSum]
  have hnn : ∀ x y, 0 ≤ P x y := fun a b => nonneg_of_mem_rowStochastic hP
  have hD : ∀ l ∈ walkFinset (S := S) N,
      walkProb P x l * (if (u, v) ∈ pathEdges x l then 1 else 0) ≤
        ∑ k ∈ Finset.range N, (if edgeAt x l k u v then walkProb P x l else 0) := by
    intro l hl
    have hlen : l.length = N := mem_walkFinset.mp hl
    have hterm : ∀ k : ℕ, 0 ≤
        (if edgeAt x l k u v then walkProb P x l else 0) := by
      intro k
      by_cases h : edgeAt x l k u v
      · simp [h, walkProb_nonneg hnn x l]
      · simp [h]
    by_cases hm : (u, v) ∈ pathEdges x l
    · rw [ite_eq_left hm, mul_one]
      obtain ⟨k, hk, hke⟩ := edgeAt_mem_of_mem_pathEdges hm
      have hkN : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      calc walkProb P x l
          = (if edgeAt x l k u v then walkProb P x l else 0) := by simp [hke]
        _ ≤ ∑ k' ∈ Finset.range N,
              (if edgeAt x l k' u v then walkProb P x l else 0) :=
            Finset.single_le_sum (fun k' _ => hterm k') hkN
    · rw [ite_eq_right hm, mul_zero]
      exact Finset.sum_nonneg fun k _ => hterm k
  calc ∑ l ∈ walkFinset (S := S) N,
        walkProb P x l * (if (u, v) ∈ pathEdges x l then 1 else 0)
      ≤ ∑ l ∈ walkFinset (S := S) N, ∑ k ∈ Finset.range N,
          (if edgeAt x l k u v then walkProb P x l else 0) :=
        Finset.sum_le_sum fun l hl => hD l hl
    _ = ∑ k ∈ Finset.range N, ∑ l ∈ walkFinset (S := S) N,
          (if edgeAt x l k u v then walkProb P x l else 0) := Finset.sum_comm
    _ = ∑ k ∈ Finset.range N, (P ^ k) x u * P u v :=
        Finset.sum_congr rfl fun k hk =>
          sum_edgeAt hP k N x (Finset.mem_range.mp hk) u v

/-- Detailed balance makes `π` stationary. -/
private theorem sum_mul_eq {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ}
    (hP : P ∈ rowStochastic ℝ S) (hrev : IsDetailedBalance π P) (w : S) :
    ∑ x, π x * P x w = π w := by
  calc ∑ x, π x * P x w = ∑ x, π w * P w x :=
        Finset.sum_congr rfl fun x _ => hrev x w
    _ = π w * ∑ x, P w x := by rw [Finset.mul_sum]
    _ = π w := by rw [sum_row_of_mem_rowStochastic hP w, mul_one]

/-- Stationarity passes to powers of `P`. -/
private theorem sum_mul_pow_eq {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ}
    (hP : P ∈ rowStochastic ℝ S) (hrev : IsDetailedBalance π P) :
    ∀ (k : ℕ) (u : S), ∑ x, π x * (P ^ k) x u = π u := by
  intro k
  induction k with
  | zero =>
    intro u
    simp only [pow_zero]
    rw [Finset.sum_eq_single u]
    · simp
    · intro x _ hxu; simp [Matrix.one_apply_ne hxu]
    · simp
  | succ k ih =>
    intro u
    calc ∑ x, π x * (P ^ (k + 1)) x u
        = ∑ x, ∑ w, π x * (P x w * (P ^ k) w u) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
      _ = ∑ w, (∑ x, π x * P x w) * (P ^ k) w u := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ w, π w * (P ^ k) w u := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [sum_mul_eq hP hrev w]
      _ = π u := ih u

/-- The walks from `x` to `y` whose cycle bypass is `p`. -/
private def flowFiber {S : Type*} [Fintype S] [DecidableEq S] (_P : Matrix S S ℝ)
    (N : ℕ) (x y : S) (p : List S) : Finset (List S) :=
  (walkFinset (S := S) N).filter (fun l => pathEnd x l = y ∧ cycleBypass x l = p)

/-- The amount of commodity `(x, y)` sent along the simple path `p`: the total
probability of the `N`-step walks from `x` to `y` bypassing to `p`, rescaled so that
the total over all `p` is `π(x) π(y)`. -/
private noncomputable def flowWeight {S : Type*} [Fintype S] [DecidableEq S]
    (π : S → ℝ) (P : Matrix S S ℝ) (N : ℕ) (x y : S) (p : List S) : ℝ :=
  (π x * π y / (P ^ N) x y) *
    ∑ l ∈ flowFiber P N x y p, walkProb P x l

/-- The simple paths carrying commodity `(x, y)`: cycle bypasses of the `N`-step
walks from `x` to `y` that carry positive probability. -/
private noncomputable def flowPaths {S : Type*} [Fintype S] [DecidableEq S]
    (_π : S → ℝ) (P : Matrix S S ℝ) (N : ℕ) (x y : S) : Finset (List S) :=
  (((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).image (cycleBypass x)).filter
    (fun p => 0 < ∑ l ∈ flowFiber P N x y p, walkProb P x l)

/-- The fiber over `p` is the fiber of cycle bypassing among the walks ending at `y`. -/
private theorem flowFiber_eq_filter {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} {N : ℕ} {x y : S} {p : List S} :
    flowFiber P N x y p =
      ((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).filter
        (fun l => cycleBypass x l = p) := by
  simp [flowFiber, Finset.filter_filter]

/-- Fiber sums are nonnegative. -/
private theorem flowFiberSum_nonneg {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {x y : S} {p : List S} :
    0 ≤ ∑ l ∈ flowFiber P N x y p, walkProb P x l :=
  Finset.sum_nonneg fun l _ =>
    walkProb_nonneg (fun _ _ => nonneg_of_mem_rowStochastic hP) x l

/-- Membership in the flow paths, unfolded. -/
private theorem mem_flowPaths {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ} {N : ℕ} {x y : S} {p : List S} :
    p ∈ flowPaths π P N x y ↔
      p ∈ ((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).image
          (cycleBypass x) ∧
        0 < ∑ l ∈ flowFiber P N x y p, walkProb P x l := by
  simp [flowPaths]

/-- The flow weights are nonnegative. -/
private theorem flowWeight_nonneg {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hπ : ∀ x, 0 < π x) {N : ℕ}
    (hden : ∀ x y, 0 < (P ^ N) x y) (x y : S) (p : List S) :
    0 ≤ flowWeight π P N x y p := by
  simp only [flowWeight]
  exact mul_nonneg
    (div_nonneg (mul_nonneg (hπ x).le (hπ y).le) (hden x y).le)
    (flowFiberSum_nonneg hP)

/-- A flow path with positive fiber sum comes from a positive-probability walk. -/
private theorem exists_walkProb_pos_of_mem_flowPaths {S : Type*} [Fintype S] [DecidableEq S]
    {π : S → ℝ} {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {x y : S}
    {p : List S} (hp : p ∈ flowPaths π P N x y) :
    ∃ l ∈ flowFiber P N x y p, 0 < walkProb P x l := by
  have hpos : 0 < ∑ l ∈ flowFiber P N x y p, walkProb P x l := (mem_flowPaths.mp hp).2
  by_contra hcon
  have hle : ∀ l ∈ flowFiber P N x y p, walkProb P x l ≤ 0 := fun l hl =>
    le_of_not_gt (fun h => hcon ⟨l, hl, h⟩)
  have hzero : ∑ l ∈ flowFiber P N x y p, walkProb P x l = 0 :=
    Finset.sum_eq_zero_iff_of_nonneg (fun l hl =>
      walkProb_nonneg (fun _ _ => nonneg_of_mem_rowStochastic hP) x l) |>.mpr
      (fun l hl => le_antisymm (hle l hl)
        (walkProb_nonneg (fun _ _ => nonneg_of_mem_rowStochastic hP) x l))
  exact absurd hzero (ne_of_gt hpos)

/-- The flow paths end at `y` and are simple. -/
private theorem flowPath_spec {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {x y : S} {p : List S}
    (hp : p ∈ flowPaths π P N x y) :
    pathEnd x p = y ∧ (x :: p).Nodup := by
  obtain ⟨l, hl, hlpos⟩ := exists_walkProb_pos_of_mem_flowPaths hP hp
  simp only [flowFiber, Finset.mem_filter] at hl
  obtain ⟨-, hend, hbyp⟩ := hl
  obtain ⟨hnod, hend', -⟩ := cycleBypass_spec x l
  exact ⟨by rw [← hbyp, hend']; exact hend, by rw [← hbyp]; exact hnod⟩

/-- Every edge of a flow path has positive capacity. -/
private theorem flowEdgePos {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hπ : ∀ x, 0 < π x) {N : ℕ}
    {x y : S} {p : List S} (hp : p ∈ flowPaths π P N x y) {e : S × S}
    (he : e ∈ pathEdges x p) : 0 < π e.1 * P e.1 e.2 := by
  obtain ⟨l, hl, hlpos⟩ := exists_walkProb_pos_of_mem_flowPaths hP hp
  simp only [flowFiber, Finset.mem_filter] at hl
  obtain ⟨-, hend, hbyp⟩ := hl
  have he' : e ∈ pathEdges x l := (cycleBypass_spec x l).2.2 e (hbyp ▸ he)
  have hPpos : 0 < P e.1 e.2 := by
    by_contra hcon
    have h0 : P e.1 e.2 = 0 :=
      le_antisymm (le_of_not_gt hcon) (nonneg_of_mem_rowStochastic hP)
    exact absurd (walkProb_eq_zero_of_mem he' h0) (ne_of_gt hlpos)
  exact mul_pos (hπ _) hPpos

/-- The flow weights sum to the demand `π(x) π(y)`. -/
private theorem flowWeight_sum_eq {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ}
    (hden : ∀ x y, 0 < (P ^ N) x y) (x y : S) :
    ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p = π x * π y := by
  have hstep1 : ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p =
      ∑ p ∈ ((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).image
          (cycleBypass x), flowWeight π P N x y p := by
    unfold flowPaths
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hq : 0 < ∑ l ∈ flowFiber P N x y p, walkProb P x l
    · simp [hq]
    · have hq0 : ∑ l ∈ flowFiber P N x y p, walkProb P x l = 0 :=
        le_antisymm (le_of_not_gt hq) (flowFiberSum_nonneg hP)
      simp [flowWeight, hq0]
  have hstep2 : ∑ p ∈ ((walkFinset (S := S) N).filter
        (fun l => pathEnd x l = y)).image (cycleBypass x),
        flowWeight π P N x y p =
      (π x * π y / (P ^ N) x y) * ∑ p ∈ ((walkFinset (S := S) N).filter
        (fun l => pathEnd x l = y)).image (cycleBypass x),
        ∑ l ∈ flowFiber P N x y p, walkProb P x l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by simp [flowWeight]
  have hstep3 : ∑ p ∈ ((walkFinset (S := S) N).filter
        (fun l => pathEnd x l = y)).image (cycleBypass x),
        ∑ l ∈ flowFiber P N x y p, walkProb P x l =
      ∑ l ∈ (walkFinset (S := S) N).filter (fun l => pathEnd x l = y),
        walkProb P x l := by
    calc ∑ p ∈ ((walkFinset (S := S) N).filter
          (fun l => pathEnd x l = y)).image (cycleBypass x),
          ∑ l ∈ flowFiber P N x y p, walkProb P x l
        = ∑ p ∈ ((walkFinset (S := S) N).filter
            (fun l => pathEnd x l = y)).image (cycleBypass x),
            ∑ l ∈ ((walkFinset (S := S) N).filter
              (fun l => pathEnd x l = y)).filter (fun l => cycleBypass x l = p),
              walkProb P x l := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [flowFiber_eq_filter]
      _ = ∑ l ∈ ((walkFinset (S := S) N).filter
            (fun l => pathEnd x l = y)).filter
            (fun l => cycleBypass x l ∈ ((walkFinset (S := S) N).filter
              (fun l => pathEnd x l = y)).image (cycleBypass x)),
            walkProb P x l :=
          Finset.sum_fiberwise_eq_sum_filter _ _ _ _
      _ = ∑ l ∈ (walkFinset (S := S) N).filter (fun l => pathEnd x l = y),
            walkProb P x l := by
          rw [Finset.filter_true_of_mem (fun l hl =>
            Finset.mem_image_of_mem _ hl)]
  have hstep4 : ∑ l ∈ (walkFinset (S := S) N).filter (fun l => pathEnd x l = y),
      walkProb P x l = (P ^ N) x y := by
    rw [pow_eq_sum_walkProb N x y, Finset.sum_filter]
  rw [hstep1, hstep2, hstep3, hstep4]
  exact div_mul_cancel₀ _ (ne_of_gt (hden x y))

/-- The multicommodity flow built from the `N`-step walks, with cycles bypassed. -/
private noncomputable def mkFlow {S : Type*} [Fintype S] [DecidableEq S]
    {π : S → ℝ} {P : Matrix S S ℝ} (N : ℕ)
    (hP : P ∈ rowStochastic ℝ S) (hπ : ∀ x, 0 < π x)
    (hden : ∀ x y, 0 < (P ^ N) x y) : MulticommodityFlow π P where
  paths := flowPaths π P N
  weight := flowWeight π P N
  weight_nonneg := fun x y p => flowWeight_nonneg hP hπ hden x y p
  pathEnd_eq := fun _x _y _ _p hp => (flowPath_spec hP hp).1
  nodup := fun _x _y _ _p hp => (flowPath_spec hP hp).2
  edge_pos := fun _x _y _ _p hp _e he => flowEdgePos hP hπ hp he
  demand := fun x y _ => flowWeight_sum_eq hP hden x y

/-- The load of the flow built from walks is at most `8 N` times the capacity. -/
private theorem mkFlow_load_le {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ}
    {P : Matrix S S ℝ} {N : ℕ} (hP : P ∈ rowStochastic ℝ S)
    (hπ : ∀ x, 0 < π x) (hrev : IsDetailedBalance π P)
    (hden : ∀ x y, 0 < (P ^ N) x y) (hlow : ∀ x y, π y / 8 ≤ (P ^ N) x y)
    (u v : S) :
    (mkFlow N hP hπ hden).load u v ≤ 8 * (N : ℝ) * (π u * P u v) := by
  have hnn : ∀ a b, 0 ≤ P a b := fun a b => nonneg_of_mem_rowStochastic hP
  have hcount : ∀ x y, ∀ p ∈ flowPaths π P N x y,
      ((pathEdges x p).count (u, v) : ℝ) ≤
        if (u, v) ∈ pathEdges x p then 1 else 0 := by
    intro x y p hp
    by_cases hm : (u, v) ∈ pathEdges x p
    · rw [ite_eq_left hm]
      have hnod : (x :: p).Nodup := (flowPath_spec hP hp).2
      exact_mod_cast List.nodup_iff_count_le_one.mp (pathEdges_nodup hnod) (u, v)
    · rw [ite_eq_right hm]
      have hz : (pathEdges x p).count (u, v) = 0 := List.count_eq_zero.mpr hm
      simp [hz]
  have hpath : ∀ x y,
      ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
          ((pathEdges x p).count (u, v) : ℝ) ≤
        (π x * π y / (P ^ N) x y) * walkUseSum P N x y u v := by
    intro x y
    have hA : ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
          ((pathEdges x p).count (u, v) : ℝ) ≤
        ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
          (if (u, v) ∈ pathEdges x p then 1 else 0) :=
      Finset.sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_left (hcount x y p hp) (flowWeight_nonneg hP hπ hden x y p)
    have hB : ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
          (if (u, v) ∈ pathEdges x p then 1 else 0) ≤
        ∑ p ∈ ((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).image
            (cycleBypass x), flowWeight π P N x y p *
          (if (u, v) ∈ pathEdges x p then 1 else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        exact (mem_flowPaths.mp hp).1
      · intro p _ _
        exact mul_nonneg (flowWeight_nonneg hP hπ hden x y p)
          (by by_cases h : (u, v) ∈ pathEdges x p <;> simp [h])
    have hC : ∑ p ∈ ((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).image
          (cycleBypass x), flowWeight π P N x y p *
          (if (u, v) ∈ pathEdges x p then 1 else 0) ≤
        (π x * π y / (P ^ N) x y) * walkUseSum P N x y u v := by
      calc ∑ p ∈ ((walkFinset (S := S) N).filter (fun l => pathEnd x l = y)).image
            (cycleBypass x), flowWeight π P N x y p *
            (if (u, v) ∈ pathEdges x p then 1 else 0)
          = (π x * π y / (P ^ N) x y) * ∑ p ∈ ((walkFinset (S := S) N).filter
              (fun l => pathEnd x l = y)).image (cycleBypass x),
              (∑ l ∈ flowFiber P N x y p, walkProb P x l) *
              (if (u, v) ∈ pathEdges x p then 1 else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            simp only [flowWeight]
            ring
        _ ≤ (π x * π y / (P ^ N) x y) * walkUseSum P N x y u v := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg
              (mul_nonneg (hπ x).le (hπ y).le) (hden x y).le)
            calc ∑ p ∈ ((walkFinset (S := S) N).filter
                  (fun l => pathEnd x l = y)).image (cycleBypass x),
                  (∑ l ∈ flowFiber P N x y p, walkProb P x l) *
                  (if (u, v) ∈ pathEdges x p then 1 else 0)
                ≤ ∑ p ∈ ((walkFinset (S := S) N).filter
                    (fun l => pathEnd x l = y)).image (cycleBypass x),
                    ∑ l ∈ flowFiber P N x y p, walkProb P x l *
                    (if (u, v) ∈ pathEdges x l then 1 else 0) := by
                  refine Finset.sum_le_sum fun p _ => ?_
                  rw [Finset.sum_mul]
                  refine Finset.sum_le_sum fun l hl => ?_
                  simp only [flowFiber, Finset.mem_filter] at hl
                  obtain ⟨-, -, hbyp⟩ := hl
                  apply mul_le_mul_of_nonneg_left _ (walkProb_nonneg hnn x l)
                  by_cases hm : (u, v) ∈ pathEdges x p
                  · have hm' : (u, v) ∈ pathEdges x (cycleBypass x l) := by
                      rw [hbyp]; exact hm
                    have he := (cycleBypass_spec x l).2.2 (u, v) hm'
                    rw [ite_eq_left hm, ite_eq_left he]
                  · rw [ite_eq_right hm]
                    by_cases he : (u, v) ∈ pathEdges x l <;> simp [he]
              _ = walkUseSum P N x y u v := by
                  simp only [walkUseSum]
                  calc ∑ p ∈ ((walkFinset (S := S) N).filter
                        (fun l => pathEnd x l = y)).image (cycleBypass x),
                        ∑ l ∈ flowFiber P N x y p, walkProb P x l *
                        (if (u, v) ∈ pathEdges x l then 1 else 0)
                      = ∑ p ∈ ((walkFinset (S := S) N).filter
                          (fun l => pathEnd x l = y)).image (cycleBypass x),
                          ∑ l ∈ ((walkFinset (S := S) N).filter
                            (fun l => pathEnd x l = y)).filter
                            (fun l => cycleBypass x l = p), walkProb P x l *
                          (if (u, v) ∈ pathEdges x l then 1 else 0) := by
                        refine Finset.sum_congr rfl fun p _ => ?_
                        rw [flowFiber_eq_filter]
                    _ = ∑ l ∈ ((walkFinset (S := S) N).filter
                          (fun l => pathEnd x l = y)).filter
                          (fun l => cycleBypass x l ∈ ((walkFinset (S := S) N).filter
                            (fun l => pathEnd x l = y)).image (cycleBypass x)),
                          walkProb P x l *
                          (if (u, v) ∈ pathEdges x l then 1 else 0) :=
                        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
                    _ = ∑ l ∈ (walkFinset (S := S) N).filter
                          (fun l => pathEnd x l = y), walkProb P x l *
                          (if (u, v) ∈ pathEdges x l then 1 else 0) := by
                        rw [Finset.filter_true_of_mem (fun l hl =>
                          Finset.mem_image_of_mem _ hl)]
    exact hA.trans (hB.trans hC)
  have hWy : ∀ x y, (if x = y then (0 : ℝ) else
      ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
        ((pathEdges x p).count (u, v) : ℝ)) ≤ 8 * π x * walkUseSum P N x y u v := by
    intro x y
    have hW : 0 ≤ walkUseSum P N x y u v := by
      simp only [walkUseSum]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (walkProb_nonneg hnn x l)
        (by by_cases h : (u, v) ∈ pathEdges x l <;> simp [h])
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      exact mul_nonneg (mul_nonneg (by norm_num) (hπ x).le) hW
    · rw [ite_eq_right hxy]
      have h8 : π y / (P ^ N) x y ≤ 8 := by
        rw [div_le_iff₀ (hden x y)]
        have h := hlow x y
        rw [div_le_iff₀ (show (0 : ℝ) < 8 by norm_num)] at h
        linarith
      refine (hpath x y).trans ?_
      calc (π x * π y / (P ^ N) x y) * walkUseSum P N x y u v
          = π x * ((π y / (P ^ N) x y) * walkUseSum P N x y u v) := by ring
        _ ≤ π x * (8 * walkUseSum P N x y u v) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h8 hW) (hπ x).le
        _ = 8 * π x * walkUseSum P N x y u v := by ring
  have hxbound : ∀ x,
      ∑ y, (if x = y then (0 : ℝ) else
          ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
            ((pathEdges x p).count (u, v) : ℝ)) ≤
        8 * π x * ∑ k ∈ Finset.range N, (P ^ k) x u * P u v := by
    intro x
    calc ∑ y, (if x = y then (0 : ℝ) else
            ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
              ((pathEdges x p).count (u, v) : ℝ))
        ≤ ∑ y, 8 * π x * walkUseSum P N x y u v :=
          Finset.sum_le_sum fun y _ => hWy x y
      _ = 8 * π x * ∑ y, walkUseSum P N x y u v := by rw [Finset.mul_sum]
      _ ≤ 8 * π x * ∑ k ∈ Finset.range N, (P ^ k) x u * P u v :=
          mul_le_mul_of_nonneg_left (walkUseSum_le_stepSum hP)
            (mul_nonneg (by norm_num) (hπ x).le)
  have htotal : ∑ x, 8 * π x * ∑ k ∈ Finset.range N, (P ^ k) x u * P u v =
      8 * (N : ℝ) * (π u * P u v) := by
    have h1 : ∀ k : ℕ, ∑ x, π x * ((P ^ k) x u * P u v) = π u * P u v := by
      intro k
      calc ∑ x, π x * ((P ^ k) x u * P u v)
          = ∑ x, (π x * (P ^ k) x u) * P u v :=
            Finset.sum_congr rfl fun x _ => by ring
        _ = (∑ x, π x * (P ^ k) x u) * P u v := (Finset.sum_mul ..).symm
        _ = π u * P u v := by rw [sum_mul_pow_eq hP hrev k u]
    calc ∑ x, 8 * π x * ∑ k ∈ Finset.range N, (P ^ k) x u * P u v
        = ∑ x, ∑ k ∈ Finset.range N, 8 * (π x * ((P ^ k) x u * P u v)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ k ∈ Finset.range N, ∑ x, 8 * (π x * ((P ^ k) x u * P u v)) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range N, 8 * (π u * P u v) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum, h1 k]
      _ = 8 * (N : ℝ) * (π u * P u v) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hload : (mkFlow N hP hπ hden).load u v =
      ∑ x, ∑ y, (if x = y then (0 : ℝ) else
        ∑ p ∈ flowPaths π P N x y, flowWeight π P N x y p *
          ((pathEdges x p).count (u, v) : ℝ)) := rfl
  rw [hload]
  exact (Finset.sum_le_sum fun x _ => hxbound x).trans htotal.le

/-- **Rapid mixing implies a low-congestion flow** (A. Sinclair, *Combin. Probab. Comput.* 1
(1992), Theorem 8: the resistance satisfies `ρ ≤ 16 τ`). Let `P` be a stochastic matrix
satisfying detailed balance with respect to a probability vector `π > 0`, and suppose every row
of `Pᵗ` is within total variation distance `1/4` of `π` for all `t ≥ τ` (so
`τ ≥ max_x τ_x(1/4)`). Then some multicommodity flow, routing `π(x) π(y)` from `x` to `y` over
simple paths of the chain, puts at most `16 τ · π(u) P(u, v)` on every oriented edge `(u, v)`. -/
theorem exists_multicommodityFlow_load_le_sixteen_mul {S : Type*} [Fintype S]
    [DecidableEq S] {π : S → ℝ} (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hrev : IsDetailedBalance π P) {τ : ℕ}
    (hτ : ∀ x, ∀ t, τ ≤ t → tvDist (fun y => (P ^ t) x y) π ≤ 1 / 4) :
    ∃ F : MulticommodityFlow π P, ∀ u v, F.load u v ≤ 16 * τ * (π u * P u v) := by
  have hlow : ∀ x y, π y / 8 ≤ (P ^ (2 * τ)) x y := fun x y =>
    div_eight_le_pow_apply hπ hπ1 hP hrev hτ le_rfl x y
  have hden : ∀ x y, 0 < (P ^ (2 * τ)) x y := fun x y =>
    lt_of_lt_of_le (div_pos (hπ y) (by norm_num)) (hlow x y)
  refine ⟨mkFlow (2 * τ) hP hπ hden, fun u v => ?_⟩
  have hle := mkFlow_load_le hP hπ hrev hden hlow u v
  calc (mkFlow (2 * τ) hP hπ hden).load u v
      ≤ 8 * ((2 * τ : ℕ) : ℝ) * (π u * P u v) := hle
    _ = 16 * τ * (π u * P u v) := by push_cast; ring

end MathlibExt.Probability.MulticommodityFlowWanted
