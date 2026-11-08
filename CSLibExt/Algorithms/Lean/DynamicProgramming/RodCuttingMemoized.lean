/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCutting

import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Memoized rod cutting

CLRS fourth edition, section14.1, pages368–370, uses a top-down saved revenue cache.
The source's nonnegative known-revenue guard is generalized to `Option.some` so signed
and fractional optimum revenues are cached too. Every positive piece is sold.

One event is charged per AUX entry/cache probe, actual first-cut candidate, and cache write.
Allocation, initialization, arithmetic, comparisons, vector operations and control are free.
These events do not represent full RAM, bit or space costs.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RodCutting

universe u

open scoped BigOperators

@[no_expose] private def scanCandidates {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (solve : (k : Nat) → k < j → Vector (Option α) (n + 1) →
      TimeM Nat (α × Vector (Option α) (n + 1))) :
    (count : Nat) → count < j → Vector (Option α) (n + 1) →
      TimeM Nat (α × Vector (Option α) (n + 1))
  | 0, hcount, cache => do
      let child ← solve (j - 1) (by omega) cache
      TimeM.tick 1
      pure (prices[0]'(by omega) + child.1, child.2)
  | count + 1, hcount, cache => do
      let previous ← scanCandidates prices j hjn solve count (by omega) cache
      let child ← solve (j - (count + 2)) (by omega) previous.2
      TimeM.tick 1
      pure (max previous.1 (prices[count + 1]'(by omega) + child.1), child.2)

@[no_expose] private def memoizedAuxWorker {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) :
    TimeM Nat (α × Vector (Option α) (n + 1)) := do
  TimeM.tick 1
  match cache[j]'(by omega) with
  | some value => pure (value, cache)
  | none =>
      match hlength : j with
      | 0 => do
          TimeM.tick 1
          pure (0, cache.set 0 (some 0) (by omega))
      | k + 1 => do
          let best ← scanCandidates prices (k + 1) (by omega)
            (fun l hlt saved => memoizedAuxWorker prices l (by omega) saved)
            k (by omega) cache
          TimeM.tick 1
          pure (best.1, best.2.set (k + 1) (some best.1) (by omega))
termination_by j
decreasing_by omega

/-- Solve the requested length top-down, carrying every recursive cache update.
Known entries are returned immediately, including signed values and length zero. -/
public def memoizedCutRodAux {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) :
    TimeM Nat (α × Vector (Option α) (n + 1)) :=
  memoizedAuxWorker prices j hjn cache

/-- Initialize an unknown cache and invoke the memoized auxiliary on the whole rod. -/
public def memoizedCutRod {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) : TimeM Nat α := do
  let result ← memoizedCutRodAux prices n le_rfl (Vector.replicate (n + 1) none)
  pure result.1


private lemma aux_eq_def {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) :
    memoizedCutRodAux prices j hjn cache = (do
  TimeM.tick 1
  match cache[j]'(by omega) with
  | some value => pure (value, cache)
  | none =>
      match hlength : j with
      | 0 => do
          TimeM.tick 1
          pure (0, cache.set 0 (some 0) (by omega))
      | k + 1 => do
          let best ← scanCandidates prices (k + 1) (by omega)
            (fun l hlt saved => memoizedCutRodAux prices l (by omega) saved)
            k (by omega) cache
          TimeM.tick 1
          pure (best.1, best.2.set (k + 1) (some best.1) (by omega))) := by
  rw [memoizedCutRodAux, memoizedAuxWorker.eq_def]
  rfl

/-- A known cache entry returns immediately without touching any saved cell. -/
public theorem memoizedCutRodAux_hit {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) (value : α)
    (hcache : cache[j]'(by omega) = some value) :
    memoizedCutRodAux prices j hjn cache = ⟨(value, cache), 1⟩ := by
  rw [aux_eq_def]
  apply TimeM.ext <;> simp [hcache, TimeM.tick]

private lemma aux_zero_miss {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (cache : Vector (Option α) (n + 1))
    (hcache : cache[0]'(by omega) = none) :
    memoizedCutRodAux prices 0 (Nat.zero_le n) cache =
      ⟨(0, cache.set 0 (some 0) (by omega)), 2⟩ := by
  rw [aux_eq_def]
  apply TimeM.ext <;> simp [hcache, TimeM.tick]


private lemma scan_transport {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (solve : (k : Nat) → k < j → Vector (Option α) (n + 1) →
      TimeM Nat (α × Vector (Option α) (n + 1)))
    (P : Vector (Option α) (n + 1) → Prop)
    (hsolve : ∀ (k : Nat) (hk : k < j) (saved : Vector (Option α) (n + 1)),
      P saved → P (solve k hk saved).ret.2)
    (count : Nat) (hcount : count < j) (cache : Vector (Option α) (n + 1))
    (hcache : P cache) : P (scanCandidates prices j hjn solve count hcount cache).ret.2 := by
  induction count generalizing cache with
  | zero =>
      simp only [scanCandidates, TimeM.ret_bind, TimeM.ret_pure]
      exact hsolve (j - 1) (by omega) cache hcache
  | succ count ih =>
      simp only [scanCandidates, TimeM.ret_bind, TimeM.ret_pure]
      exact hsolve (j - (count + 2)) (by omega)
        (scanCandidates prices j hjn solve count (by omega) cache).ret.2
        (ih (by omega) cache hcache)


private lemma aux_protected {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) (k : Nat) (hkn : k ≤ n)
    (hprotect : (∃ value : α, cache[k]'(by omega) = some value) ∨ j < k) :
    (memoizedCutRodAux prices j hjn cache).ret.2[k]'(by omega) = cache[k] := by
  revert hjn cache k hkn hprotect
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjn cache k hkn hprotect
      cases htarget : cache[j]'(by omega) with
      | some value =>
          rw [memoizedCutRodAux_hit prices j hjn cache value htarget]
      | none =>
          have hne : j ≠ k := by
            intro heq
            subst k
            rcases hprotect with ⟨value, hvalue⟩ | hlt
            · simp [htarget] at hvalue
            · omega
          cases j with
          | zero =>
              rw [aux_zero_miss prices cache htarget]
              exact Vector.getElem_set_ne (i := 0) (j := k) (by omega) (by omega) hne
          | succ j =>
              let solve := fun (l : Nat) (hl : l < j + 1)
                (saved : Vector (Option α) (n + 1)) =>
                  memoizedCutRodAux prices l (by omega) saved
              have hscan := scan_transport prices (j + 1) hjn solve
                (fun saved => saved[k]'(by omega) = cache[k])
                (fun l hl saved hsaved => (ih l hl (by omega) saved k hkn (by
                  rcases hprotect with ⟨value, hvalue⟩ | hlt
                  · exact Or.inl ⟨value, hsaved.trans hvalue⟩
                  · exact Or.inr (by omega))).trans hsaved)
                j (by omega) cache rfl
              rw [aux_eq_def]
              simp only [htarget, TimeM.ret_bind, TimeM.ret_pure]
              rw [Vector.getElem_set_ne (i := j + 1) (j := k) (by omega) (by omega) hne]
              exact hscan


/-- Known entries and every cell above the requested length are preserved. -/
public theorem memoizedCutRodAux_preserves {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) :
    (∀ (k : Nat) (hkn : k ≤ n) (value : α), cache[k]'(by omega) = some value →
      (memoizedCutRodAux prices j hjn cache).ret.2[k]'(by omega) = some value) ∧
    ∀ (k : Nat) (hkn : k ≤ n), j < k →
      (memoizedCutRodAux prices j hjn cache).ret.2[k]'(by omega) = cache[k] := by
  constructor
  · intro k hkn value hvalue
    exact (aux_protected prices j hjn cache k hkn (Or.inl ⟨value, hvalue⟩)).trans hvalue
  · intro k hkn hlt
    exact aux_protected prices j hjn cache k hkn (Or.inr hlt)

private lemma aux_saved {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) :
    (memoizedCutRodAux prices j hjn cache).ret.2[j]'(by omega) =
      some (memoizedCutRodAux prices j hjn cache).ret.1 := by
  cases htarget : cache[j]'(by omega) with
  | some value => rw [memoizedCutRodAux_hit prices j hjn cache value htarget]; exact htarget
  | none =>
      cases j with
      | zero =>
          rw [aux_zero_miss prices cache htarget]
          exact Vector.getElem_set_self (by omega)
      | succ j =>
          rw [aux_eq_def]
          simp only [htarget, TimeM.ret_bind, TimeM.ret_pure, Vector.getElem_set_self]

/-- The empty uncached rod earns zero with one probe and one actual cache write. -/
public theorem memoizedCutRod_zero {α : Type u} [AddCommMonoid α] [LinearOrder α]
    (prices : Vector α 0) : memoizedCutRod prices = ⟨0, 2⟩ := by
  rw [memoizedCutRod]
  rw [aux_zero_miss prices (Vector.replicate 1 none) (by simp)]
  apply TimeM.ext <;> simp


private lemma scan_optimal {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (solve : (k : Nat) → k < j → Vector (Option α) (n + 1) →
      TimeM Nat (α × Vector (Option α) (n + 1)))
    (P : Vector (Option α) (n + 1) → Prop)
    (hsolve : ∀ (k : Nat) (hk : k < j) (saved : Vector (Option α) (n + 1)),
      P saved → P (solve k hk saved).ret.2 ∧
        IsGreatest (Set.range fun parts : Composition k =>
          compositionRevenue prices parts (by omega)) (solve k hk saved).ret.1)
    (count : Nat) (hcount : count < j) (cache : Vector (Option α) (n + 1))
    (hcache : P cache) :
    P (scanCandidates prices j hjn solve count hcount cache).ret.2 ∧
    (∃ i : Fin j, i.val ≤ count ∧ ∃ parts : Composition (j - (i.val + 1)),
      prices[i.val]'(by omega) + compositionRevenue prices parts (by omega) =
        (scanCandidates prices j hjn solve count hcount cache).ret.1) ∧
    ∀ (i : Fin j), i.val ≤ count → ∀ parts : Composition (j - (i.val + 1)),
      prices[i.val]'(by omega) + compositionRevenue prices parts (by omega) ≤
        (scanCandidates prices j hjn solve count hcount cache).ret.1 := by
  induction count generalizing cache with
  | zero =>
      obtain ⟨hvalid, hattain, hupper⟩ := hsolve (j - 1) (by omega) cache hcache
      simp only [scanCandidates, TimeM.ret_bind, TimeM.ret_pure]
      refine ⟨hvalid, ?_, ?_⟩
      · obtain ⟨parts, hparts⟩ := hattain
        exact ⟨⟨0, hcount⟩, le_rfl, parts, congrArg (prices[0]'(by omega) + ·) hparts⟩
      · intro i hi parts
        have hi0 : i.val = 0 := by omega
        have hiEq : i = ⟨0, hcount⟩ := Fin.ext hi0
        subst i
        exact add_le_add le_rfl (hupper (Set.mem_range_self parts))
  | succ count ih =>
      obtain ⟨hvalid, ⟨i, hi, parts, hparts⟩, hupper⟩ := ih (by omega) cache hcache
      obtain ⟨hchild, ⟨newParts, hnew⟩, hnewUpper⟩ := hsolve (j - (count + 2))
        (by omega) (scanCandidates prices j hjn solve count (by omega) cache).ret.2 hvalid
      simp only [scanCandidates, TimeM.ret_bind, TimeM.ret_pure]
      refine ⟨hchild, ?_, ?_⟩
      · by_cases hbetter :
            (scanCandidates prices j hjn solve count (by omega) cache).ret.1 ≥
              prices[count + 1]'(by omega) +
                (solve (j - (count + 2)) (by omega)
                  (scanCandidates prices j hjn solve count (by omega) cache).ret.2).ret.1
        · exact ⟨i, by omega, parts, hparts.trans (max_eq_left hbetter).symm⟩
        · refine ⟨⟨count + 1, hcount⟩, le_rfl, newParts, ?_⟩
          simpa only [Nat.add_assoc, Nat.reduceAdd] using
            (congrArg (prices[count + 1]'(by omega) + ·) hnew).trans
              (max_eq_right (le_of_not_ge hbetter)).symm
      · intro i hi parts
        by_cases hold : i.val ≤ count
        · exact (hupper i hold parts).trans (le_max_left _ _)
        · have hi1 : i.val = count + 1 := by omega
          have hiEq : i = ⟨count + 1, hcount⟩ := Fin.ext hi1
          subst i
          exact (add_le_add le_rfl (hnewUpper (Set.mem_range_self parts))).trans
            (le_max_right _ _)


private lemma revenue_cast {α : Type u} [AddCommMonoid α] {n k l : Nat}
    (prices : Vector α n) (parts : Composition k) (hkl : k = l) (hl : l ≤ n) :
    compositionRevenue prices (parts.cast hkl) hl =
      compositionRevenue prices parts (by omega) := by
  subst l
  rfl

private lemma firstCuts_optimal {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (j : Nat)
    (hjn : j ≤ n) (hpos : 0 < j) (best : α)
    (hattain : ∃ i : Fin j, ∃ parts : Composition (j - (i.val + 1)),
      prices[i.val]'(by omega) + compositionRevenue prices parts (by omega) = best)
    (hupper : ∀ (i : Fin j) (parts : Composition (j - (i.val + 1))),
      prices[i.val]'(by omega) + compositionRevenue prices parts (by omega) ≤ best) :
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hjn)
      best := by
  constructor
  · obtain ⟨i, parts, hparts⟩ := hattain
    refine ⟨((Composition.single (i.val + 1) (by omega)).append parts).cast (by omega), ?_⟩
    dsimp only
    rw [revenue_cast, compositionRevenue_append, compositionRevenue_single]
    simpa only [Nat.add_sub_cancel] using hparts
  · rintro value ⟨parts, rfl⟩
    induction parts using Composition.recOnSingleAppend with
    | zero => omega
    | single_append k m tail _ih =>
        dsimp only
        rw [compositionRevenue_append, compositionRevenue_single]
        have hcut := hupper ⟨k, by omega⟩ (tail.cast (by dsimp; omega))
        dsimp only at hcut
        rw [revenue_cast] at hcut
        simpa only [Nat.add_sub_cancel] using hcut


@[no_expose] private def CacheValid {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (cache : Vector (Option α) (n + 1)) : Prop :=
  ∀ (k : Nat) (hk : k ≤ n) (value : α), cache[k]'(by omega) = some value →
    IsGreatest (Set.range fun parts : Composition k => compositionRevenue prices parts hk) value

private lemma cacheValid_set {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (cache : Vector (Option α) (n + 1))
    (j : Nat) (hjn : j ≤ n) (value : α) (hvalid : CacheValid prices cache)
    (hvalue : IsGreatest
      (Set.range fun parts : Composition j => compositionRevenue prices parts hjn) value) :
    CacheValid prices (cache.set j (some value) (by omega)) := by
  intro k hk v hv
  by_cases hkj : k = j
  · subst k
    rw [Vector.getElem_set_self] at hv
    cases Option.some.inj hv
    exact hvalue
  · rw [Vector.getElem_set_ne (i := j) (j := k) (by omega) (by omega) (Ne.symm hkj)] at hv
    exact hvalid k hk v hv

private lemma aux_valid {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) (hvalid : CacheValid prices cache) :
    CacheValid prices (memoizedCutRodAux prices j hjn cache).ret.2 ∧
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hjn)
      (memoizedCutRodAux prices j hjn cache).ret.1 := by
  revert hjn cache hvalid
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjn cache hvalid
      cases htarget : cache[j]'(by omega) with
      | some value =>
          rw [memoizedCutRodAux_hit prices j hjn cache value htarget]
          exact ⟨hvalid, hvalid j hjn value htarget⟩
      | none =>
          cases j with
          | zero =>
              have hzero : IsGreatest
                  (Set.range fun parts : Composition 0 =>
                    compositionRevenue prices parts (Nat.zero_le n)) (0 : α) := by
                constructor
                · exact ⟨Composition.ones 0, compositionRevenue_zero prices _⟩
                · rintro value ⟨parts, rfl⟩
                  simp
              rw [aux_zero_miss prices cache htarget]
              exact ⟨cacheValid_set prices cache 0 hjn 0 hvalid hzero, hzero⟩
          | succ j =>
              let solve := fun (l : Nat) (hl : l < j + 1)
                (saved : Vector (Option α) (n + 1)) =>
                  memoizedCutRodAux prices l (by omega) saved
              obtain ⟨hscanValid, ⟨i, _, parts, hparts⟩, hupper⟩ :=
                scan_optimal prices (j + 1) hjn solve (CacheValid prices)
                  (fun l hl saved hsaved => ih l hl (by omega) saved hsaved)
                  j (by omega) cache hvalid
              have hrow : IsGreatest
                  (Set.range fun parts : Composition (j + 1) =>
                    compositionRevenue prices parts hjn)
                  (scanCandidates prices (j + 1) hjn solve j (by omega) cache).ret.1 :=
                firstCuts_optimal prices (j + 1) hjn (by omega) _ ⟨i, parts, hparts⟩
                  (fun cut tail => hupper cut (by omega) tail)
              rw [aux_eq_def]
              simp only [htarget, TimeM.ret_bind, TimeM.ret_pure]
              exact ⟨cacheValid_set prices _ (j + 1) hjn _ hscanValid hrow, hrow⟩


/-- A valid supplied cache yields an attained optimum and remains valid after the call. -/
public theorem memoizedCutRodAux_correct {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1))
    (hvalid : ∀ (k : Nat) (hk : k ≤ n) (value : α), cache[k]'(by omega) = some value →
      IsGreatest (Set.range fun parts : Composition k => compositionRevenue prices parts hk)
        value) :
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hjn)
      (memoizedCutRodAux prices j hjn cache).ret.1 ∧
    (∀ (k : Nat) (hk : k ≤ n) (value : α),
      (memoizedCutRodAux prices j hjn cache).ret.2[k]'(by omega) = some value →
        IsGreatest (Set.range fun parts : Composition k => compositionRevenue prices parts hk)
          value) ∧
    (memoizedCutRodAux prices j hjn cache).ret.2[j]'(by omega) =
      some (memoizedCutRodAux prices j hjn cache).ret.1 := by
  obtain ⟨hcache, hvalue⟩ := aux_valid prices j hjn cache hvalid
  exact ⟨hvalue, hcache, aux_saved prices j hjn cache⟩

/-- The top-down memoized result attains and dominates every whole-rod composition revenue. -/
public theorem memoizedCutRod_correct {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n => compositionRevenue prices parts le_rfl)
      (memoizedCutRod prices).ret := by
  have hvalid : CacheValid prices (Vector.replicate (n + 1) none) := by
    intro k hk value hvalue
    simp at hvalue
  simpa only [memoizedCutRod, TimeM.ret_bind, TimeM.ret_pure] using
    (aux_valid prices n le_rfl (Vector.replicate (n + 1) none) hvalid).2

@[no_expose] private def pendingPotential {α : Type u} {n : Nat}
    (cache : Vector (Option α) (n + 1)) : Nat :=
  ∑ k : Fin (n + 1), match cache[k.val] with
    | none => 2 * k.val + 1
    | some _ => 0

private lemma potential_set {α : Type u} {n : Nat}
    (cache : Vector (Option α) (n + 1)) (j : Nat) (hjn : j ≤ n) (value : α)
    (hj : cache[j]'(by omega) = none) :
    pendingPotential (cache.set j (some value) (by omega)) + (2 * j + 1) =
      pendingPotential cache := by
  let index : Fin (n + 1) := ⟨j, by omega⟩
  let before := fun k : Fin (n + 1) => match cache[k.val] with
    | none => 2 * k.val + 1
    | some _ => 0
  let after := fun k : Fin (n + 1) => match (cache.set j (some value) (by omega))[k.val] with
    | none => 2 * k.val + 1
    | some _ => 0
  have hbefore : before index = 2 * j + 1 := by simp [before, index, hj]
  have hafter : after index = 0 := by simp [after, index]
  have herase : ∑ k ∈ Finset.univ.erase index, after k =
      ∑ k ∈ Finset.univ.erase index, before k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hne : j ≠ k.val := by
      intro h
      exact (Finset.mem_erase.mp hk).1 (Fin.ext h.symm)
    simp only [after, before, Vector.getElem_set_ne (by omega) k.isLt hne]
  have hb := Finset.sum_erase_add Finset.univ before (Finset.mem_univ index)
  have ha := Finset.sum_erase_add Finset.univ after (Finset.mem_univ index)
  change (∑ k, after k) + (2 * j + 1) = ∑ k, before k
  rw [hbefore] at hb
  rw [hafter] at ha
  omega

private lemma scan_potential {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (solve : (k : Nat) → k < j → Vector (Option α) (n + 1) →
      TimeM Nat (α × Vector (Option α) (n + 1)))
    (hsolve : ∀ (k : Nat) (hk : k < j) (saved : Vector (Option α) (n + 1)),
      (solve k hk saved).time + pendingPotential (solve k hk saved).ret.2 =
        1 + pendingPotential saved)
    (count : Nat) (hcount : count < j) (cache : Vector (Option α) (n + 1)) :
    (scanCandidates prices j hjn solve count hcount cache).time +
        pendingPotential (scanCandidates prices j hjn solve count hcount cache).ret.2 =
      2 * (count + 1) + pendingPotential cache := by
  induction count generalizing cache with
  | zero =>
      have hchild := hsolve (j - 1) (by omega) cache
      simp only [scanCandidates, TimeM.time_bind, TimeM.time_pure,
        TimeM.ret_bind, TimeM.ret_pure, TimeM.tick] at ⊢
      omega
  | succ count ih =>
      have hprevious := ih (by omega) cache
      have hchild := hsolve (j - (count + 2)) (by omega)
        (scanCandidates prices j hjn solve count (by omega) cache).ret.2
      simp only [scanCandidates, TimeM.time_bind, TimeM.time_pure,
        TimeM.ret_bind, TimeM.ret_pure, TimeM.tick] at ⊢
      omega

private lemma aux_potential {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (cache : Vector (Option α) (n + 1)) :
    (memoizedCutRodAux prices j hjn cache).time +
        pendingPotential (memoizedCutRodAux prices j hjn cache).ret.2 =
      1 + pendingPotential cache := by
  revert hjn cache
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjn cache
      cases htarget : cache[j]'(by omega) with
      | some value =>
          rw [memoizedCutRodAux_hit prices j hjn cache value htarget]
      | none =>
          cases j with
          | zero =>
              have hwrite := potential_set cache 0 hjn (0 : α) htarget
              rw [aux_zero_miss prices cache htarget]
              dsimp only
              omega
          | succ j =>
              let solve := fun (l : Nat) (hl : l < j + 1)
                (saved : Vector (Option α) (n + 1)) =>
                  memoizedCutRodAux prices l (by omega) saved
              have hscan := scan_potential prices (j + 1) hjn solve
                (fun l hl saved => ih l hl (by omega) saved) j (by omega) cache
              have hnone := scan_transport prices (j + 1) hjn solve
                (fun saved => saved[j + 1]'(by omega) = none)
                (fun l hl saved hsaved =>
                  ((memoizedCutRodAux_preserves prices l (by omega) saved).2
                    (j + 1) hjn hl).trans hsaved)
                j (by omega) cache htarget
              have hwrite := potential_set
                (scanCandidates prices (j + 1) hjn solve j (by omega) cache).ret.2
                (j + 1) hjn
                (scanCandidates prices (j + 1) hjn solve j (by omega) cache).ret.1 hnone
              rw [aux_eq_def]
              simp only [htarget, TimeM.time_bind, TimeM.time_pure,
                TimeM.ret_bind, TimeM.ret_pure, TimeM.tick]
              change 1 + ((scanCandidates prices (j + 1) hjn solve j (by omega) cache).time +
                (1 + 0)) + pendingPotential
                  ((scanCandidates prices (j + 1) hjn solve j (by omega) cache).ret.2.set
                    (j + 1)
                    (some (scanCandidates prices (j + 1) hjn solve j (by omega) cache).ret.1)
                    (by omega)) = 1 + pendingPotential cache
              omega

private lemma scan_first_transport {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n)
    (solve : (k : Nat) → k < j → Vector (Option α) (n + 1) →
      TimeM Nat (α × Vector (Option α) (n + 1)))
    (P : Vector (Option α) (n + 1) → Prop)
    (hsolve : ∀ (k : Nat) (hk : k < j) (saved : Vector (Option α) (n + 1)),
      P saved → P (solve k hk saved).ret.2)
    (count : Nat) (hcount : count < j) (cache : Vector (Option α) (n + 1))
    (hfirst : P (solve (j - 1) (by omega) cache).ret.2) :
    P (scanCandidates prices j hjn solve count hcount cache).ret.2 := by
  induction count generalizing cache with
  | zero =>
      simp only [scanCandidates, TimeM.ret_bind, TimeM.ret_pure]
      exact hfirst
  | succ count ih =>
      simp only [scanCandidates, TimeM.ret_bind, TimeM.ret_pure]
      exact hsolve (j - (count + 2)) (by omega)
        (scanCandidates prices j hjn solve count (by omega) cache).ret.2
        (ih (by omega) cache hfirst)

private lemma aux_prefix {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n) :
    ∀ (k : Nat) (hk : k ≤ j), ∃ value : α,
      (memoizedCutRodAux prices j hjn (Vector.replicate (n + 1) none)).ret.2[k]'(by omega) =
        some value := by
  revert hjn
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjn k hk
      by_cases hkj : k = j
      · subst k
        exact ⟨_, aux_saved prices j hjn (Vector.replicate (n + 1) none)⟩
      · cases j with
        | zero => omega
        | succ j =>
            let solve := fun (l : Nat) (hl : l < j + 1)
              (saved : Vector (Option α) (n + 1)) =>
                memoizedCutRodAux prices l (by omega) saved
            have hfirst := ih j (by omega) (by omega) k (by omega)
            have hscan := scan_first_transport prices (j + 1) hjn solve
              (fun saved => ∃ value : α, saved[k]'(by omega) = some value)
              (fun l hl saved hsaved => by
                obtain ⟨value, hvalue⟩ := hsaved
                exact ⟨value, (memoizedCutRodAux_preserves prices l (by omega) saved).1
                  k (by omega) value hvalue⟩)
              j (by omega) (Vector.replicate (n + 1) none) (by
                simpa only [solve, Nat.add_sub_cancel] using hfirst)
            rw [aux_eq_def]
            simp only [Vector.getElem_replicate, TimeM.ret_bind, TimeM.ret_pure]
            rw [Vector.getElem_set_ne (i := j + 1) (j := k) (by omega) (by omega)
              (Ne.symm hkj)]
            exact hscan

private lemma potential_empty {α : Type u} (n : Nat) :
    pendingPotential (Vector.replicate (n + 1) (none : Option α)) = (n + 1) ^ 2 := by
  have hsum : ∀ m : Nat, (∑ k : Fin (m + 1), (2 * k.val + 1)) = (m + 1) ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
        simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
  simpa only [pendingPotential, Vector.getElem_replicate] using hsum n

private lemma potential_full {α : Type u} {n : Nat}
    (cache : Vector (Option α) (n + 1))
    (hfull : ∀ (k : Nat) (hk : k ≤ n), ∃ value : α, cache[k]'(by omega) = some value) :
    pendingPotential cache = 0 := by
  apply Finset.sum_eq_zero
  intro k _hk
  obtain ⟨value, hvalue⟩ := hfull k.val (by omega)
  simp only [hvalue]

/-- An initially unknown cache is filled through the requested length with exact optima. -/
public theorem memoizedCutRodAux_complete {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n) :
    ∀ (k : Nat) (hk : k ≤ j), ∃ value : α,
      (memoizedCutRodAux prices j hjn (Vector.replicate (n + 1) none)).ret.2[k]'(by omega) =
        some value ∧
      IsGreatest (Set.range fun parts : Composition k =>
        compositionRevenue prices parts (by omega)) value := by
  intro k hk
  obtain ⟨value, hvalue⟩ := aux_prefix prices j hjn k hk
  refine ⟨value, hvalue, ?_⟩
  exact (aux_valid prices j hjn (Vector.replicate (n + 1) none) (by
    intro l hl v hv
    simp at hv)).1 k (by omega) value hvalue

/-- Exact same-execution event count: one per cache probe, candidate, and actual write. -/
public theorem memoizedCutRod_time {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    (memoizedCutRod prices).time = n ^ 2 + 2 * n + 2 := by
  have hcost := aux_potential prices n le_rfl (Vector.replicate (n + 1) none)
  have hfull := potential_full
    (memoizedCutRodAux prices n le_rfl (Vector.replicate (n + 1) none)).ret.2
    (aux_prefix prices n le_rfl)
  rw [hfull, potential_empty] at hcost
  simp only [memoizedCutRod, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  have hpoly : (n + 1) ^ 2 + 1 = n ^ 2 + 2 * n + 2 := by
    simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  omega

end Cslib.Algorithms.Lean.RodCutting
