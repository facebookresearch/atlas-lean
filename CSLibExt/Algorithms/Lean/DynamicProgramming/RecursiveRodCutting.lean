/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCutting

import Mathlib.Algebra.Ring.GeomSum

/-!
# Recursive rod cutting

The source-order, nonmemoized CUT-ROD algorithm from CLRS fourth edition,
Section14.1, printed366. Every invocation, including an empty rod, charges one
entry tick. Arithmetic, max, access and finite scanning are free in this
call-count model; this is not a full RAM or space bound.

Positive lengths start from the first real candidate instead of negative
infinity. This preserves the source maximum without introducing a discard
option. Signed and fractional prices are a documented ordered-additive
generalization of nonnegative sales, as in the canonical rod-cutting module.
Codex authorship was explicitly selected by Adam Kiezun.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RodCutting

universe u

@[no_expose] private def scanFirstCuts {α : Type u} [LinearOrder α] {j : Nat}
    (candidate : Fin j → TimeM Nat α) : (count : Nat) → count < j → TimeM Nat α
  | 0, hcount => candidate ⟨0, hcount⟩
  | count + 1, hcount => do
      let best ← scanFirstCuts candidate count (by omega)
      let next ← candidate ⟨count + 1, hcount⟩
      pure (max best next)

private lemma scanFirstCuts_spec {α : Type u} [LinearOrder α] {j : Nat}
    (candidate : Fin j → TimeM Nat α) (count : Nat) (hcount : count < j) :
    (∃ i : Fin j, i.val ≤ count ∧
      (candidate i).ret = (scanFirstCuts candidate count hcount).ret) ∧
    ∀ i : Fin j, i.val ≤ count →
      (candidate i).ret ≤ (scanFirstCuts candidate count hcount).ret := by
  induction count with
  | zero =>
      refine ⟨⟨⟨0, hcount⟩, le_rfl, rfl⟩, ?_⟩
      intro i hi
      have heq : i = ⟨0, hcount⟩ := Fin.ext (show i.val = 0 by omega)
      simp [heq, scanFirstCuts]
  | succ count ih =>
      obtain ⟨⟨i, hi, heq⟩, hupper⟩ := ih (by omega)
      simp only [scanFirstCuts, TimeM.ret_bind, TimeM.ret_pure]
      constructor
      · by_cases h : (candidate ⟨count + 1, hcount⟩).ret ≤
            (scanFirstCuts candidate count (by omega)).ret
        · exact ⟨i, by omega, heq.trans (max_eq_left h).symm⟩
        · exact ⟨⟨count + 1, hcount⟩, le_rfl,
            (max_eq_right (le_of_not_ge h)).symm⟩
      · intro i hi
        by_cases h : i.val ≤ count
        · exact (hupper i h).trans (le_max_left _ _)
        · have heq : i = ⟨count + 1, hcount⟩ :=
            Fin.ext (show i.val = count + 1 by omega)
          simpa only [heq] using
            le_max_right (scanFirstCuts candidate count (by omega)).ret
              (candidate ⟨count + 1, hcount⟩).ret

private lemma scanFirstCuts_time {α : Type u} [LinearOrder α] {j : Nat}
    (candidate : Fin j → TimeM Nat α) (cost : Nat → Nat)
    (hcost : ∀ i : Fin j, (candidate i).time = cost i.val)
    (count : Nat) (hcount : count < j) :
    (scanFirstCuts candidate count hcount).time =
      ∑ i ∈ Finset.range (count + 1), cost i := by
  induction count with
  | zero => simp [scanFirstCuts, hcost]
  | succ count ih =>
      simp [scanFirstCuts, ih (by omega), hcost, Finset.sum_range_succ]

@[no_expose] private def recursiveCutRodAux {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n) :
    TimeM Nat α := do
  TimeM.tick 1
  match h : j with
  | 0 => pure 0
  | j + 1 =>
      scanFirstCuts (fun i : Fin (j + 1) => do
        let suffix ← recursiveCutRodAux prices (j + 1 - (i.val + 1)) (by omega)
        pure (prices[i.val]'(by omega) + suffix)) j (by omega)
termination_by j
decreasing_by omega

/-- Evaluate every first cut in increasing order, freshly recomputing every suffix.
One cost tick is charged at every invocation, including the root and empty suffixes. -/
public def recursiveCutRod {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) : TimeM Nat α :=
  recursiveCutRodAux prices n le_rfl

private lemma compositionRevenue_cast {α : Type u} [AddCommMonoid α]
    {n k l : Nat} (prices : Vector α n) (parts : Composition k) (hkl : k = l)
    (hl : l ≤ n) :
    compositionRevenue prices (parts.cast hkl) hl =
      compositionRevenue prices parts (by omega) := by
  subst l
  rfl

private lemma compositionRevenue_le_best {α : Type u} [AddCommMonoid α]
    [LinearOrder α] [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n)
    (j : Nat) (hjn : j ≤ n) (hpos : 0 < j) (best : α)
    (hoptimal : ∀ (k : Nat) (hk : k ≤ n), k < j →
      IsGreatest (Set.range fun parts : Composition k => compositionRevenue prices parts hk)
        (recursiveCutRodAux prices k hk).ret)
    (hupper : ∀ i : Fin j, prices[i.val]'(by omega) +
      (recursiveCutRodAux prices (j - (i.val + 1)) (by omega)).ret ≤ best)
    (parts : Composition j) : compositionRevenue prices parts hjn ≤ best := by
  induction parts using Composition.recOnSingleAppend with
  | zero => omega
  | single_append k m parts _ih =>
      have hsuffix := (hoptimal m (by omega) (by omega)).2 (Set.mem_range_self parts)
      have hcut := hupper ⟨k, by omega⟩
      rw [compositionRevenue_append, compositionRevenue_single]
      refine (add_le_add_right hsuffix _).trans ?_
      simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hcut

private lemma recursiveCutRodAux_correct {α : Type u} [AddCommMonoid α]
    [LinearOrder α] [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n)
    (j : Nat) (hjn : j ≤ n) :
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hjn)
      (recursiveCutRodAux prices j hjn).ret := by
  revert hjn
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjn
      cases j with
      | zero =>
          simp only [recursiveCutRodAux, TimeM.ret_bind]
          constructor
          · exact ⟨Composition.ones 0, compositionRevenue_zero prices _⟩
          · rintro revenue ⟨parts, rfl⟩
            simp
      | succ j =>
          let candidate : Fin (j + 1) → TimeM Nat α := fun i => do
            let suffix ← recursiveCutRodAux prices (j + 1 - (i.val + 1)) (by omega)
            pure (prices[i.val]'(by omega) + suffix)
          obtain ⟨⟨i, _, hbest⟩, hupper⟩ := scanFirstCuts_spec candidate j (by omega)
          simp only [recursiveCutRodAux, TimeM.ret_bind]
          change IsGreatest _ (scanFirstCuts candidate j (by omega)).ret
          constructor
          · obtain ⟨parts, hparts⟩ := (ih (j + 1 - (i.val + 1)) (by omega) (by omega)).1
            refine ⟨((Composition.single (i.val + 1) (by omega)).append parts).cast
              (by omega), ?_⟩
            dsimp only at hparts ⊢
            rw [compositionRevenue_cast, compositionRevenue_append,
              compositionRevenue_single, hparts]
            simpa only [candidate, TimeM.ret_bind, TimeM.ret_pure,
              Nat.add_sub_cancel] using hbest
          · rintro revenue ⟨parts, rfl⟩
            refine compositionRevenue_le_best prices (j + 1) hjn (by omega) _
              (fun k hk hlt => ih k hlt hk) ?_ parts
            intro i
            simpa only [candidate, TimeM.ret_bind, TimeM.ret_pure] using
              hupper i (by omega)

private lemma recursiveCutRodAux_time {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n) :
    (recursiveCutRodAux prices j hjn).time = 2 ^ j := by
  revert hjn
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hjn
      cases j with
      | zero => simp [recursiveCutRodAux]
      | succ j =>
          let candidate : Fin (j + 1) → TimeM Nat α := fun i => do
            let suffix ← recursiveCutRodAux prices (j + 1 - (i.val + 1)) (by omega)
            pure (prices[i.val]'(by omega) + suffix)
          have hcost : ∀ i : Fin (j + 1), (candidate i).time = 2 ^ (j - i.val) := by
            intro i
            have heq : j + 1 - (i.val + 1) = j - i.val := by omega
            simp only [candidate, TimeM.time_bind, TimeM.time_pure, add_zero]
            rw [ih (j + 1 - (i.val + 1)) (by omega) (by omega), heq]
          have hscan := scanFirstCuts_time candidate (fun i => 2 ^ (j - i)) hcost j
            (by omega)
          have hreflect : (∑ i ∈ Finset.range (j + 1), 2 ^ (j - i)) =
              ∑ i ∈ Finset.range (j + 1), 2 ^ i := by
            simpa only [Nat.add_sub_cancel] using
              Finset.sum_range_reflect (fun i => 2 ^ i) (j + 1)
          calc
            (recursiveCutRodAux prices (j + 1) hjn).time =
                1 + (scanFirstCuts candidate j (by omega)).time := by
                  simp [recursiveCutRodAux, candidate]
            _ = 1 + ∑ i ∈ Finset.range (j + 1), 2 ^ (j - i) := by rw [hscan]
            _ = 1 + ∑ i ∈ Finset.range (j + 1), 2 ^ i := by rw [hreflect]
            _ = 2 ^ (j + 1) := by
              simpa only [one_add_one_eq_two, mul_one, Nat.add_comm] using
                geom_sum_mul_add (1 : Nat) (j + 1)

/-- Recursive CUT-ROD returns an attaining maximum over canonical whole-length
compositions. Negative prices do not create a discard option. -/
public theorem recursiveCutRod_correct {α : Type u} [AddCommMonoid α]
    [LinearOrder α] [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n =>
      compositionRevenue prices parts le_rfl) (recursiveCutRod prices).ret :=
  recursiveCutRodAux_correct prices n le_rfl

/-- The actual nonmemoized execution enters exactly `2 ^ n` invocations,
including the root and every empty suffix. -/
public theorem recursiveCutRod_time {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (recursiveCutRod prices).time = 2 ^ n :=
  recursiveCutRodAux_time prices n le_rfl

end Cslib.Algorithms.Lean.RodCutting
