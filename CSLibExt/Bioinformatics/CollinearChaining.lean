/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Chain
import Mathlib.Tactic.Ring

/-!
# Weighted collinear chaining

Given previously matched anchor pairs, compute the score of an optimal same-orientation chain
ending at each anchor. Each adjacent pair must increase in both ranks, with strictly fewer than
the allowed number of intervening genes on either side. The score adds the anchor weights
and the signed penalty for the larger gap at each step.

This is the scoring recurrence in Wang et al., *MCScanX: a toolkit for detection and evolutionary
analysis of gene synteny and collinearity*, Nucleic Acids Research 40(7), e49 (2012), Materials
and Methods. It does not model how anchors are inferred, how blocks are extracted, or how a
reporting threshold is selected. The cost model charges one unit per predecessor inspection;
sorting the input and the bit costs of arithmetic are not included.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.CollinearChaining

open Cslib.Algorithms.Lean TimeM

/-- An anchor records the two ranks and the score of a supplied match. -/
structure Anchor where
  first : ℕ
  second : ℕ
  weight : ℤ
  deriving DecidableEq, Repr

/-- For increasing anchors, the larger of the two numbers of intervening ranks. -/
def gaps (u v : Anchor) : ℕ :=
  max (v.first - u.first - 1) (v.second - u.second - 1)

/-- An extension is strictly increasing in both ranks and lies below the gap limit. -/
def Admissible (gapLimit : ℕ) (u v : Anchor) : Prop :=
  u.first < v.first ∧ u.second < v.second ∧ gaps u v < gapLimit

instance (gapLimit : ℕ) (u v : Anchor) : Decidable (Admissible gapLimit u v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Extend a chain of the given score from `u` to `v`, adding the new weight and gap penalty. -/
def extension (penalty : ℤ) (u v : Anchor) (score : ℤ) : ℤ :=
  score + v.weight + (gaps u v : ℤ) * penalty

/-- The score of a nonempty chain, with the last anchor `v` first and its predecessors listed
backwards. Each extension adds one anchor weight and one signed gap penalty. -/
def chainScore (penalty : ℤ) (v : Anchor) : List Anchor → ℤ
  | [] => v.weight
  | u :: rest => extension penalty u v (chainScore penalty u rest)

/-- The score is attained by some admissible chain ending at `v`, and bounds every such chain.
Only the predecessors have to be drawn from `anchors`; `v` is given separately. -/
def IsBestScore (gapLimit : ℕ) (penalty : ℤ) (anchors : List Anchor) (v : Anchor)
    (score : ℤ) : Prop :=
  (∃ rest, (∀ u ∈ rest, u ∈ anchors) ∧
    (v :: rest).IsChain (fun b a => Admissible gapLimit a b) ∧
    chainScore penalty v rest = score) ∧
  ∀ rest, (∀ u ∈ rest, u ∈ anchors) →
    (v :: rest).IsChain (fun b a => Admissible gapLimit a b) →
    chainScore penalty v rest ≤ score

/-- Start with the singleton chain at `v`, then take the best score among its admissible
predecessors in the table, charging one unit per inspected cell. -/
def bestExtension (gapLimit : ℕ) (penalty : ℤ) (v : Anchor) :
    List (Anchor × ℤ) → TimeM ℕ ℤ
  | [] => pure v.weight
  | (u, s) :: rest => do
      ✓
      let best ← bestExtension gapLimit penalty v rest
      let next := extension penalty u v s
      pure (if Admissible gapLimit u v ∧ best < next then next else best)

/-- Build the score table right to left, so that on input in nonincreasing first-rank order
all possible predecessors of the current anchor have already been scored. -/
def scoreTable (gapLimit : ℕ) (penalty : ℤ) : List Anchor → TimeM ℕ (List (Anchor × ℤ))
  | [] => pure []
  | v :: rest => do
      let table ← scoreTable gapLimit penalty rest
      let best ← bestExtension gapLimit penalty v table
      pure ((v, best) :: table)

private theorem bestExtension_spec (gapLimit : ℕ) (penalty : ℤ) (v : Anchor)
    (table : List (Anchor × ℤ)) :
    let best := (bestExtension gapLimit penalty v table).ret
    v.weight ≤ best ∧
      (∀ u s, (u, s) ∈ table → Admissible gapLimit u v → extension penalty u v s ≤ best) ∧
      (best = v.weight ∨ ∃ u s, (u, s) ∈ table ∧ Admissible gapLimit u v ∧
        best = extension penalty u v s) := by
  induction table with
  | nil => simp [bestExtension]
  | cons e t ih =>
      obtain ⟨u, s⟩ := e
      obtain ⟨hbase, hbound, hatt⟩ := ih
      simp only [bestExtension, ret_bind, ret_pure]
      set best := (bestExtension gapLimit penalty v t).ret
      by_cases h : Admissible gapLimit u v ∧ best < extension penalty u v s
      · simp only [h]
        refine ⟨hbase.trans h.2.le, ?_, Or.inr ⟨u, s, List.mem_cons_self, h.1, rfl⟩⟩
        intro x k hmem hadm
        rcases List.mem_cons.mp hmem with hpair | htail
        · cases hpair
          exact le_rfl
        · exact (hbound x k htail hadm).trans h.2.le
      · simp only [h, ite_false]
        refine ⟨hbase, ?_, ?_⟩
        · intro x k hmem hadm
          rcases List.mem_cons.mp hmem with hpair | htail
          · cases hpair
            exact le_of_not_gt (fun hlt => h ⟨hadm, hlt⟩)
          · exact hbound x k htail hadm
        · rcases hatt with hv | ⟨x, k, hx, hxy, hk⟩
          · exact Or.inl hv
          · exact Or.inr ⟨x, k, List.mem_cons_of_mem _ hx, hxy, hk⟩

private theorem bestExtension_isBestScore {gapLimit : ℕ} {penalty : ℤ} {v : Anchor}
    {anchors : List Anchor} {table : List (Anchor × ℤ)}
    (sound : ∀ u s, (u, s) ∈ table → u ∈ anchors ∧ IsBestScore gapLimit penalty anchors u s)
    (complete : ∀ u ∈ anchors, ∃ s, (u, s) ∈ table) :
    IsBestScore gapLimit penalty anchors v (bestExtension gapLimit penalty v table).ret := by
  obtain ⟨hbase, hbound, hatt⟩ := bestExtension_spec gapLimit penalty v table
  refine ⟨?_, ?_⟩
  · rcases hatt with hv | ⟨u, s, hu, hstep, hs⟩
    · exact ⟨[], by simp, List.IsChain.singleton _, hv.symm⟩
    · obtain ⟨hmem, hopt⟩ := sound u s hu
      obtain ⟨rest, hrest, hchain, hscore⟩ := hopt.1
      refine ⟨u :: rest, ?_, List.isChain_cons_cons.mpr ⟨hstep, hchain⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hmem
        · exact hrest x hx
      · simp only [chainScore, hs, extension, hscore]
  · intro rest hmem hchain
    cases rest with
    | nil => exact hbase
    | cons u rest =>
        obtain ⟨s, hs⟩ := complete u (hmem _ List.mem_cons_self)
        obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hchain
        have hle := (sound u s hs).2.2 rest
          (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) htail
        calc
          chainScore penalty v (u :: rest) ≤ extension penalty u v s := by
            change chainScore penalty u rest + v.weight + (gaps u v : ℤ) * penalty ≤
              s + v.weight + (gaps u v : ℤ) * penalty
            exact add_le_add (add_le_add hle le_rfl) le_rfl
          _ ≤ (bestExtension gapLimit penalty v table).ret := hbound u s hs hstep

private theorem first_lt_of_mem_chain_tail {gapLimit : ℕ} {v u : Anchor} {rest : List Anchor}
    (h : (v :: rest).IsChain (fun b a => Admissible gapLimit a b)) (hu : u ∈ rest) :
    u.first < v.first := by
  induction rest generalizing v with
  | nil => simp at hu
  | cons x rest ih =>
      obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp h
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hstep.1
      · exact (ih htail hu).trans hstep.1

private theorem bestScore_cons_iff {gapLimit : ℕ} {penalty score : ℤ} {v x : Anchor}
    {anchors : List Anchor} (hr : v.first ≤ x.first) :
    IsBestScore gapLimit penalty (x :: anchors) v score ↔
      IsBestScore gapLimit penalty anchors v score := by
  have narrow (rest : List Anchor)
      (hc : (v :: rest).IsChain (fun b a => Admissible gapLimit a b))
      (hm : ∀ u ∈ rest, u ∈ x :: anchors) : ∀ u ∈ rest, u ∈ anchors := by
    intro u hu
    rcases List.mem_cons.mp (hm u hu) with rfl | hu'
    · exact (not_lt_of_ge hr (first_lt_of_mem_chain_tail hc hu)).elim
    · exact hu'
  have widen (rest : List Anchor) (hm : ∀ u ∈ rest, u ∈ anchors) :
      ∀ u ∈ rest, u ∈ x :: anchors := fun u hu => List.mem_cons_of_mem _ (hm u hu)
  constructor
  · rintro ⟨⟨rest, hm, hc, hs⟩, hopt⟩
    exact ⟨⟨rest, narrow rest hc hm, hc, hs⟩, fun zs hz hc' => hopt zs (widen zs hz) hc'⟩
  · rintro ⟨⟨rest, hm, hc, hs⟩, hopt⟩
    exact ⟨⟨rest, widen rest hm, hc, hs⟩, fun zs hz hc' => hopt zs (narrow zs hc' hz) hc'⟩

/-- **Optimal scores of collinear chains.** On a list sorted in nonincreasing first rank,
with ties allowed, the table contains an attained optimal score for every anchor, and every
listed score is optimal for its anchor among chains in the input. -/
theorem scoreTable_spec (gapLimit : ℕ) (penalty : ℤ) (anchors : List Anchor)
    (sorted : anchors.Pairwise (fun v u => u.first ≤ v.first)) :
    let table := (scoreTable gapLimit penalty anchors).ret
    (∀ v s, (v, s) ∈ table → v ∈ anchors ∧ IsBestScore gapLimit penalty anchors v s) ∧
      ∀ v ∈ anchors, ∃ s, (v, s) ∈ table := by
  induction anchors with
  | nil => simp [scoreTable]
  | cons v rest ih =>
      obtain ⟨hr, hsorted⟩ := List.pairwise_cons.mp sorted
      obtain ⟨hsound, hcomplete⟩ := ih hsorted
      have hbest := bestExtension_isBestScore (v := v) hsound hcomplete
      simp only [scoreTable, ret_bind, ret_pure]
      constructor
      · intro x s hmem
        rcases List.mem_cons.mp hmem with he | ht
        · cases he
          exact ⟨List.mem_cons_self, (bestScore_cons_iff le_rfl).mpr hbest⟩
        · obtain ⟨hx, hopt⟩ := hsound x s ht
          exact ⟨List.mem_cons_of_mem _ hx, (bestScore_cons_iff (hr _ hx)).mpr hopt⟩
      · intro x hmem
        rcases List.mem_cons.mp hmem with rfl | hx
        · exact ⟨_, List.mem_cons_self⟩
        · obtain ⟨s, hs⟩ := hcomplete x hx
          exact ⟨s, List.mem_cons_of_mem _ hs⟩

@[simp]
private theorem bestExtension_time (gapLimit : ℕ) (penalty : ℤ) (v : Anchor)
    (table : List (Anchor × ℤ)) : (bestExtension gapLimit penalty v table).time = table.length := by
  induction table with
  | nil => simp [bestExtension]
  | cons e t ih =>
      cases e
      simp [bestExtension, ih, Nat.add_comm]

@[simp]
private theorem scoreTable_length (gapLimit : ℕ) (penalty : ℤ) (anchors : List Anchor) :
    (scoreTable gapLimit penalty anchors).ret.length = anchors.length := by
  induction anchors with
  | nil => simp [scoreTable]
  | cons v rest ih => simp [scoreTable, ih]

/-- **Quadratic count of predecessor inspections.** On `n` input anchors, twice the
number of charged table inspections equals `n * (n - 1)`.
The proof follows `lisTable_time` in `LongestIncreasingSubsequence.lean`. -/
theorem scoreTable_time (gapLimit : ℕ) (penalty : ℤ) (anchors : List Anchor) :
    2 * (scoreTable gapLimit penalty anchors).time = anchors.length * (anchors.length - 1) := by
  induction anchors with
  | nil => simp [scoreTable]
  | cons v rest ih =>
      simp only [scoreTable, time_bind, bestExtension_time, scoreTable_length, time_pure,
        List.length_cons, Nat.add_sub_cancel, Nat.add_zero]
      obtain ⟨n, hn⟩ : ∃ n, rest.length = n := ⟨_, rfl⟩
      rw [hn] at ih ⊢
      rcases n with _ | n
      · simp only [Nat.zero_mul] at ih
        omega
      · simp only [Nat.add_sub_cancel] at ih
        rw [Nat.mul_add, ih]
        ring

end Cslib.Bioinformatics.CollinearChaining
