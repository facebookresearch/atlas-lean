/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.Huffman
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Optimality of Huffman coding

The executable heap algorithm is related to the standard exchange-and-contraction
proof through a trace of its two-minimum merges.  The auxiliary tree below erases
symbols, which keeps the exchange argument independent of symbol equality.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- A full binary tree carrying only real-valued leaf weights. -/
inductive HuffmanWeightTree where
  | leaf (weight : Real)
  | fork (left right : HuffmanWeightTree)
deriving Inhabited


namespace HuffmanWeightTree

/-- Leaf weights, independent of their locations in the tree. -/
def weights : HuffmanWeightTree → Multiset Real
  | .leaf weight => {weight}
  | .fork left right => left.weights + right.weights

/-- Sum of all leaf weights. -/
def totalWeight : HuffmanWeightTree → Real
  | .leaf weight => weight
  | .fork left right => left.totalWeight + right.totalWeight

/-- Weighted external path length, defined directly by the merge recurrence. -/
def pathCost : HuffmanWeightTree → Real
  | .leaf _ => 0
  | .fork left right =>
      left.pathCost + right.pathCost + left.totalWeight + right.totalWeight

/-- Height of the underlying full binary tree. -/
def height : HuffmanWeightTree → Nat
  | .leaf _ => 0
  | .fork left right => Nat.succ (max left.height right.height)

@[simp] theorem weights_leaf (weight : Real) : (leaf weight).weights = {weight} := rfl

@[simp] theorem weights_fork (left right : HuffmanWeightTree) :
    (fork left right).weights = left.weights + right.weights := rfl

@[simp] theorem totalWeight_leaf (weight : Real) :
    (leaf weight).totalWeight = weight := rfl

@[simp] theorem totalWeight_fork (left right : HuffmanWeightTree) :
    (fork left right).totalWeight = left.totalWeight + right.totalWeight := rfl

@[simp] theorem pathCost_leaf (weight : Real) : (leaf weight).pathCost = 0 := rfl

@[simp] theorem pathCost_fork (left right : HuffmanWeightTree) :
    (fork left right).pathCost =
      left.pathCost + right.pathCost + left.totalWeight + right.totalWeight := rfl

@[simp] theorem height_leaf (weight : Real) : (leaf weight).height = 0 := rfl

@[simp] theorem height_fork (left right : HuffmanWeightTree) :
    (fork left right).height = Nat.succ (max left.height right.height) := rfl

theorem totalWeight_eq_sum (tree : HuffmanWeightTree) :
    tree.totalWeight = tree.weights.sum := by
  induction tree with
  | leaf weight => simp
  | fork left right ihLeft ihRight => simp [ihLeft, ihRight]

theorem weights_ne_zero (tree : HuffmanWeightTree) : tree.weights ≠ 0 := by
  induction tree with
  | leaf weight => simp
  | fork left right ihLeft _ =>
      intro hzero
      have := congrArg Multiset.card hzero
      simp only [weights_fork, Multiset.card_add, Multiset.card_zero] at this
      have : Multiset.card left.weights = 0 := by omega
      exact ihLeft (Multiset.card_eq_zero.mp this)

theorem eq_leaf_of_height_eq_zero {tree : HuffmanWeightTree}
    (hheight : tree.height = 0) : ∃ weight, tree = leaf weight := by
  cases tree with
  | leaf weight => exact ⟨weight, rfl⟩
  | fork left right => simp at hheight

/-- A proof that a particular occurrence of a weight sits at a given depth. -/
inductive ContainsAt (value : Real) : HuffmanWeightTree → Nat → Prop where
  | root : ContainsAt value (.leaf value) 0
  | descendLeft {left right depth}
      (h : ContainsAt value left depth) :
      ContainsAt value (.fork left right) (depth + 1)
  | descendRight {left right depth}
      (h : ContainsAt value right depth) :
      ContainsAt value (.fork left right) (depth + 1)

theorem containsAt_iff_mem {value : Real} {tree : HuffmanWeightTree} :
    value ∈ tree.weights ↔ ∃ depth, ContainsAt value tree depth := by
  induction tree with
  | leaf weight =>
      constructor
      · intro h
        have : value = weight := by simpa using h
        subst value
        exact ⟨0, .root⟩
      · rintro ⟨depth, h⟩
        cases h
        simp
  | fork left right ihLeft ihRight =>
      rw [weights_fork, Multiset.mem_add, ihLeft, ihRight]
      constructor
      · rintro (⟨depth, h⟩ | ⟨depth, h⟩)
        · exact ⟨depth + 1, .descendLeft h⟩
        · exact ⟨depth + 1, .descendRight h⟩
      · rintro ⟨depth, h⟩
        cases h with
        | descendLeft h => exact Or.inl ⟨_, h⟩
        | descendRight h => exact Or.inr ⟨_, h⟩

theorem ContainsAt.depth_le_height {value : Real} {tree : HuffmanWeightTree}
    {depth : Nat} (h : ContainsAt value tree depth) : depth ≤ tree.height := by
  induction h with
  | root => simp
  | descendLeft h ih =>
      simp only [height_fork]
      omega
  | descendRight h ih =>
      simp only [height_fork]
      omega

/-- Change one specified leaf occurrence and record its exact cost change. -/
theorem ContainsAt.reweight {value replacement : Real}
    {tree : HuffmanWeightTree} {depth : Nat}
    (h : ContainsAt value tree depth) :
    ∃ (remainder : Multiset Real) (result : HuffmanWeightTree),
      tree.weights = value ::ₘ remainder ∧
      result.weights = replacement ::ₘ remainder ∧
      result.totalWeight = tree.totalWeight + (replacement - value) ∧
      result.pathCost =
        tree.pathCost + (depth : Real) * (replacement - value) ∧
      result.height = tree.height := by
  induction h with
  | root =>
      refine ⟨0, leaf replacement, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  | @descendLeft left right depth h ih =>
      obtain ⟨remainder, changed, hweights, hchangedWeights,
        htotal, hcost, hheight⟩ := ih
      refine ⟨remainder + right.weights, fork changed right, ?_, ?_, ?_, ?_, ?_⟩
      · rw [weights_fork, hweights, Multiset.cons_add]
      · rw [weights_fork, hchangedWeights, Multiset.cons_add]
      · simp only [totalWeight_fork, htotal]
        ring
      · simp only [pathCost_fork, hcost, htotal]
        push_cast
        ring
      · simp [hheight]
  | @descendRight left right depth h ih =>
      obtain ⟨remainder, changed, hweights, hchangedWeights,
        htotal, hcost, hheight⟩ := ih
      refine ⟨left.weights + remainder, fork left changed, ?_, ?_, ?_, ?_, ?_⟩
      · rw [weights_fork, hweights, Multiset.add_cons]
      · rw [weights_fork, hchangedWeights, Multiset.add_cons]
      · simp only [totalWeight_fork, htotal]
        ring
      · simp only [pathCost_fork, hcost, htotal]
        push_cast
        ring
      · simp [hheight]

/-- Replace one smaller weight by a larger one, with a height-based cost bound. -/
theorem raiseBounded {bound : Nat} (tree : HuffmanWeightTree)
    (hheight : tree.height ≤ bound) (target : Multiset Real)
    (replacement value : Real)
    (hweights : replacement ::ₘ tree.weights = value ::ₘ target)
    (hle : value ≤ replacement) :
    ∃ result : HuffmanWeightTree,
      result.weights = target ∧ result.height ≤ bound ∧
      result.pathCost ≤
        tree.pathCost + (bound : Real) * (replacement - value) := by
  by_cases hsame : value = replacement
  · subst value
    refine ⟨tree, (Multiset.cons_inj_right replacement).mp hweights, hheight, ?_⟩
    simp
  · have hmem : value ∈ tree.weights := by
      have : value ∈ replacement ::ₘ tree.weights := by
        rw [hweights]
        exact Multiset.mem_cons_self _ _
      rcases Multiset.mem_cons.mp this with h | h
      · exact absurd h hsame
      · exact h
    obtain ⟨depth, hoccurs⟩ := containsAt_iff_mem.mp hmem
    obtain ⟨remainder, result, htreeWeights, hresultWeights,
      _, hresultCost, hresultHeight⟩ :=
        hoccurs.reweight (replacement := replacement)
    have htarget : target = replacement ::ₘ remainder := by
      have hcancel :
          value ::ₘ (replacement ::ₘ remainder) = value ::ₘ target := by
        calc
          value ::ₘ (replacement ::ₘ remainder) =
              replacement ::ₘ (value ::ₘ remainder) :=
                Multiset.cons_swap _ _ _
          _ = replacement ::ₘ tree.weights := by rw [htreeWeights]
          _ = value ::ₘ target := hweights
      exact ((Multiset.cons_inj_right value).mp hcancel).symm
    refine ⟨result, hresultWeights.trans htarget.symm, ?_, ?_⟩
    · rw [hresultHeight]
      exact hheight
    · have hdepth := hoccurs.depth_le_height.trans hheight
      have hcast : (depth : Real) ≤ bound := by exact_mod_cast hdepth
      rw [hresultCost]
      nlinarith [sub_nonneg.mpr hle]

private theorem split_two_replacements
    (source : Multiset Real) (first second least next : Real)
    (target : Multiset Real)
    (hweights : first ::ₘ second ::ₘ source = least ::ₘ next ::ₘ target)
    (hleastNext : least ≤ next) (hnextSecond : next ≤ second)
    (hne : least ≠ first) :
    ∃ middle : Multiset Real,
      first ::ₘ source = least ::ₘ middle ∧
      second ::ₘ middle = next ::ₘ target := by
  have hleastSource : least ∈ source := by
    have hleastAll : least ∈ first ::ₘ second ::ₘ source := by
      rw [hweights]
      exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_cons.mp hleastAll with hfirst | htail
    · exact absurd hfirst hne
    · rcases Multiset.mem_cons.mp htail with hsecond | hsource
      · have hnextLeast : next ≤ least := by
          rw [hsecond]
          exact hnextSecond
        have hequal : least = next := le_antisymm hleastNext hnextLeast
        have hcancel : first ::ₘ source = least ::ₘ target := by
          have : least ::ₘ (first ::ₘ source) =
              least ::ₘ (least ::ₘ target) := by
            calc
              least ::ₘ (first ::ₘ source) =
                  first ::ₘ (least ::ₘ source) := Multiset.cons_swap _ _ _
              _ = first ::ₘ (second ::ₘ source) := by rw [hsecond]
              _ = least ::ₘ (next ::ₘ target) := hweights
              _ = least ::ₘ (least ::ₘ target) := by rw [← hequal]
          exact (Multiset.cons_inj_right least).mp this
        have : least ∈ first ::ₘ source := by
          rw [hcancel]
          exact Multiset.mem_cons_self _ _
        rcases Multiset.mem_cons.mp this with hfirst | hsource
        · exact absurd hfirst hne
        · exact hsource
      · exact hsource
  obtain ⟨tail, hsource⟩ := Multiset.exists_cons_of_mem hleastSource
  refine ⟨first ::ₘ tail, ?_, ?_⟩
  · rw [hsource, Multiset.cons_swap]
  · have hcancel :
        least ::ₘ (second ::ₘ first ::ₘ tail) =
          least ::ₘ (next ::ₘ target) := by
      calc
        least ::ₘ (second ::ₘ first ::ₘ tail) =
            first ::ₘ (second ::ₘ least ::ₘ tail) := by
              change ({least} + ({second} + ({first} + tail))) =
                ({first} + ({second} + ({least} + tail)))
              abel
        _ = first ::ₘ second ::ₘ source := by rw [hsource]
        _ = least ::ₘ next ::ₘ target := hweights
    have := (Multiset.cons_inj_right least).mp hcancel
    rw [← this, Multiset.cons_swap]

/-- Perform two occurrence-preserving weight exchanges. -/
theorem raisePair {bound : Nat} (tree : HuffmanWeightTree)
    (hheight : tree.height ≤ bound) (target : Multiset Real)
    (first second least next : Real)
    (hweights : first ::ₘ second ::ₘ tree.weights =
      least ::ₘ next ::ₘ target)
    (hleastNext : least ≤ next) (hleastFirst : least ≤ first)
    (hnextSecond : next ≤ second) :
    ∃ result : HuffmanWeightTree,
      result.weights = target ∧
      result.pathCost ≤ tree.pathCost +
        (bound : Real) * (first - least) +
        (bound : Real) * (second - next) := by
  by_cases hsame : least = first
  · subst least
    have hcancel : second ::ₘ tree.weights = next ::ₘ target := by
      apply (Multiset.cons_inj_right first).mp
      calc
        first ::ₘ (second ::ₘ tree.weights) =
            first ::ₘ second ::ₘ tree.weights := rfl
        _ = first ::ₘ next ::ₘ target := hweights
    obtain ⟨result, hresultWeights, _, hresultCost⟩ :=
      raiseBounded tree hheight target second next hcancel hnextSecond
    refine ⟨result, hresultWeights, ?_⟩
    simpa using hresultCost
  · obtain ⟨middle, hfirst, hsecond⟩ :=
      split_two_replacements tree.weights first second least next target
        hweights hleastNext hnextSecond hsame
    obtain ⟨firstResult, hfirstWeights, hfirstHeight, hfirstCost⟩ :=
      raiseBounded tree hheight middle first least hfirst hleastFirst
    obtain ⟨result, hresultWeights, _, hsecondCost⟩ :=
      raiseBounded firstResult hfirstHeight target second next
        (by rw [hfirstWeights]; exact hsecond) hnextSecond
    exact ⟨result, hresultWeights, by linarith⟩

/-- Expose a deepest sibling pair and describe contraction by structural cost
identities, without representing the whole tree as weight-depth pairs. -/
theorem exists_cherry_contraction (tree : HuffmanWeightTree)
    (hpositive : 1 ≤ tree.height) :
    ∃ (first second : Real) (remainder : Multiset Real) (baseCost : Real),
      tree.weights = first ::ₘ second ::ₘ remainder ∧
      tree.pathCost =
        baseCost + (tree.height : Real) * first +
          (tree.height : Real) * second ∧
      ∀ combined : Real, ∃ result : HuffmanWeightTree,
        result.weights = combined ::ₘ remainder ∧
        result.height ≤ tree.height ∧
        result.pathCost =
          baseCost + ((tree.height - 1 : Nat) : Real) * combined := by
  induction tree with
  | leaf weight => simp at hpositive
  | fork left right ihLeft ihRight =>
      by_cases hright : right.height ≤ left.height
      · have hheight : (fork left right).height = left.height + 1 := by
          simp only [height_fork]
          omega
        rcases Nat.eq_zero_or_pos left.height with hzero | hleftPositive
        · obtain ⟨first, rfl⟩ := eq_leaf_of_height_eq_zero hzero
          have hrightZero : right.height = 0 := by omega
          obtain ⟨second, rfl⟩ := eq_leaf_of_height_eq_zero hrightZero
          refine ⟨first, second, 0, 0, ?_, ?_, ?_⟩
          · simp
          · simp
          · intro combined
            refine ⟨leaf combined, by simp, by simp, ?_⟩
            simp
        · obtain ⟨first, second, innerRest, innerBase,
            hinnerWeights, hinnerCost, hcontract⟩ := ihLeft hleftPositive
          let remainder := innerRest + right.weights
          let baseCost :=
            innerBase + right.pathCost + innerRest.sum + right.totalWeight
          refine ⟨first, second, remainder, baseCost, ?_, ?_, ?_⟩
          · simp only [weights_fork, hinnerWeights, remainder,
              Multiset.cons_add]
          · have hleftTotal : left.totalWeight =
                first + second + innerRest.sum := by
              rw [totalWeight_eq_sum, hinnerWeights]
              simp
              ring
            simp only [pathCost_fork, hinnerCost, hleftTotal, hheight,
              baseCost]
            push_cast
            ring
          · intro combined
            obtain ⟨changed, hchangedWeights, hchangedHeight, hchangedCost⟩ :=
              hcontract combined
            refine ⟨fork changed right, ?_, ?_, ?_⟩
            · simp only [weights_fork, hchangedWeights, remainder,
                Multiset.cons_add]
            · simp only [height_fork, hheight]
              omega
            · have hchangedTotal : changed.totalWeight =
                  combined + innerRest.sum := by
                rw [totalWeight_eq_sum, hchangedWeights]
                simp
              rw [hheight]
              have hsub : left.height + 1 - 1 = left.height := by omega
              rw [hsub]
              have hcast :
                  (((left.height - 1 : Nat) : Real) + 1) = left.height := by
                rw [Nat.cast_sub hleftPositive]
                norm_num
              simp only [pathCost_fork, hchangedCost, hchangedTotal,
                baseCost]
              calc
                innerBase + (left.height - 1 : Nat) * combined +
                      right.pathCost + (combined + innerRest.sum) +
                      right.totalWeight =
                    innerBase + right.pathCost + innerRest.sum +
                      right.totalWeight +
                      (((left.height - 1 : Nat) : Real) + 1) * combined := by ring
                _ = innerBase + right.pathCost + innerRest.sum +
                      right.totalWeight + left.height * combined := by
                        rw [hcast]
      · have hleft : left.height ≤ right.height := by omega
        have hheight : (fork left right).height = right.height + 1 := by
          simp only [height_fork]
          omega
        have hrightPositive : 1 ≤ right.height := by omega
        obtain ⟨first, second, innerRest, innerBase,
            hinnerWeights, hinnerCost, hcontract⟩ := ihRight hrightPositive
        let remainder := left.weights + innerRest
        let baseCost :=
          innerBase + left.pathCost + left.totalWeight + innerRest.sum
        refine ⟨first, second, remainder, baseCost, ?_, ?_, ?_⟩
        · simp only [weights_fork, hinnerWeights, remainder,
            Multiset.add_cons]
        · have hrightTotal : right.totalWeight =
              first + second + innerRest.sum := by
            rw [totalWeight_eq_sum, hinnerWeights]
            simp
            ring
          simp only [pathCost_fork, hinnerCost, hrightTotal, hheight,
            baseCost]
          push_cast
          ring
        · intro combined
          obtain ⟨changed, hchangedWeights, hchangedHeight, hchangedCost⟩ :=
            hcontract combined
          refine ⟨fork left changed, ?_, ?_, ?_⟩
          · simp only [weights_fork, hchangedWeights, remainder,
              Multiset.add_cons]
          · simp only [height_fork, hheight]
            omega
          · have hchangedTotal : changed.totalWeight =
                combined + innerRest.sum := by
              rw [totalWeight_eq_sum, hchangedWeights]
              simp
            rw [hheight]
            have hsub : right.height + 1 - 1 = right.height := by omega
            rw [hsub]
            have hcast :
                (((right.height - 1 : Nat) : Real) + 1) = right.height := by
              rw [Nat.cast_sub hrightPositive]
              norm_num
            simp only [pathCost_fork, hchangedCost, hchangedTotal,
              baseCost]
            calc
              left.pathCost +
                    (innerBase + (right.height - 1 : Nat) * combined) +
                    left.totalWeight + (combined + innerRest.sum) =
                  innerBase + left.pathCost + left.totalWeight +
                    innerRest.sum +
                    (((right.height - 1 : Nat) : Real) + 1) * combined := by ring
              _ = innerBase + left.pathCost + left.totalWeight +
                    innerRest.sum + right.height * combined := by
                      rw [hcast]

private theorem second_le_one_of_two {first second least next : Real}
    {remainder target : Multiset Real}
    (hweights : first ::ₘ second ::ₘ remainder =
      least ::ₘ next ::ₘ target)
    (hleastNext : least ≤ next)
    (htarget : ∀ weight ∈ target, next ≤ weight) :
    next ≤ first ∨ next ≤ second := by
  have hleastAll : ∀ weight ∈ least ::ₘ next ::ₘ target, least ≤ weight := by
    intro weight hweight
    rcases Multiset.mem_cons.mp hweight with rfl | hweight
    · exact le_rfl
    · rcases Multiset.mem_cons.mp hweight with rfl | hweight
      · exact hleastNext
      · exact hleastNext.trans (htarget weight hweight)
  have hfirstMem : first ∈ least ::ₘ next ::ₘ target := by
    rw [← hweights]
    exact Multiset.mem_cons_self _ _
  have hsecondMem : second ∈ least ::ₘ next ::ₘ target := by
    rw [← hweights]
    exact Multiset.mem_cons.mpr (Or.inr (Multiset.mem_cons_self _ _))
  by_contra hnone
  push Not at hnone
  obtain ⟨hfirstSmall, hsecondSmall⟩ := hnone
  have hfirstEq : first = least := by
    rcases Multiset.mem_cons.mp hfirstMem with h | h
    · exact h
    · rcases Multiset.mem_cons.mp h with h | h
      · exfalso
        rw [h] at hfirstSmall
        exact (lt_irrefl next) hfirstSmall
      · exact absurd (htarget first h) (not_le.mpr hfirstSmall)
  have hsecondEq : second = least := by
    rcases Multiset.mem_cons.mp hsecondMem with h | h
    · exact h
    · rcases Multiset.mem_cons.mp h with h | h
      · exfalso
        rw [h] at hsecondSmall
        exact (lt_irrefl next) hsecondSmall
      · exact absurd (htarget second h) (not_le.mpr hsecondSmall)
  have hcancel : least ::ₘ remainder = next ::ₘ target := by
    rw [hfirstEq, hsecondEq] at hweights
    exact (Multiset.cons_inj_right least).mp hweights
  have hnextLeast : next ≤ least := by
    have : least ∈ next ::ₘ target := by
      rw [← hcancel]
      exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_cons.mp this with h | h
    · exact le_of_eq h.symm
    · exact htarget least h
  rw [hfirstEq] at hfirstSmall
  exact (not_le.mpr hfirstSmall) hnextLeast

/-- Contract the two least weights after an independently derived sibling
exchange argument on structural tree cost. -/
theorem contractLeastPair (tree : HuffmanWeightTree) (least next : Real)
    (tail : Multiset Real)
    (htree : tree.weights = least ::ₘ next ::ₘ tail)
    (hleastNext : least ≤ next)
    (htail : ∀ weight ∈ tail, next ≤ weight) :
    ∃ result : HuffmanWeightTree,
      result.weights = (least + next) ::ₘ tail ∧
      result.pathCost + least + next ≤ tree.pathCost := by
  have hpositive : 1 ≤ tree.height := by
    rcases Nat.eq_zero_or_pos tree.height with hzero | hpositive
    · obtain ⟨weight, rfl⟩ := eq_leaf_of_height_eq_zero hzero
      simp at htree
    · exact hpositive
  obtain ⟨first, second, remainder, baseCost,
      hweights, htreeCost, hcontract⟩ :=
    exists_cherry_contraction tree hpositive
  have hpairs :
      first ::ₘ second ::ₘ remainder = least ::ₘ next ::ₘ tail := by
    rw [← hweights, htree]
  have hleastAll : ∀ weight ∈ least ::ₘ next ::ₘ tail, least ≤ weight := by
    intro weight hweight
    rcases Multiset.mem_cons.mp hweight with rfl | hweight
    · exact le_rfl
    · rcases Multiset.mem_cons.mp hweight with rfl | hweight
      · exact hleastNext
      · exact hleastNext.trans (htail weight hweight)
  have hleastFirst : least ≤ first := hleastAll first (by
    rw [← hpairs]
    exact Multiset.mem_cons_self _ _)
  have hleastSecond : least ≤ second := hleastAll second (by
    rw [← hpairs]
    exact Multiset.mem_cons.mpr (Or.inr (Multiset.mem_cons_self _ _)))
  have horient := second_le_one_of_two hpairs hleastNext htail
  have finish : ∀ upper lower : Real,
      upper ::ₘ lower ::ₘ remainder = least ::ₘ next ::ₘ tail →
      least ≤ upper → next ≤ lower →
      ∃ result : HuffmanWeightTree,
        result.weights = (least + next) ::ₘ tail ∧
        result.pathCost + least + next ≤ tree.pathCost := by
    intro upper lower horiented hleastUpper hnextLower
    obtain ⟨contracted, hcontractedWeights, hcontractedHeight,
      hcontractedCost⟩ := hcontract (least + next)
    have hexchange :
        upper ::ₘ lower ::ₘ contracted.weights =
          least ::ₘ next ::ₘ ((least + next) ::ₘ tail) := by
      rw [hcontractedWeights]
      calc
        upper ::ₘ lower ::ₘ (least + next) ::ₘ remainder =
            (least + next) ::ₘ (upper ::ₘ lower ::ₘ remainder) := by
              change ({upper} + ({lower} + ({least + next} + remainder))) =
                ({least + next} + ({upper} + ({lower} + remainder)))
              abel
        _ = (least + next) ::ₘ (least ::ₘ next ::ₘ tail) := by
              rw [horiented]
        _ = least ::ₘ next ::ₘ ((least + next) ::ₘ tail) := by
              change ({least + next} + ({least} + ({next} + tail))) =
                ({least} + ({next} + ({least + next} + tail)))
              abel
    obtain ⟨result, hresultWeights, hresultCost⟩ :=
      raisePair contracted hcontractedHeight ((least + next) ::ₘ tail)
        upper lower least next hexchange hleastNext hleastUpper hnextLower
    refine ⟨result, hresultWeights, ?_⟩
    have hheightCast :
        ((tree.height - 1 : Nat) : Real) = (tree.height : Real) - 1 := by
      rw [Nat.cast_sub hpositive]
      norm_num
    rw [hcontractedCost, hheightCast] at hresultCost
    have hpairsOriented :
        upper ::ₘ lower ::ₘ remainder = first ::ₘ second ::ₘ remainder :=
      horiented.trans hpairs.symm
    have hsum : upper + lower = first + second := by
      have := congrArg Multiset.sum hpairsOriented
      simp only [Multiset.sum_cons] at this
      linarith
    rw [htreeCost]
    nlinarith
  rcases horient with hnextFirst | hnextSecond
  · apply finish second first
    · rw [Multiset.cons_swap]
      exact hpairs
    · exact hleastSecond
    · exact hnextFirst
  · exact finish first second hpairs hleastFirst hnextSecond

/-- A certificate that a cost is produced by repeated two-minimum merges. -/
inductive MergeTrace : Multiset Real → Real → Prop where
  | singleton (weight : Real) : MergeTrace {weight} 0
  | merge {least next tailCost : Real} {rest : Multiset Real}
      (hle : least ≤ next)
      (hrest : ∀ weight ∈ rest, next ≤ weight)
      (tailTrace : MergeTrace ((least + next) ::ₘ rest) tailCost) :
      MergeTrace (least ::ₘ next ::ₘ rest) (least + next + tailCost)

/-- Repeated two-minimum merges lower-bound every full tree with the same
weight multiset. -/
theorem MergeTrace.le_pathCost {weightBag : Multiset Real} {cost : Real}
    (trace : MergeTrace weightBag cost) (tree : HuffmanWeightTree)
    (htree : tree.weights = weightBag) : cost ≤ tree.pathCost := by
  induction trace generalizing tree with
  | singleton weight =>
      cases tree with
      | leaf value => simp
      | fork left right =>
          have hcard := congrArg Multiset.card htree
          simp only [weights_fork, Multiset.card_add, Multiset.card_singleton] at hcard
          have hleft : 1 ≤ Multiset.card left.weights :=
            Multiset.card_pos.mpr left.weights_ne_zero
          have hright : 1 ≤ Multiset.card right.weights :=
            Multiset.card_pos.mpr right.weights_ne_zero
          omega
  | merge hleastNext hrest tailTrace ih =>
      obtain ⟨contracted, hweights, hcost⟩ :=
        contractLeastPair tree _ _ _ htree hleastNext hrest
      have := ih contracted hweights
      linarith

end HuffmanWeightTree

/-- Erase symbols and cast natural weights to real weights. -/
def HuffmanTree.eraseSymbols {α : Type u} : HuffmanTree α → HuffmanWeightTree
  | .leaf _ weight => .leaf weight
  | .fork left right => .fork left.eraseSymbols right.eraseSymbols

/-- Erasure preserves the multiset of leaf weights. -/
theorem HuffmanTree.eraseSymbols_weights {α : Type u} (tree : HuffmanTree α) :
    tree.eraseSymbols.weights =
      (tree.weightedLeaves.map (fun pair => (pair.2 : Real)) : Multiset Real) := by
  induction tree with
  | leaf symbol weight => simp [HuffmanTree.eraseSymbols, HuffmanTree.weightedLeaves]
  | fork left right ihLeft ihRight =>
      simp [HuffmanTree.eraseSymbols, HuffmanTree.weightedLeaves, ihLeft, ihRight]

/-- Erasure preserves total weight after casting to the reals. -/
theorem HuffmanTree.eraseSymbols_totalWeight {α : Type u} (tree : HuffmanTree α) :
    tree.eraseSymbols.totalWeight = tree.totalWeight := by
  induction tree with
  | leaf symbol weight => simp [HuffmanTree.eraseSymbols, HuffmanTree.totalWeight]
  | fork left right ihLeft ihRight =>
      simp [HuffmanTree.eraseSymbols, HuffmanTree.totalWeight, ihLeft, ihRight]

/-- Erasure preserves weighted path length after casting to the reals. -/
theorem HuffmanTree.eraseSymbols_pathCost {α : Type u} (tree : HuffmanTree α) :
    tree.eraseSymbols.pathCost = tree.weightedPathLength := by
  induction tree with
  | leaf symbol weight => simp [HuffmanTree.eraseSymbols, HuffmanTree.weightedPathLength]
  | fork left right ihLeft ihRight =>
      simp [HuffmanTree.eraseSymbols, HuffmanTree.weightedPathLength,
        ihLeft, ihRight, HuffmanTree.eraseSymbols_totalWeight]

/-- Priorities represented by a work forest. -/
def huffmanForestPriorities {α : Type u} (forest : List (HuffmanWorkItem α)) :
    Multiset HuffmanPriority :=
  forest.map HuffmanWorkItem.priority

/-- Total weights represented by a work forest. -/
def huffmanForestWeights {α : Type u} (forest : List (HuffmanWorkItem α)) :
    Multiset Real :=
  forest.map (fun item => (item.tree.totalWeight : Real))

/-- Sum of the already-incurred subtree costs in a work forest. -/
def huffmanForestCost {α : Type u} (forest : List (HuffmanWorkItem α)) : Real :=
  (forest.map (fun item => (item.tree.weightedPathLength : Real))).sum

/-- The heap and the serial-indexed table describe the same
uniquely-serial-numbered weighted trees. -/
structure HuffmanLoopInvariant {α : Type u} (nextSerial : Nat)
    (heap : MinHeap HuffmanPriority)
    (table : Array (Option (HuffmanWorkItem α))) : Prop where
  heap_eq : heap.elements = huffmanForestPriorities (huffmanTableForest table)
  serials_nodup :
    ((huffmanTableForest table).map (fun item => item.priority.serial)).Nodup
  serial_lt : ∀ item ∈ huffmanTableForest table, item.priority.serial < nextSerial
  weight_eq : ∀ item ∈ huffmanTableForest table,
    item.priority.weight = item.tree.totalWeight
  size_eq : table.size = nextSerial
  stored : ∀ item ∈ huffmanTableForest table,
    table[item.priority.serial]? = some (some item)

private theorem eq_of_mem_of_mem_of_serial_eq {α : Type u}
    {first second : HuffmanWorkItem α} {forest : List (HuffmanWorkItem α)}
    (hnodup : (forest.map (fun item => item.priority.serial)).Nodup)
    (hfirst : first ∈ forest) (hsecond : second ∈ forest)
    (hserial : first.priority.serial = second.priority.serial) : first = second := by
  induction forest with
  | nil => simp at hfirst
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hfresh, htail⟩
      simp only [List.mem_cons] at hfirst hsecond
      rcases hfirst with rfl | hfirst
      · rcases hsecond with rfl | hsecond
        · rfl
        · exfalso
          apply hfresh
          exact List.mem_map.mpr ⟨second, hsecond, hserial.symm⟩
      · rcases hsecond with rfl | hsecond
        · exfalso
          apply hfresh
          exact List.mem_map.mpr ⟨first, hfirst, hserial⟩
        · exact ih htail hfirst hsecond

private theorem HuffmanLoopInvariant.takeSerial {α : Type u}
    {nextSerial serial : Nat} {heap : MinHeap HuffmanPriority}
    {table remaining : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (hinvariant : HuffmanLoopInvariant nextSerial heap table)
    {priority : HuffmanPriority} (hpriority : priority ∈ heap.elements)
    (hserial : priority.serial = serial)
    (htake : takeSerial? serial table = some (tree, remaining)) :
    (⟨priority, tree⟩ :: huffmanTableForest remaining).Perm
      (huffmanTableForest table) := by
  obtain ⟨item, htree, hitemSerial, hperm⟩ := takeSerial?_item htake
  have hfoundMem : item ∈ huffmanTableForest table :=
    hperm.mem_iff.mp (by simp)
  have hpriorityForest : priority ∈ huffmanForestPriorities (huffmanTableForest table) := by
    rw [← hinvariant.heap_eq]
    exact hpriority
  have hpriorityList :
      priority ∈ (huffmanTableForest table).map HuffmanWorkItem.priority := by
    simpa [huffmanForestPriorities] using hpriorityForest
  obtain ⟨item', hitem'Mem, hitem'Priority⟩ := List.mem_map.mp hpriorityList
  have heq : item = item' :=
    eq_of_mem_of_mem_of_serial_eq hinvariant.serials_nodup hfoundMem hitem'Mem (by
      rw [hitemSerial, ← hserial, hitem'Priority])
  have hpriorityEq : item.priority = priority := by
    rw [heq, hitem'Priority]
  cases item with
  | mk foundPriority foundTree =>
      change foundTree = tree at htree
      change foundPriority = priority at hpriorityEq
      subst htree
      subst hpriorityEq
      exact hperm

private theorem priority_weight_le {first second : HuffmanPriority}
    (h : first ≤ second) : first.weight ≤ second.weight := by
  change toLex (first.weight, first.serial) ≤ toLex (second.weight, second.serial) at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | h
  · exact h.le
  · exact le_of_eq h.1

private theorem huffmanForestPriorities_of_perm {α : Type u}
    {first second : List (HuffmanWorkItem α)} (h : first.Perm second) :
    huffmanForestPriorities first = huffmanForestPriorities second := by
  exact Multiset.coe_eq_coe.mpr (h.map HuffmanWorkItem.priority)

private theorem huffmanForestWeights_of_perm {α : Type u}
    {first second : List (HuffmanWorkItem α)} (h : first.Perm second) :
    huffmanForestWeights first = huffmanForestWeights second := by
  exact Multiset.coe_eq_coe.mpr (h.map fun item => (item.tree.totalWeight : Real))

private theorem huffmanForestCost_of_perm {α : Type u}
    {first second : List (HuffmanWorkItem α)} (h : first.Perm second) :
    huffmanForestCost first = huffmanForestCost second := by
  exact (h.map fun item => (item.tree.weightedPathLength : Real)).sum_eq

private theorem HuffmanLoopInvariant.afterTake {α : Type u}
    {nextSerial : Nat} {heap remainingHeap : MinHeap HuffmanPriority}
    {table remaining : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (hinvariant : HuffmanLoopInvariant nextSerial heap table)
    {priority : HuffmanPriority}
    (hpartition : priority ::ₘ remainingHeap.elements = heap.elements)
    (htake : takeSerial? priority.serial table = some (tree, remaining)) :
    HuffmanLoopInvariant nextSerial remainingHeap remaining := by
  have hpriority : priority ∈ heap.elements := by
    rw [← hpartition]
    exact Multiset.mem_cons_self _ _
  have hperm := hinvariant.takeSerial hpriority rfl htake
  have hpriorities := huffmanForestPriorities_of_perm hperm
  have hpriorityEq :
      priority ::ₘ huffmanForestPriorities (huffmanTableForest remaining) =
        heap.elements := by
    calc
      priority ::ₘ huffmanForestPriorities (huffmanTableForest remaining) =
          huffmanForestPriorities (⟨priority, tree⟩ :: huffmanTableForest remaining) := by
            rfl
      _ = huffmanForestPriorities (huffmanTableForest table) := hpriorities
      _ = heap.elements := hinvariant.heap_eq.symm
  have hheap : remainingHeap.elements =
      huffmanForestPriorities (huffmanTableForest remaining) :=
    (Multiset.cons_inj_right priority).mp (hpartition.trans hpriorityEq.symm)
  have hserials :
      ((⟨priority, tree⟩ : HuffmanWorkItem α) :: huffmanTableForest remaining).map
          (fun item => item.priority.serial) |>.Nodup := by
    exact (hperm.map fun item => item.priority.serial).nodup_iff.mpr
      hinvariant.serials_nodup
  refine {
    heap_eq := hheap
    serials_nodup := (List.nodup_cons.mp hserials).2
    serial_lt := ?_
    weight_eq := ?_
    size_eq := by rw [takeSerial?_size htake, hinvariant.size_eq]
    stored := ?_
  }
  · intro item hitem
    exact hinvariant.serial_lt item
      (hperm.mem_iff.mp (List.mem_cons_of_mem (⟨priority, tree⟩ : HuffmanWorkItem α) hitem))
  · intro item hitem
    exact hinvariant.weight_eq item
      (hperm.mem_iff.mp (List.mem_cons_of_mem (⟨priority, tree⟩ : HuffmanWorkItem α) hitem))
  · intro item hitem
    have hne : item.priority.serial ≠ priority.serial := by
      intro hh
      have hserialsCons := (List.nodup_cons.mp hserials).1
      apply hserialsCons
      exact List.mem_map.mpr ⟨item, hitem, hh⟩
    rw [takeSerial?_getElem?_of_ne htake hne]
    exact hinvariant.stored item
      (hperm.mem_iff.mp (List.mem_cons_of_mem (⟨priority, tree⟩ : HuffmanWorkItem α) hitem))

private theorem huffmanHeapOfForest_elements {α : Type u}
    (forest : List (HuffmanWorkItem α)) :
    (huffmanHeapOfForest forest).elements = huffmanForestPriorities forest := by
  have general : ∀ (items : List (HuffmanWorkItem α))
      (heap : MinHeap HuffmanPriority),
      (items.foldl (fun current item => current.push item.priority) heap).elements =
        huffmanForestPriorities items + heap.elements := by
    intro items
    induction items with
    | nil => intro heap; simp [huffmanForestPriorities]
    | cons item items ih =>
        intro heap
        simp only [List.foldl_cons]
        calc
          (items.foldl (fun current item => current.push item.priority)
              (heap.push item.priority)).elements =
              huffmanForestPriorities items + (heap.push item.priority).elements := ih _
          _ = huffmanForestPriorities items + (item.priority ::ₘ heap.elements) := by
            rw [heap.elements_push]
          _ = item.priority ::ₘ (huffmanForestPriorities items + heap.elements) :=
            Multiset.add_cons _ _ _
          _ = (item.priority ::ₘ huffmanForestPriorities items) + heap.elements :=
            (Multiset.cons_add _ _ _).symm
          _ = huffmanForestPriorities (item :: items) + heap.elements := by
            simp [huffmanForestPriorities, Multiset.cons_coe]
  rw [huffmanHeapOfForest, general]
  simp [huffmanForestPriorities, MinHeap.elements, MinHeap.empty]

private theorem initialHuffmanForestFrom_serial_ge {α : Type u}
    (start : Nat) (input : List (α × Nat)) :
    ∀ item ∈ initialHuffmanForestFrom start input, start ≤ item.priority.serial := by
  induction input generalizing start with
  | nil => simp [initialHuffmanForestFrom]
  | cons pair input ih =>
      rcases pair with ⟨symbol, weight⟩
      intro item hitem
      simp only [initialHuffmanForestFrom, List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · simp
      · exact (Nat.le_succ start).trans (ih (start + 1) item hitem)

private theorem initialHuffmanForestFrom_length {α : Type u} (start : Nat)
    (input : List (α × Nat)) :
    (initialHuffmanForestFrom start input).length = input.length := by
  induction input generalizing start with
  | nil => rfl
  | cons _ _ ih =>
      simp only [initialHuffmanForestFrom, List.length_cons]
      rw [ih (start + 1)]

private theorem initialHuffmanForestFrom_serial_lt {α : Type u}
    (start : Nat) (input : List (α × Nat)) :
    ∀ item ∈ initialHuffmanForestFrom start input,
      item.priority.serial < start + input.length := by
  induction input generalizing start with
  | nil => simp [initialHuffmanForestFrom]
  | cons pair input ih =>
      rcases pair with ⟨symbol, weight⟩
      intro item hitem
      simp only [initialHuffmanForestFrom, List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · simp
      · have := ih (start + 1) item hitem
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private theorem initialHuffmanForestFrom_serials_nodup {α : Type u}
    (start : Nat) (input : List (α × Nat)) :
    ((initialHuffmanForestFrom start input).map
      (fun item => item.priority.serial)).Nodup := by
  induction input generalizing start with
  | nil => simp [initialHuffmanForestFrom]
  | cons pair input ih =>
      rcases pair with ⟨symbol, weight⟩
      simp only [initialHuffmanForestFrom, List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨item, hitem, hserial⟩ := List.mem_map.mp hmem
        have hge := initialHuffmanForestFrom_serial_ge (α := α) (start + 1) input item hitem
        omega
      · exact ih (start + 1)

private theorem initialHuffmanForestFrom_weight_eq {α : Type u}
    (start : Nat) (input : List (α × Nat)) :
    ∀ item ∈ initialHuffmanForestFrom start input,
      item.priority.weight = item.tree.totalWeight := by
  induction input generalizing start with
  | nil => simp [initialHuffmanForestFrom]
  | cons pair input ih =>
      rcases pair with ⟨symbol, weight⟩
      intro item hitem
      simp only [initialHuffmanForestFrom, List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · rfl
      · exact ih (start + 1) item hitem

private theorem initialHuffmanForestFrom_get? {α : Type u}
    (start : Nat) (input : List (α × Nat)) :
    ∀ item ∈ initialHuffmanForestFrom start input,
      (initialHuffmanForestFrom start input)[item.priority.serial - start]? =
        some item := by
  induction input generalizing start with
  | nil => simp [initialHuffmanForestFrom]
  | cons pair input ih =>
      rcases pair with ⟨symbol, weight⟩
      intro item hitem
      simp only [initialHuffmanForestFrom, List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · simp [initialHuffmanForestFrom]
      · have hge : start + 1 ≤ item.priority.serial :=
          initialHuffmanForestFrom_serial_ge (start + 1) input item hitem
        have h := ih (start + 1) item hitem
        simp only [initialHuffmanForestFrom]
        rw [show item.priority.serial - start =
          (item.priority.serial - (start + 1)) + 1 by omega,
          List.getElem?_cons_succ]
        exact h

/-- Every initial leaf is stored in the initial table at its own serial. -/
private theorem initialHuffmanTable_stored {α : Type u} (input : List (α × Nat)) :
    ∀ item ∈ huffmanTableForest (initialHuffmanTable input),
      (initialHuffmanTable input)[item.priority.serial]? = some (some item) := by
  intro item hitem
  rw [huffmanTableForest_initial] at hitem
  have hget := initialHuffmanForestFrom_get? 0 input item hitem
  have h1 : (initialHuffmanTable input)[item.priority.serial]? =
      ((initialHuffmanForest input).map some)[item.priority.serial]? := by
    simp [initialHuffmanTable, List.getElem?_toArray]
  rw [h1, List.getElem?_map]
  simpa [initialHuffmanForest] using hget

private theorem initialHuffmanForest_weights {α : Type u}
    (input : List (α × Nat)) :
    huffmanForestWeights (initialHuffmanForest input) =
      (input.map (fun pair => (pair.2 : Real)) : Multiset Real) := by
  have aux : ∀ (start : Nat) (items : List (α × Nat)),
      huffmanForestWeights (initialHuffmanForestFrom start items) =
        (items.map (fun pair => (pair.2 : Real)) : Multiset Real) := by
    intro start items
    induction items generalizing start with
    | nil => simp [initialHuffmanForestFrom, huffmanForestWeights]
    | cons pair items ih =>
        rcases pair with ⟨symbol, weight⟩
        have h := congrArg (fun weights : Multiset Real => (weight : Real) ::ₘ weights)
          (ih (start + 1))
        simpa [initialHuffmanForestFrom, huffmanForestWeights,
          HuffmanTree.totalWeight, Multiset.cons_coe] using h
  exact aux 0 input

private theorem initialHuffmanForest_cost {α : Type u}
    (input : List (α × Nat)) :
    huffmanForestCost (initialHuffmanForest input) = 0 := by
  have aux : ∀ (start : Nat) (items : List (α × Nat)),
      huffmanForestCost (initialHuffmanForestFrom start items) = 0 := by
    intro start items
    induction items generalizing start with
    | nil => simp [initialHuffmanForestFrom, huffmanForestCost]
    | cons pair items ih =>
        rcases pair with ⟨symbol, weight⟩
        simpa [initialHuffmanForestFrom, huffmanForestCost,
          HuffmanTree.weightedPathLength] using ih (start + 1)
  exact aux 0 input

private theorem initialHuffmanLoopInvariant {α : Type u}
    (input : List (α × Nat)) :
    HuffmanLoopInvariant input.length
      (huffmanHeapOfForest (initialHuffmanForest input))
      (initialHuffmanTable input) := by
  refine {
    heap_eq := by rw [huffmanTableForest_initial]; exact huffmanHeapOfForest_elements _
    serials_nodup := ?_
    serial_lt := ?_
    weight_eq := ?_
    size_eq := ?_
    stored := initialHuffmanTable_stored input
  }
  · rw [huffmanTableForest_initial]
    exact initialHuffmanForestFrom_serials_nodup 0 input
  · intro item hitem
    rw [huffmanTableForest_initial] at hitem
    simpa using initialHuffmanForestFrom_serial_lt 0 input item hitem
  · intro item hitem
    rw [huffmanTableForest_initial] at hitem
    exact initialHuffmanForestFrom_weight_eq 0 input item hitem
  · simp [initialHuffmanTable, initialHuffmanForest, initialHuffmanForestFrom_length]

private theorem HuffmanLoopInvariant.afterMerge {α : Type u}
    {nextSerial : Nat} {heap : MinHeap HuffmanPriority}
    {remaining : Array (Option (HuffmanWorkItem α))}
    (hinvariant : HuffmanLoopInvariant nextSerial heap remaining)
    (firstPriority secondPriority : HuffmanPriority)
    (firstTree secondTree : HuffmanTree α)
    (hfirstWeight : firstPriority.weight = firstTree.totalWeight)
    (hsecondWeight : secondPriority.weight = secondTree.totalWeight) :
    let priority : HuffmanPriority :=
      ⟨firstPriority.weight + secondPriority.weight, nextSerial⟩
    let tree := HuffmanTree.fork firstTree secondTree
    HuffmanLoopInvariant (nextSerial + 1) (heap.push priority)
      (remaining.push (some ⟨priority, tree⟩)) := by
  dsimp
  refine {
    heap_eq := ?_
    serials_nodup := ?_
    serial_lt := ?_
    weight_eq := ?_
    size_eq := by rw [Array.size_push, hinvariant.size_eq]
    stored := ?_
  }
  · rw [huffmanTableForest_push_some, heap.elements_push, hinvariant.heap_eq]
    simp only [huffmanForestPriorities, List.map_append]
    exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _).symm
  · rw [huffmanTableForest_push_some, List.map_append]
    refine List.nodup_append.mpr ⟨hinvariant.serials_nodup, by simp, ?_⟩
    intro x hx y hy
    obtain ⟨item, hitem, hserial⟩ := List.mem_map.mp hx
    change item.priority.serial = x at hserial
    have hlt := hinvariant.serial_lt item hitem
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    change y = nextSerial at hy
    omega
  · intro item hitem
    rw [huffmanTableForest_push_some] at hitem
    simp only [List.mem_append, List.mem_singleton] at hitem
    rcases hitem with hitem | rfl
    · exact (hinvariant.serial_lt item hitem).trans (Nat.lt_succ_self _)
    · simp
  · intro item hitem
    rw [huffmanTableForest_push_some] at hitem
    simp only [List.mem_append, List.mem_singleton] at hitem
    rcases hitem with hitem | rfl
    · exact hinvariant.weight_eq item hitem
    · simp only [HuffmanTree.totalWeight]
      omega
  · intro item hitem
    rw [huffmanTableForest_push_some] at hitem
    simp only [List.mem_append, List.mem_singleton] at hitem
    rw [Array.getElem?_push]
    rcases hitem with hitem | rfl
    · have hstored := hinvariant.stored item hitem
      have hlt : item.priority.serial < remaining.size := by
        rw [hinvariant.size_eq]
        exact hinvariant.serial_lt item hitem
      simp [show item.priority.serial ≠ remaining.size from by omega, hstored]
    · simp [hinvariant.size_eq]

private theorem huffmanLoop_mergeTrace {α : Type u}
    {fuel nextSerial : Nat} {heap : MinHeap HuffmanPriority}
    {table : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (hinvariant : HuffmanLoopInvariant nextSerial heap table)
    (hloop : huffmanLoop fuel nextSerial heap table = some tree) :
    ∃ mergeCost : Real,
      HuffmanWeightTree.MergeTrace
        (huffmanForestWeights (huffmanTableForest table)) mergeCost ∧
      (tree.weightedPathLength : Real) =
        huffmanForestCost (huffmanTableForest table) + mergeCost := by
  induction fuel generalizing nextSerial heap table tree with
  | zero =>
      simp only [huffmanLoop] at hloop
      cases hextract : heap.extractMin with
      | none => simp [hextract] at hloop
      | some result =>
          rcases result with ⟨priority, restHeap⟩
          simp only [hextract] at hloop
          cases htake : takeSerial? priority.serial table with
          | none => simp [htake] at hloop
          | some result =>
              rcases result with ⟨found, remaining⟩
              simp only [htake] at hloop
              cases hisEmpty : restHeap.data.isEmpty with
              | false => simp [hisEmpty] at hloop
              | true =>
                  cases hforestEmpty : (huffmanTableForest remaining).isEmpty with
                  | false => simp [hisEmpty, hforestEmpty] at hloop
                  | true =>
                      simp only [hisEmpty, hforestEmpty, Bool.true_and, ↓reduceIte,
                        Option.some.injEq] at hloop
                      subst tree
                      have hrem : huffmanTableForest remaining = [] :=
                        List.isEmpty_iff.mp hforestEmpty
                      have hpriorityMem : priority ∈ heap.elements := by
                        rw [← heap.extractMin_cons_elements hextract]
                        exact Multiset.mem_cons_self _ _
                      have hperm := hinvariant.takeSerial hpriorityMem rfl htake
                      rw [hrem] at hperm
                      have hweights := huffmanForestWeights_of_perm hperm
                      have hcost := huffmanForestCost_of_perm hperm
                      refine ⟨0, ?_, ?_⟩
                      · rw [← hweights]
                        simp [huffmanForestWeights,
                          HuffmanWeightTree.MergeTrace.singleton]
                      · rw [← hcost]
                        simp [huffmanForestCost]
  | succ fuel ih =>
      simp only [huffmanLoop] at hloop
      cases hchoice : extractTwoMin? heap with
      | none => simp [hchoice] at hloop
      | some choice =>
          simp only [hchoice] at hloop
          cases hfirst : takeSerial? choice.first.serial table with
          | none => simp [hfirst] at hloop
          | some firstResult =>
              rcases firstResult with ⟨firstTree, afterFirst⟩
              simp only [hfirst] at hloop
              cases hsecond : takeSerial? choice.second.serial afterFirst with
              | none => simp [hsecond] at hloop
              | some secondResult =>
                  rcases secondResult with ⟨secondTree, remaining⟩
                  simp only [hsecond] at hloop
                  let afterFirstHeap := choice.rest.push choice.second
                  have hpartitionFirst :
                      choice.first ::ₘ afterFirstHeap.elements = heap.elements := by
                    simp only [afterFirstHeap, choice.rest.elements_push]
                    exact extractTwoMin_cons_elements hchoice
                  have hinvariantFirst :=
                    hinvariant.afterTake hpartitionFirst hfirst
                  have hpartitionSecond :
                      choice.second ::ₘ choice.rest.elements = afterFirstHeap.elements := by
                    simp only [afterFirstHeap, choice.rest.elements_push]
                  have hinvariantSecond :=
                    hinvariantFirst.afterTake hpartitionSecond hsecond
                  have hfirstMem : choice.first ∈ heap.elements := by
                    rw [← extractTwoMin_cons_elements hchoice]
                    exact Multiset.mem_cons_self _ _
                  have hsecondMem : choice.second ∈ afterFirstHeap.elements := by
                    rw [← hpartitionSecond]
                    exact Multiset.mem_cons_self _ _
                  have hfirstPerm := hinvariant.takeSerial hfirstMem rfl hfirst
                  have hsecondPerm :=
                    hinvariantFirst.takeSerial hsecondMem rfl hsecond
                  have hfirstWeight := hinvariant.weight_eq
                    (⟨choice.first, firstTree⟩ : HuffmanWorkItem α)
                    (hfirstPerm.mem_iff.mp (by simp))
                  have hsecondWeight := hinvariantFirst.weight_eq
                    (⟨choice.second, secondTree⟩ : HuffmanWorkItem α)
                    (hsecondPerm.mem_iff.mp (by simp))
                  change choice.first.weight = firstTree.totalWeight at hfirstWeight
                  change choice.second.weight = secondTree.totalWeight at hsecondWeight
                  let mergedPriority : HuffmanPriority :=
                    ⟨choice.first.weight + choice.second.weight, nextSerial⟩
                  let mergedTree := HuffmanTree.fork firstTree secondTree
                  have hinvariantMerged : HuffmanLoopInvariant (nextSerial + 1)
                      (choice.rest.push mergedPriority)
                      (remaining.push (some ⟨mergedPriority, mergedTree⟩)) := by
                    exact hinvariantSecond.afterMerge choice.first choice.second
                      firstTree secondTree hfirstWeight hsecondWeight
                  obtain ⟨tailCost, htail, hcost⟩ :=
                    ih hinvariantMerged hloop
                  have hgreedy := extractTwoMin_greedy hchoice
                  have hfirstSecond : choice.first.weight ≤ choice.second.weight :=
                    priority_weight_le (hgreedy.1 choice.second (by
                      rw [← extractTwoMin_cons_elements hchoice]
                      exact Multiset.mem_cons.mpr
                        (Or.inr (Multiset.mem_cons_self _ _))))
                  have hsecondRemaining : ∀ item ∈ huffmanTableForest remaining,
                      choice.second.weight ≤ item.tree.totalWeight := by
                    intro item hitem
                    have hpriorityMem : item.priority ∈ choice.rest.elements := by
                      rw [hinvariantSecond.heap_eq]
                      simpa [huffmanForestPriorities] using
                        List.mem_map.mpr ⟨item, hitem, rfl⟩
                    have hle := hgreedy.2 item.priority
                      (Multiset.mem_cons.mpr (Or.inr hpriorityMem))
                    calc
                      choice.second.weight ≤ item.priority.weight := priority_weight_le hle
                      _ = item.tree.totalWeight :=
                        hinvariantSecond.weight_eq item hitem
                  have hbothPerm :
                      ((⟨choice.first, firstTree⟩ : HuffmanWorkItem α) ::
                        ⟨choice.second, secondTree⟩ ::
                          huffmanTableForest remaining).Perm
                        (huffmanTableForest table) :=
                    (List.Perm.cons _ hsecondPerm).trans hfirstPerm
                  refine ⟨(choice.first.weight : Real) + choice.second.weight + tailCost,
                    ?_, ?_⟩
                  · rw [← huffmanForestWeights_of_perm hbothPerm]
                    change HuffmanWeightTree.MergeTrace
                      ((firstTree.totalWeight : Real) ::ₘ
                        (secondTree.totalWeight : Real) ::ₘ
                          huffmanForestWeights (huffmanTableForest remaining))
                      ((choice.first.weight : Real) + choice.second.weight + tailCost)
                    rw [← hfirstWeight, ← hsecondWeight]
                    apply HuffmanWeightTree.MergeTrace.merge
                    · exact_mod_cast hfirstSecond
                    · intro weight hweight
                      simp only [huffmanForestWeights] at hweight
                      have hweightList :
                          weight ∈ (huffmanTableForest remaining).map
                            (fun item => (item.tree.totalWeight : Real)) := by
                        simpa using hweight
                      obtain ⟨item, hitem, hweightEq⟩ :=
                        List.mem_map.mp hweightList
                      rw [← hweightEq]
                      exact_mod_cast hsecondRemaining item hitem
                    · rw [huffmanTableForest_push_some] at htail
                      have hpermW : ((⟨mergedPriority, mergedTree⟩ :
                          HuffmanWorkItem α) ::
                            huffmanTableForest remaining).Perm
                          (huffmanTableForest remaining ++
                            [⟨mergedPriority, mergedTree⟩]) :=
                        (List.perm_append_singleton _ _).symm
                      rw [← huffmanForestWeights_of_perm hpermW] at htail
                      simpa [huffmanForestWeights, mergedTree,
                        HuffmanTree.totalWeight, hfirstWeight, hsecondWeight,
                        Nat.cast_add] using htail
                  · rw [← huffmanForestCost_of_perm hbothPerm, hcost]
                    simp only [huffmanTableForest_push_some, huffmanForestCost,
                      List.map_append, List.map_cons, List.map_nil, List.sum_append,
                      List.sum_cons, List.sum_nil, mergedTree,
                      HuffmanTree.weightedPathLength]
                    push_cast
                    rw [← hfirstWeight, ← hsecondWeight]
                    ring

/-- Under the loop invariant, a forest of `fuel + 1` trees always merges
down to a single tree: every heap extraction and serial lookup succeeds. -/
private theorem huffmanLoop_isSome {α : Type u} {fuel nextSerial : Nat}
    {heap : MinHeap HuffmanPriority} {table : Array (Option (HuffmanWorkItem α))}
    (hinvariant : HuffmanLoopInvariant nextSerial heap table)
    (hlen : (huffmanTableForest table).length = fuel + 1) :
    ∃ tree, huffmanLoop fuel nextSerial heap table = some tree := by
  induction fuel generalizing nextSerial heap table with
  | zero =>
      obtain ⟨item, hforest⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
      have hsize : heap.data.size = 1 := by
        have hcard : Multiset.card heap.elements = 1 := by
          rw [hinvariant.heap_eq, hforest]
          simp [huffmanForestPriorities]
        have hcard' : Multiset.card heap.elements = heap.data.size := by
          simp [MinHeap.elements]
        omega
      obtain ⟨priority, restHeap, hextract⟩ :
          ∃ p r, heap.extractMin = some (p, r) := by
        cases he : heap.extractMin with
        | none =>
            rw [MinHeap.extractMin_eq_none_iff] at he
            omega
        | some result =>
            obtain ⟨p, r⟩ := result
            exact ⟨p, r, rfl⟩
      have hpriority : priority = item.priority := by
        have hmem : priority ∈ heap.elements := heap.extractMin_mem hextract
        rw [hinvariant.heap_eq, hforest] at hmem
        simpa [huffmanForestPriorities] using hmem
      obtain ⟨remainingTable, htake⟩ := takeSerial?_isSome_of_stored
        (hinvariant.stored item (by rw [hforest]; exact List.mem_singleton_self item))
      rw [← hpriority] at htake
      obtain ⟨foundItem, -, -, hperm⟩ := takeSerial?_item htake
      rw [hforest] at hperm
      have hrem : huffmanTableForest remainingTable = [] :=
        List.length_eq_zero_iff.mp (by
          have hl := hperm.length_eq
          simp only [List.length_cons, List.length_nil] at hl
          omega)
      have hempty : restHeap.data.isEmpty = true := by
        have hcons := heap.extractMin_cons_elements hextract
        rw [hinvariant.heap_eq, hforest] at hcons
        have hzero : restHeap.elements = 0 := by
          have hcons' : priority ::ₘ restHeap.elements = item.priority ::ₘ 0 := by
            simpa [huffmanForestPriorities] using hcons
          rw [hpriority] at hcons'
          exact (Multiset.cons_inj_right _).mp hcons'
        have hsz : restHeap.data.size = 0 := by
          have hcard' : Multiset.card restHeap.elements = restHeap.data.size := by
            simp [MinHeap.elements]
          rw [hzero, Multiset.card_zero] at hcard'
          exact hcard'.symm
        change (restHeap.data.size == 0) = true
        simp [hsz]
      exact ⟨item.tree, by simp [huffmanLoop, hextract, htake, hempty, hrem]⟩
  | succ fuel ih =>
      have hsize : heap.data.size = (huffmanTableForest table).length := by
        have hcard : Multiset.card heap.elements =
            (huffmanTableForest table).length := by
          rw [hinvariant.heap_eq]
          simp [huffmanForestPriorities]
        have hcard' : Multiset.card heap.elements = heap.data.size := by
          simp [MinHeap.elements]
        omega
      obtain ⟨choice, hchoice⟩ : ∃ c, extractTwoMin? heap = some c := by
        cases h1 : heap.extractMin with
        | none =>
            rw [MinHeap.extractMin_eq_none_iff] at h1
            omega
        | some r1 =>
            obtain ⟨p1, rest1⟩ := r1
            have hcard1 : rest1.data.size = heap.data.size - 1 := by
              have hcons := heap.extractMin_cons_elements h1
              have hc1 : Multiset.card (p1 ::ₘ rest1.elements) =
                  Multiset.card heap.elements := by rw [hcons]
              simp only [Multiset.card_cons] at hc1
              have e1 : Multiset.card rest1.elements = rest1.data.size := by
                simp [MinHeap.elements]
              have e2 : Multiset.card heap.elements = heap.data.size := by
                simp [MinHeap.elements]
              omega
            cases h2 : rest1.extractMin with
            | none =>
                rw [MinHeap.extractMin_eq_none_iff] at h2
                omega
            | some r2 =>
                obtain ⟨p2, rest2⟩ := r2
                exact ⟨⟨p1, p2, rest2⟩, by simp [extractTwoMin?, h1, h2]⟩
      have hfirstMem : choice.first ∈ heap.elements := by
        rw [← extractTwoMin_cons_elements hchoice]
        exact Multiset.mem_cons_self _ _
      obtain ⟨firstTree, afterFirst, hfirst⟩ :
          ∃ tree afterFirst, takeSerial? choice.first.serial table =
            some (tree, afterFirst) := by
        rw [hinvariant.heap_eq] at hfirstMem
        obtain ⟨item, hitem, hpriority⟩ :
            ∃ item ∈ huffmanTableForest table, item.priority = choice.first := by
          have hmem := hfirstMem
          simp only [huffmanForestPriorities, Multiset.mem_coe,
            List.mem_map] at hmem
          exact hmem
        obtain ⟨afterFirst, htake⟩ :=
          takeSerial?_isSome_of_stored (hinvariant.stored item hitem)
        rw [hpriority] at htake
        exact ⟨item.tree, afterFirst, htake⟩
      have hpartitionFirst :
          choice.first ::ₘ (choice.rest.push choice.second).elements =
            heap.elements := by
        simp only [MinHeap.elements_push]
        exact extractTwoMin_cons_elements hchoice
      have hinvariantFirst := hinvariant.afterTake hpartitionFirst hfirst
      have hsecondMem :
          choice.second ∈ (choice.rest.push choice.second).elements := by
        rw [MinHeap.elements_push]
        exact Multiset.mem_cons_self _ _
      obtain ⟨secondTree, remaining, hsecond⟩ :
          ∃ tree remaining, takeSerial? choice.second.serial afterFirst =
            some (tree, remaining) := by
        rw [hinvariantFirst.heap_eq] at hsecondMem
        obtain ⟨item, hitem, hpriority⟩ :
            ∃ item ∈ huffmanTableForest afterFirst,
              item.priority = choice.second := by
          have hmem := hsecondMem
          simp only [huffmanForestPriorities, Multiset.mem_coe,
            List.mem_map] at hmem
          exact hmem
        obtain ⟨remaining, htake⟩ :=
          takeSerial?_isSome_of_stored (hinvariantFirst.stored item hitem)
        rw [hpriority] at htake
        exact ⟨item.tree, remaining, htake⟩
      have hpartitionSecond :
          choice.second ::ₘ choice.rest.elements =
            (choice.rest.push choice.second).elements := by
        simp only [MinHeap.elements_push]
      have hinvariantSecond := hinvariantFirst.afterTake hpartitionSecond hsecond
      have hfirstWeight : choice.first.weight = firstTree.totalWeight := by
        have hperm := hinvariant.takeSerial hfirstMem rfl hfirst
        exact hinvariant.weight_eq (⟨choice.first, firstTree⟩ : HuffmanWorkItem α)
          (hperm.mem_iff.mp (by simp))
      have hsecondWeight : choice.second.weight = secondTree.totalWeight := by
        have hperm := hinvariantFirst.takeSerial hsecondMem rfl hsecond
        exact hinvariantFirst.weight_eq
          (⟨choice.second, secondTree⟩ : HuffmanWorkItem α)
          (hperm.mem_iff.mp (by simp))
      have hinvariantMerged := hinvariantSecond.afterMerge choice.first
        choice.second firstTree secondTree hfirstWeight hsecondWeight
      have hlenMerged :
          (huffmanTableForest (remaining.push
            (some ⟨⟨choice.first.weight + choice.second.weight, nextSerial⟩,
              HuffmanTree.fork firstTree secondTree⟩))).length = fuel + 1 := by
        rw [huffmanTableForest_push_some, List.length_append]
        have hperm1 := hinvariant.takeSerial hfirstMem rfl hfirst
        have hperm2 := hinvariantFirst.takeSerial hsecondMem rfl hsecond
        have hl1 := hperm1.length_eq
        have hl2 := hperm2.length_eq
        simp only [List.length_cons, List.length_nil] at hl1 hl2 ⊢
        omega
      obtain ⟨tree, hrec⟩ := ih hinvariantMerged hlenMerged
      refine ⟨tree, ?_⟩
      simp only [huffmanLoop, hchoice, hfirst, hsecond]
      exact hrec

/-- A successful executable run supplies the standard two-minimum merge
certificate for its weighted path length. -/
theorem huffman_mergeTrace {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree : HuffmanTree α}
    (hresult : huffman input = some tree) :
    HuffmanWeightTree.MergeTrace
      (input.map (fun pair => (pair.2 : Real)) : Multiset Real)
      tree.weightedPathLength := by
  unfold huffman at hresult
  split at hresult
  · contradiction
  · obtain ⟨mergeCost, htrace, hcost⟩ :=
      huffmanLoop_mergeTrace (initialHuffmanLoopInvariant input) hresult
    rw [huffmanTableForest_initial] at htrace hcost
    rw [initialHuffmanForest_weights] at htrace
    rw [initialHuffmanForest_cost, zero_add] at hcost
    rw [hcost]
    exact htrace

/-- The constructor succeeds on every nonempty duplicate-free input. -/
theorem huffman_isSome {α : Type u} [DecidableEq α] {input : List (α × Nat)}
    (hne : input ≠ []) (hnd : (input.map Prod.fst).Nodup) :
    (huffman input).isSome := by
  have hforest : (huffmanTableForest (initialHuffmanTable input)).length =
      input.length := by
    rw [huffmanTableForest_initial]
    exact initialHuffmanForestFrom_length 0 input
  have hlen : (huffmanTableForest (initialHuffmanTable input)).length =
      input.length - 1 + 1 := by
    have hpos : 0 < input.length :=
      Nat.pos_of_ne_zero (fun hz => hne (List.length_eq_zero_iff.mp hz))
    omega
  obtain ⟨tree, htree⟩ := huffmanLoop_isSome
    (initialHuffmanLoopInvariant input) hlen
  have hresult : huffman input = some tree := by
    unfold huffman
    rw [show (input.isEmpty || !(input.map Prod.fst).Nodup) = false by
      simp [hne, hnd]]
    exact htree
  rw [hresult]
  rfl

/-- The constructor rejects exactly the empty inputs and the inputs with a
repeated symbol. -/
theorem huffman_eq_none_iff {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} :
    huffman input = none ↔ input = [] ∨ ¬(input.map Prod.fst).Nodup := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hne, hnd⟩ := hc
    have hsome := huffman_isSome hne hnd
    rw [h] at hsome
    simp at hsome
  · rintro (rfl | hnd)
    · simp [huffman]
    · have hc : (input.isEmpty || !(input.map Prod.fst).Nodup) = true := by
        simp [hnd]
      simp [huffman, hc]

/-- A competitor is a full prefix-code tree with exactly the same weighted
symbols as the input.  Full binary structure is intrinsic to `HuffmanTree`. -/
def HuffmanTree.Admissible {α : Type u} (tree : HuffmanTree α)
    (input : List (α × Nat)) : Prop :=
  tree.weightedLeaves.Perm input

/-- The global optimality result once the executable heap loop has been related
to its two-minimum merge trace. -/
theorem huffman_optimal_of_mergeTrace {α : Type u}
    {input : List (α × Nat)} {tree competitor : HuffmanTree α}
    (htrace : HuffmanWeightTree.MergeTrace
      (input.map (fun pair => (pair.2 : Real)) : Multiset Real)
      tree.weightedPathLength)
    (hcompetitor : competitor.Admissible input) :
    tree.weightedPathLength ≤ competitor.weightedPathLength := by
  have hpermuted := hcompetitor.map (fun pair => (pair.2 : Real))
  have hweights : competitor.eraseSymbols.weights =
      (input.map (fun pair => (pair.2 : Real)) : Multiset Real) := by
    rw [competitor.eraseSymbols_weights]
    exact Multiset.coe_eq_coe.mpr hpermuted
  have hbound := htrace.le_pathCost competitor.eraseSymbols hweights
  rw [competitor.eraseSymbols_pathCost] at hbound
  exact_mod_cast hbound

/-- The tree returned by `huffman` globally minimizes weighted path length
among full prefix-code trees with exactly the input's weighted symbols. -/
theorem huffman_optimal {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree competitor : HuffmanTree α}
    (hresult : huffman input = some tree)
    (hcompetitor : competitor.Admissible input) :
    tree.weightedPathLength ≤ competitor.weightedPathLength :=
  huffman_optimal_of_mergeTrace (huffman_mergeTrace hresult) hcompetitor

/-- The tree returned by `huffman` also minimizes the structural
encoded-length objective, including the one-bit singleton code; by
`HuffmanTree.encodedLength_eq_sum_codeLengths` this is the encoder's emitted
cost whenever the leaf symbols are unique. -/
theorem huffman_encodedLength_optimal {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree competitor : HuffmanTree α}
    (hresult : huffman input = some tree)
    (hcompetitor : competitor.Admissible input) :
    tree.encodedLength ≤ competitor.encodedLength := by
  have htree : tree.weightedLeaves.Perm input :=
    huffman_weightedLeaves_perm hresult
  have hperm : tree.weightedLeaves.Perm competitor.weightedLeaves :=
    htree.trans hcompetitor.symm
  have hlength : tree.weightedLeaves.length = competitor.weightedLeaves.length :=
    hperm.length_eq
  have hpos : ∀ t : HuffmanTree α, 0 < t.weightedLeaves.length := by
    intro t
    induction t with
    | leaf _ _ => simp [HuffmanTree.weightedLeaves]
    | fork _ _ ihl ihr => simp [HuffmanTree.weightedLeaves, List.length_append]; omega
  cases competitor with
  | leaf symbol weight =>
      have hone : tree.weightedLeaves.length = 1 := by
        rw [hlength]; rfl
      cases tree with
      | leaf s w =>
          have hweight : w = weight := by
            have h := hperm
            simp only [HuffmanTree.weightedLeaves, List.perm_singleton] at h
            injection h with hp _
            exact congrArg Prod.snd hp
          simp [HuffmanTree.encodedLength, hweight]
      | fork l r =>
          have hge : 2 ≤ (HuffmanTree.fork l r).weightedLeaves.length := by
            have hl := hpos l
            have hr := hpos r
            simp only [HuffmanTree.weightedLeaves, List.length_append] at hl hr ⊢
            omega
          omega
  | fork l r =>
      rw [HuffmanTree.encodedLength_fork]
      have hge : 2 ≤ (HuffmanTree.fork l r).weightedLeaves.length := by
        have hl := hpos l
        have hr := hpos r
        simp only [HuffmanTree.weightedLeaves, List.length_append] at hl hr ⊢
        omega
      cases tree with
      | leaf s w =>
          have hone : (HuffmanTree.leaf s w).weightedLeaves.length = 1 := rfl
          omega
      | fork tl tr =>
          rw [HuffmanTree.encodedLength_fork]
          exact huffman_optimal hresult hcompetitor

end Cslib.Algorithms.Lean
