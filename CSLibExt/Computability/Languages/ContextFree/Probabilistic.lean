/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.CYK
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Probabilistic context-free grammars: the inside recurrence

For a fixed finite grammar with bounded derivation depth, normalized rule
choices and the inside recurrence as a sum of derivation weights (Collins,
"The Inside-Outside Algorithm", Section 3), plus the Chi-Geman tightness
counterexample (Chi and Geman, 1998, p. 300).

A PCFG is a context-free grammar with rule weights `q r >= 0` normalized per
nonterminal: the weights of the rules with input `A` sum to `1` (the source's
`psi(r) = q(r)`). Mathlib's `Derives` is `Prop`-valued, so derivation weights
need a derivation-tree datatype: `PDerivTree` has one leaf per terminal rule
and one binary node per binary rule. `inside d A w` is the CYK-shaped sum
recurrence, and it equals the sum of weights of valid trees of depth at most
`d` with yield `w` rooted at `A`. A CNF tree for a word of length `m` has depth
at most `m`, so depth `d >= |w|` already sums every derivation of `w`.
Grammar termination and total mass over unbounded strings need a separate
consistency theorem, which is not claimed here.

The same file carries the Chi-Geman counterexample: the one-nonterminal
grammar `A -> A A` (weight `p = 2 / 3`) and `A -> a` (`q = 1 / 3`) is
normalized per nonterminal, yet the total weight `S h` of finite trees of
depth at most `h` stays below `1 / 2` for all `h`, so the infinite-derivation
event has weight at least `1 / 2`.

## Main definitions

* `Cslib.Language.PDerivTree`: derivation trees (leaves and binary nodes).
* `Cslib.Language.IsRuleWeight`, `Cslib.Language.IsNormalized`: rule-weight
  nonnegativity and per-nonterminal normalization.
* `Cslib.Language.inside`: the inside recurrence (CYK-shaped sum).
* `Cslib.Language.treesUpTo`: the finite set of valid trees of depth at most
  `d` with yield `w` rooted at `A`.
* `Cslib.Language.chiGemanS`: the Chi-Geman total-weight sequence.

## Main results

* `Cslib.Language.inside_eq_treeSum`: the inside recurrence equals the sum
  of derivation weights.
* `Cslib.Language.mem_treesUpTo_iff`: membership unfolds to validity,
  depth, yield and root.
* `Cslib.Language.inside_stable`: depth `d >= |w|` sums every derivation.
* `Cslib.Language.chiGeman_main_half`: the Chi-Geman bound `S h <= 1 / 2`.
-/

@[expose] public section

namespace Cslib.Language

/-- Derivation trees for binary/terminal rules: a leaf records a terminal
rule `A -> a`, a node records a binary rule `A -> B C` with subtrees. -/
inductive PDerivTree (NT T : Type*) where
  | leaf : NT → T → PDerivTree NT T
  | node : NT → NT → NT → PDerivTree NT T → PDerivTree NT T → PDerivTree NT T
deriving DecidableEq

/-- The root nonterminal of a derivation tree. -/
def PDerivTree.rootOf {NT T : Type*} (t : PDerivTree NT T) : NT :=
  match t with
  | .leaf A _ => A
  | .node A _ _ _ _ => A

/-- The word a derivation tree yields. -/
def PDerivTree.yieldOf {NT T : Type*} (t : PDerivTree NT T) : List T :=
  match t with
  | .leaf _ a => [a]
  | .node _ _ _ l r => l.yieldOf ++ r.yieldOf

/-- The depth of a derivation tree: leaves have depth one. -/
def PDerivTree.depthOf {NT T : Type*} (t : PDerivTree NT T) : ℕ :=
  match t with
  | .leaf _ _ => 1
  | .node _ _ _ l r => 1 + max l.depthOf r.depthOf

/-- The weight of a derivation tree: the product of its rule weights. -/
def PDerivTree.weightOf {NT T : Type*} (q : ContextFreeRule T NT → ℝ) (t : PDerivTree NT T) :
    ℝ :=
  match t with
  | .leaf A a => q ⟨A, [Symbol.terminal a]⟩
  | .node A B C l r =>
      q ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ *
        l.weightOf q * r.weightOf q

/-- Every derivation tree yields a nonempty word. -/
theorem PDerivTree.yieldOf_ne_nil {NT T : Type*} (t : PDerivTree NT T) : t.yieldOf ≠ [] := by
  induction t with
  | leaf _ _ => simp [PDerivTree.yieldOf]
  | node _ _ _ l r ihl _ =>
      simp only [PDerivTree.yieldOf, Ne, List.append_eq_nil_iff,
        not_and_or]
      exact Or.inl ihl

/-- A derivation tree is no deeper than its yield is long. -/
theorem PDerivTree.depthOf_le_length {NT T : Type*} (t : PDerivTree NT T) :
    t.depthOf ≤ t.yieldOf.length := by
  induction t with
  | leaf _ _ => rfl
  | node _ _ _ l r ihl ihr =>
      have h1 : 0 < l.yieldOf.length :=
        List.length_pos_iff.mpr l.yieldOf_ne_nil
      have h2 : 0 < r.yieldOf.length :=
        List.length_pos_iff.mpr r.yieldOf_ne_nil
      simp only [PDerivTree.depthOf, PDerivTree.yieldOf, List.length_append]
      omega

/-- Rule weights are nonnegative on the rules of `g`. -/
def IsRuleWeight (T : Type*) (g : ContextFreeGrammar T)
    (q : ContextFreeRule T g.NT → ℝ) : Prop :=
  ∀ r ∈ g.rules, 0 ≤ q r

/-- A PCFG is normalized when weights are nonnegative and sum to one per
nonterminal (Chi and Geman, Eq. (1)). -/
def IsNormalized (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ) : Prop :=
  IsRuleWeight T g q ∧
    ∀ A : g.NT, ∑ r ∈ g.rules.filter (fun r => r.input = A), q r = 1

/-- The binary rule bodies with input `A`, as nonterminal pairs. -/
def binRules (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (A : g.NT) : Finset (g.NT × g.NT) :=
  (g.rules.filter (fun r => r.input = A)).biUnion fun r =>
    match r.output with
    | [Symbol.nonterminal B, Symbol.nonterminal C] => {(B, C)}
    | _ => ∅

/-- The leaf trees contributing to `inside`: at most the tree for `A -> a`
when `w = [a]`. -/
def leafTrees (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (A : g.NT) (w : List T) :
    Finset (PDerivTree g.NT T) :=
  match w with
  | [a] =>
      if ⟨A, [Symbol.terminal a]⟩ ∈ g.rules then {PDerivTree.leaf A a}
      else ∅
  | _ => ∅

/-- The leaf summand of the inside recurrence. -/
def leafWeight (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ) (A : g.NT)
    (w : List T) : ℝ :=
  match w with
  | [a] =>
      if ⟨A, [Symbol.terminal a]⟩ ∈ g.rules then
        q ⟨A, [Symbol.terminal a]⟩
      else 0
  | _ => 0

/-- The inside recurrence (CYK-shaped sum): terminal rules plus, for each
binary rule body and each split of `w` into nonempty parts, the rule weight
times the inside values of the parts. -/
def inside (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ) : ℕ → g.NT →
    List T → ℝ
  | 0, _, _ => 0
  | d + 1, A, w =>
      leafWeight T g q A w +
        ∑ p ∈ binRules T g A, ∑ k ∈ Finset.range (w.length + 1),
          if w.take k = [] ∨ w.drop k = [] then 0
          else
            q ⟨A, [Symbol.nonterminal p.1, Symbol.nonterminal p.2]⟩ *
              inside T g q d p.1 (w.take k) *
                inside T g q d p.2 (w.drop k)

/-- Unfolding `inside` at successor depth. -/
theorem inside_succ (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ) (d : ℕ) (A : g.NT)
    (w : List T) :
    inside T g q (d + 1) A w = leafWeight T g q A w +
      ∑ p ∈ binRules T g A, ∑ k ∈ Finset.range (w.length + 1),
        (if w.take k = [] ∨ w.drop k = [] then 0
        else
          q ⟨A, [Symbol.nonterminal p.1, Symbol.nonterminal p.2]⟩ *
            inside T g q d p.1 (w.take k) *
            inside T g q d p.2 (w.drop k)) := rfl

/-- The trees built from one binary rule body at one split position, from
explicit left and right subtree sets. -/
def splitTreeAt (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (A B C : g.NT) (w : List T) (k : ℕ)
    (L R : Finset (PDerivTree g.NT T)) : Finset (PDerivTree g.NT T) :=
  if w.take k = [] ∨ w.drop k = [] then ∅
  else
    (L ×ˢ R).image fun p => PDerivTree.node A B C p.1 p.2

/-- Valid trees of depth at most `d` with yield `w` rooted at `A`. -/
def treesUpTo (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] : ℕ → g.NT → List T → Finset (PDerivTree g.NT T)
  | 0, _, _ => ∅
  | d + 1, A, w =>
      leafTrees T g A w ∪
        (binRules T g A).biUnion fun p =>
          (Finset.range (w.length + 1)).biUnion fun k =>
            splitTreeAt T g A p.1 p.2 w k
              (treesUpTo T g d p.1 (w.take k))
              (treesUpTo T g d p.2 (w.drop k))

/-- The trees built from one binary rule body and one split position. -/
def splitTrees (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (d : ℕ) (A B C : g.NT) (w : List T) :
    Finset (PDerivTree g.NT T) :=
  (Finset.range (w.length + 1)).biUnion fun k =>
    splitTreeAt T g A B C w k (treesUpTo T g d B (w.take k))
      (treesUpTo T g d C (w.drop k))

/-- The binary trees contributing to `inside`: over rule bodies and splits. -/
def branchTrees (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T) :
    Finset (PDerivTree g.NT T) :=
  (binRules T g A).biUnion fun p => splitTrees T g d A p.1 p.2 w

/-- The bounded-depth sum of derivation weights. -/
def treeSum (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ) (d : ℕ) (A : g.NT)
    (w : List T) : ℝ :=
  ∑ t ∈ treesUpTo T g d A w, t.weightOf q

/-- Validity of a derivation tree against the rules of `g`. -/
def IsValidTree (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] : PDerivTree g.NT T → Prop
  | .leaf A a => ⟨A, [Symbol.terminal a]⟩ ∈ g.rules
  | .node A B C l r =>
      ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ ∈ g.rules ∧
        l.rootOf = B ∧ r.rootOf = C ∧ IsValidTree T g l ∧ IsValidTree T g r

/-- Reading a rule back out of `binRules` membership. -/
theorem mem_binRules_iff (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (A : g.NT) (B C : g.NT) :
    (B, C) ∈ binRules T g A ↔
      ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ ∈ g.rules := by
  constructor
  · intro h
    rw [binRules, Finset.mem_biUnion] at h
    obtain ⟨r, hr, hmem⟩ := h
    rw [Finset.mem_filter] at hr
    have hmem' : (B, C) ∈ match r.output with
        | [Symbol.nonterminal B', Symbol.nonterminal C'] => {(B', C')}
        | _ => ∅ := hmem
    obtain ⟨input, output⟩ := r
    cases output with
    | nil =>
        dsimp only at hmem'
        exact absurd hmem' (Finset.notMem_empty _)
    | cons s rest =>
        cases s with
        | terminal _ =>
            dsimp only at hmem'
            exact absurd hmem' (Finset.notMem_empty _)
        | nonterminal B' =>
            cases rest with
            | nil =>
                dsimp only at hmem'
                exact absurd hmem' (Finset.notMem_empty _)
            | cons s₂ rest₂ =>
                cases s₂ with
                | terminal _ =>
                    dsimp only at hmem'
                    exact absurd hmem' (Finset.notMem_empty _)
                | nonterminal C' =>
                    cases rest₂ with
                    | nil =>
                        dsimp only at hmem'
                        rw [Finset.mem_singleton] at hmem'
                        have hB : B = B' := congrArg Prod.fst hmem'
                        have hC : C = C' := congrArg Prod.snd hmem'
                        subst hB
                        subst hC
                        have hrIn : input = A := hr.2
                        rw [← hrIn]
                        exact hr.1
                    | cons _ _ =>
                        dsimp only at hmem'
                        exact absurd hmem' (Finset.notMem_empty _)
  · intro h
    rw [binRules, Finset.mem_biUnion]
    refine ⟨⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨h, rfl⟩
    · exact Finset.mem_singleton_self _

/-- Inverting membership in `branchTrees`: the rule body, the split and the
subtrees. -/
theorem mem_branchTrees_iff (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T)
    (t : PDerivTree g.NT T) :
    t ∈ branchTrees T g d A w ↔
      ∃ B C k l r, ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ ∈
        g.rules ∧ k ∈ Finset.range (w.length + 1) ∧ w.take k ≠ [] ∧
        w.drop k ≠ [] ∧ l ∈ treesUpTo T g d B (w.take k) ∧
        r ∈ treesUpTo T g d C (w.drop k) ∧
        t = PDerivTree.node A B C l r := by
  constructor
  · intro h
    rw [branchTrees, Finset.mem_biUnion] at h
    obtain ⟨⟨B, C⟩, hBC, hsplit⟩ := h
    rw [mem_binRules_iff] at hBC
    rw [splitTrees, Finset.mem_biUnion] at hsplit
    obtain ⟨k, hk, hmem⟩ := hsplit
    by_cases hempty : w.take k = [] ∨ w.drop k = []
    · rcases hempty with h | h <;> simp [h, splitTreeAt] at hmem
    · push Not at hempty
      simp only [splitTreeAt, hempty.1, hempty.2, or_self, ite_false] at hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨l, r⟩, hprod, rfl⟩ := hmem
      rw [Finset.mem_product] at hprod
      exact ⟨B, C, k, l, r, hBC, hk, hempty.1, hempty.2, hprod.1, hprod.2,
        rfl⟩
  · rintro ⟨B, C, k, l, r, hBC, hk, hne1, hne2, hl, hr, rfl⟩
    rw [branchTrees, Finset.mem_biUnion]
    refine ⟨⟨B, C⟩, mem_binRules_iff T g A B C |>.mpr hBC, ?_⟩
    rw [splitTrees, Finset.mem_biUnion]
    refine ⟨k, hk, ?_⟩
    simp only [splitTreeAt, hne1, hne2, or_self, ite_false]
    rw [Finset.mem_image]
    exact ⟨⟨l, r⟩, Finset.mem_product.mpr ⟨hl, hr⟩, rfl⟩

/-- Unfolding `treesUpTo` at depth zero. -/
theorem treesUpTo_zero (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (A : g.NT) (w : List T) :
    treesUpTo T g 0 A w = ∅ := rfl

/-- Unfolding `treesUpTo` at successor depth. -/
theorem treesUpTo_succ (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T) :
    treesUpTo T g (d + 1) A w =
      leafTrees T g A w ∪ branchTrees T g d A w := rfl

/-- Unfolding `leafTrees` on the empty word. -/
theorem leafTrees_nil (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (A : g.NT) :
    leafTrees T g A [] = ∅ := rfl

/-- Unfolding `leafTrees` on a singleton word. -/
theorem leafTrees_singleton (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (A : g.NT) (a : T) :
    leafTrees T g A [a] =
      if ⟨A, [Symbol.terminal a]⟩ ∈ g.rules then {PDerivTree.leaf A a}
      else ∅ := rfl

/-- Unfolding `leafTrees` on a word of length at least two. -/
theorem leafTrees_cons_cons (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (A : g.NT) (a b : T)
    (rest : List T) : leafTrees T g A (a :: b :: rest) = ∅ := rfl

/-- Unfolding `inside` at depth zero. -/
theorem inside_zero (T : Type*) (g : ContextFreeGrammar T) [DecidableEq T]
    [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ) (A : g.NT)
    (w : List T) : inside T g q 0 A w = 0 := rfl

/-- Membership in `treesUpTo` unfolds to validity, depth, yield and root. -/
theorem mem_treesUpTo_iff (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T)
    (t : PDerivTree g.NT T) :
    t ∈ treesUpTo T g d A w ↔
      IsValidTree T g t ∧ t.depthOf ≤ d ∧ t.yieldOf = w ∧ t.rootOf = A := by
  induction d generalizing A w t with
  | zero =>
      rw [treesUpTo_zero T g A w]
      simp only [Finset.notMem_empty, false_iff]
      intro h
      obtain ⟨-, hd, -, -⟩ := h
      have h1 : 1 ≤ t.depthOf := by
        cases t with
        | leaf _ _ => exact Nat.le_refl 1
        | node _ _ _ _ _ => exact Nat.le_add_right 1 _
      omega
  | succ d ih =>
      constructor
      · intro h
        have hU : t ∈ leafTrees T g A w ∨ t ∈ branchTrees T g d A w := by
          rw [treesUpTo_succ T g d A w] at h
          exact Finset.mem_union.mp h
        rcases hU with hleaf | hbranch
        · cases w with
          | nil =>
              rw [leafTrees_nil] at hleaf
              exact absurd hleaf (Finset.notMem_empty _)
          | cons a rest =>
              cases rest with
              | nil =>
                  rw [leafTrees_singleton] at hleaf
                  by_cases hR : ⟨A, [Symbol.terminal a]⟩ ∈ g.rules
                  · simp only [hR, ite_true, Finset.mem_singleton] at hleaf
                    subst hleaf
                    refine ⟨hR, ?_, rfl, rfl⟩
                    simp only [PDerivTree.depthOf]
                    omega
                  · simp only [hR, ite_false] at hleaf
                    exact absurd hleaf (Finset.notMem_empty _)
              | cons b rest =>
                  rw [leafTrees_cons_cons] at hleaf
                  exact absurd hleaf (Finset.notMem_empty _)
        · rw [mem_branchTrees_iff T g d A w t] at hbranch
          obtain ⟨B, C, k, l, r, hBC, -, hne1, hne2, hl, hr, rfl⟩ := hbranch
          obtain ⟨hVl, hdl, hyl, hrl⟩ := (ih _ _ _).mp hl
          obtain ⟨hVr, hdr, hyr, hrr⟩ := (ih _ _ _).mp hr
          refine ⟨⟨hBC, hrl, hrr, hVl, hVr⟩, ?_, ?_, rfl⟩
          · simp only [PDerivTree.depthOf]
            have hmax : max l.depthOf r.depthOf ≤ d :=
              Nat.max_le.mpr ⟨hdl, hdr⟩
            omega
          · simp only [PDerivTree.yieldOf, hyl, hyr]
            exact List.take_append_drop k w
      · rintro ⟨hV, hd, hy, hroot⟩
        rw [treesUpTo_succ T g d A w, Finset.mem_union]
        cases t with
        | leaf A' a =>
            refine Or.inl ?_
            simp only [PDerivTree.yieldOf] at hy
            simp only [PDerivTree.rootOf] at hroot
            subst hy
            have hroot' : A = A' := hroot.symm
            subst hroot'
            have hV' : ⟨A, [Symbol.terminal a]⟩ ∈ g.rules := hV
            rw [leafTrees_singleton, ite_eq_left hV', Finset.mem_singleton]
        | node A' B C l r =>
            refine Or.inr ?_
            simp only [PDerivTree.yieldOf] at hy
            simp only [PDerivTree.rootOf] at hroot
            simp only [PDerivTree.depthOf] at hd
            obtain ⟨hBC, hBl, hCr, hVl, hVr⟩ := hV
            have hroot' : A = A' := hroot.symm
            subst hroot'
            rw [mem_branchTrees_iff T g d A w (PDerivTree.node A B C l r)]
            have htake : w.take l.yieldOf.length = l.yieldOf := by
              conv_lhs => rw [← hy]
              exact List.take_left
            have hdrop : w.drop l.yieldOf.length = r.yieldOf := by
              conv_lhs => rw [← hy]
              exact List.drop_left
            have hmax : max l.depthOf r.depthOf ≤ d := by omega
            have hdl : l.depthOf ≤ d := (Nat.max_le.mp hmax).1
            have hdr : r.depthOf ≤ d := (Nat.max_le.mp hmax).2
            have hlen : (l.yieldOf ++ r.yieldOf).length = w.length := by
              rw [hy]
            refine ⟨B, C, l.yieldOf.length, l, r, hBC, ?_, ?_, ?_, ?_, ?_,
              rfl⟩
            · rw [Finset.mem_range]
              have hle : l.yieldOf.length ≤ w.length := by
                rw [← hlen, List.length_append]
                exact Nat.le_add_right _ _
              omega
            · rw [htake]
              exact l.yieldOf_ne_nil
            · rw [hdrop]
              exact r.yieldOf_ne_nil
            · rw [htake]
              exact (ih _ _ _).mpr ⟨hVl, hdl, rfl, hBl⟩
            · rw [hdrop]
              exact (ih _ _ _).mpr ⟨hVr, hdr, rfl, hCr⟩

/-- The leaf summand equals the leaf tree sum. -/
theorem leafWeight_eq_sum (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ)
    (A : g.NT) (w : List T) :
    leafWeight T g q A w =
      ∑ t ∈ leafTrees T g A w, t.weightOf q := by
  cases w with
  | nil =>
      have hW : leafWeight T g q A [] = 0 := by simp [leafWeight]
      rw [leafTrees_nil, hW, Finset.sum_empty]
  | cons a rest =>
      cases rest with
      | nil =>
          by_cases hR : ⟨A, [Symbol.terminal a]⟩ ∈ g.rules
          · have hW : leafWeight T g q A [a] =
                q ⟨A, [Symbol.terminal a]⟩ := by simp [leafWeight, hR]
            have hT : leafTrees T g A [a] = {PDerivTree.leaf A a} := by
              simp [leafTrees_singleton, hR]
            rw [hW, hT, Finset.sum_singleton, PDerivTree.weightOf]
          · have hW : leafWeight T g q A [a] = 0 := by
              simp [leafWeight, hR]
            have hT : leafTrees T g A [a] = ∅ := by
              simp [leafTrees_singleton, hR]
            rw [hW, hT, Finset.sum_empty]
      | cons b rest =>
          have hW : leafWeight T g q A (a :: b :: rest) = 0 := by
            simp [leafWeight]
          rw [leafTrees_cons_cons T g A a b rest, hW, Finset.sum_empty]

/-- Every tree in `splitTrees` is a node with the given labels. -/
theorem mem_splitTrees_node (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A B C : g.NT) (w : List T)
    (t : PDerivTree g.NT T) (ht : t ∈ splitTrees T g d A B C w) :
    ∃ l r, t = PDerivTree.node A B C l r := by
  rw [splitTrees, Finset.mem_biUnion] at ht
  obtain ⟨k, -, hmem⟩ := ht
  simp only [splitTreeAt] at hmem
  by_cases h : w.take k = [] ∨ w.drop k = []
  · simp only [h, ite_true, Finset.notMem_empty] at hmem
  · simp only [h, ite_false, Finset.mem_image] at hmem
    obtain ⟨⟨l, r⟩, -, rfl⟩ := hmem
    exact ⟨l, r, rfl⟩

/-- Splits at different positions give disjoint tree sets. -/
theorem splitTreeAt_disjoint (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A B C : g.NT) (w : List T)
    (k₁ k₂ : ℕ) (h₁ : k₁ ∈ Finset.range (w.length + 1))
    (h₂ : k₂ ∈ Finset.range (w.length + 1)) (hne : k₁ ≠ k₂) :
    Disjoint
      (splitTreeAt T g A B C w k₁ (treesUpTo T g d B (w.take k₁))
        (treesUpTo T g d C (w.drop k₁)))
      (splitTreeAt T g A B C w k₂ (treesUpTo T g d B (w.take k₂))
        (treesUpTo T g d C (w.drop k₂))) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  simp only [splitTreeAt] at ht1 ht2
  by_cases h1 : w.take k₁ = [] ∨ w.drop k₁ = []
  · simp only [h1, ite_true, Finset.notMem_empty] at ht1
  · by_cases h2 : w.take k₂ = [] ∨ w.drop k₂ = []
    · simp only [h2, ite_true, Finset.notMem_empty] at ht2
    · simp only [h1, h2, ite_false, Finset.mem_image] at ht1 ht2
      obtain ⟨⟨l₁, r₁⟩, hprod1, rfl⟩ := ht1
      obtain ⟨⟨l₂, r₂⟩, hprod2, hEq⟩ := ht2
      cases hEq
      rw [Finset.mem_product] at hprod1 hprod2
      have hy1 := ((mem_treesUpTo_iff T g d B _ _).mp hprod1.1).2.2.1
      have hy2 := ((mem_treesUpTo_iff T g d B _ _).mp hprod2.1).2.2.1
      have hkk : w.take k₁ = w.take k₂ := by rw [← hy1, hy2]
      have hk1 : k₁ ≤ w.length := by
        rw [Finset.mem_range] at h₁
        omega
      have hk2 : k₂ ≤ w.length := by
        rw [Finset.mem_range] at h₂
        omega
      have hlen : (w.take k₁).length = (w.take k₂).length := by rw [hkk]
      rw [List.length_take, List.length_take, Nat.min_eq_left hk1,
        Nat.min_eq_left hk2] at hlen
      exact hne hlen

/-- One split position contributes the factored product of inside values. -/
theorem splitTreeAt_sum (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ)
    (d : ℕ) (A B C : g.NT) (w : List T) (k : ℕ)
    (hIH : ∀ X : g.NT, ∀ u : List T,
      inside T g q d X u = treeSum T g q d X u) :
    (if w.take k = [] ∨ w.drop k = [] then (0 : ℝ)
      else
        q ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ *
          inside T g q d B (w.take k) * inside T g q d C (w.drop k)) =
      ∑ t ∈ splitTreeAt T g A B C w k
        (treesUpTo T g d B (w.take k))
        (treesUpTo T g d C (w.drop k)), t.weightOf q := by
  by_cases h : w.take k = [] ∨ w.drop k = []
  · simp only [ite_true, splitTreeAt, h, ite_true, Finset.sum_empty]
  · simp only [h, ite_false, splitTreeAt, ite_false]
    rw [hIH B (w.take k), hIH C (w.drop k)]
    simp only [treeSum]
    have hnode_inj : Function.Injective
        (fun p : PDerivTree g.NT T × PDerivTree g.NT T =>
          PDerivTree.node A B C p.1 p.2) := by
      intro x y hxy
      obtain ⟨a₁, b₁⟩ := x
      obtain ⟨a₂, b₂⟩ := y
      have h2 : PDerivTree.node A B C a₁ b₁ =
        PDerivTree.node A B C a₂ b₂ := hxy
      cases h2
      rfl
    have hinj : Set.InjOn
        (fun p : PDerivTree g.NT T × PDerivTree g.NT T =>
          PDerivTree.node A B C p.1 p.2)
        ↑((treesUpTo T g d B (w.take k)) ×ˢ
          (treesUpTo T g d C (w.drop k))) := by
      intro x _ y _ heq
      exact hnode_inj heq
    rw [Finset.sum_image hinj, Finset.sum_product]
    simp only [PDerivTree.weightOf]
    rw [← Finset.sum_mul_sum, ← Finset.mul_sum]

/-- Leaf trees have the expected form. -/
theorem mem_leafTrees_form (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (A : g.NT) (w : List T)
    (t : PDerivTree g.NT T) (ht : t ∈ leafTrees T g A w) :
    ∃ a, w = [a] ∧ t = PDerivTree.leaf A a ∧
      ⟨A, [Symbol.terminal a]⟩ ∈ g.rules := by
  cases w with
  | nil =>
      rw [leafTrees_nil] at ht
      exact absurd ht (Finset.notMem_empty _)
  | cons a rest =>
      cases rest with
      | nil =>
          rw [leafTrees_singleton] at ht
          by_cases hR : ⟨A, [Symbol.terminal a]⟩ ∈ g.rules
          · simp only [hR, ite_true, Finset.mem_singleton] at ht
            exact ⟨a, rfl, ht, hR⟩
          · simp only [hR, ite_false, Finset.notMem_empty] at ht
      | cons b rest =>
          rw [leafTrees_cons_cons] at ht
          exact absurd ht (Finset.notMem_empty _)

/-- Leaf and branch trees are disjoint. -/
theorem leaf_branch_disjoint (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T) :
    Disjoint (leafTrees T g A w) (branchTrees T g d A w) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  obtain ⟨a, rfl, rfl, -⟩ := mem_leafTrees_form T g A _ t ht1
  rw [mem_branchTrees_iff T g d A [a] (PDerivTree.leaf A a)] at ht2
  obtain ⟨B, C, k, l, r, -, -, -, -, -, -, hEq⟩ := ht2
  cases hEq

/-- Binary trees for different rule bodies are disjoint. -/
theorem branchTrees_pairwise (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T) :
    Set.PairwiseDisjoint (↑(binRules T g A) : Set (g.NT × g.NT))
      (fun p => splitTrees T g d A p.1 p.2 w) := by
  intro x hx y hy hne
  obtain ⟨B₁, C₁⟩ := x
  obtain ⟨B₂, C₂⟩ := y
  refine Finset.disjoint_left.mpr ?_
  intro t ht1 ht2
  obtain ⟨l₁, r₁, hEq₁⟩ := mem_splitTrees_node T g d A B₁ C₁ w t ht1
  obtain ⟨l₂, r₂, hEq₂⟩ := mem_splitTrees_node T g d A B₂ C₂ w t ht2
  rw [hEq₁] at hEq₂
  cases hEq₂
  exact hne rfl

/-- The inside recurrence equals the sum of derivation weights (Collins,
Section 3): `inside d A w` is the sum of `weightOf` over valid trees of
depth at most `d` with yield `w` rooted at `A`. This is purely algebraic:
no normalization is assumed. -/
theorem inside_eq_treeSum (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ)
    (d : ℕ) (A : g.NT) (w : List T) :
    inside T g q d A w = treeSum T g q d A w := by
  induction d generalizing A w with
  | zero =>
      rw [inside_zero T g q A w, treeSum, treesUpTo_zero T g A w,
        Finset.sum_empty]
  | succ d ih =>
      rw [inside_succ T g q d A w, treeSum, treesUpTo_succ T g d A w,
        Finset.sum_union (leaf_branch_disjoint T g d A w)]
      congr 1
      · exact leafWeight_eq_sum T g q A w
      · rw [branchTrees, Finset.sum_biUnion (branchTrees_pairwise T g d A w)]
        apply Finset.sum_congr rfl
        intro p _
        obtain ⟨B, C⟩ := p
        rw [splitTrees]
        rw [Finset.sum_biUnion]
        · apply Finset.sum_congr rfl
          intro k _
          exact splitTreeAt_sum T g q d A B C w k (fun X u => ih X u)
        · intro k₁ hk₁ k₂ hk₂ hne
          exact splitTreeAt_disjoint T g d A B C w k₁ k₂ hk₁ hk₂ hne

/-- Trees for `w` all have depth at most `|w|`, so the tree set stabilizes
once `d >= |w|`. -/
theorem treesUpTo_stable (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T)
    (hd : w.length ≤ d) :
    treesUpTo T g d A w = treesUpTo T g w.length A w := by
  ext t
  rw [mem_treesUpTo_iff, mem_treesUpTo_iff]
  constructor
  · rintro ⟨hV, hdd, hy, hroot⟩
    refine ⟨hV, ?_, hy, hroot⟩
    have hle : t.depthOf ≤ t.yieldOf.length := t.depthOf_le_length
    have hlen2 : t.yieldOf.length = w.length := congrArg List.length hy
    omega
  · rintro ⟨hV, hdw, hy, hroot⟩
    exact ⟨hV, by omega, hy, hroot⟩

/-- The inside recurrence stabilizes once `d >= |w|`: depth `|w|` already
sums every derivation of `w`. -/
theorem inside_stable (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ)
    (d : ℕ) (A : g.NT) (w : List T) (hd : w.length ≤ d) :
    inside T g q d A w = inside T g q w.length A w := by
  rw [inside_eq_treeSum, inside_eq_treeSum, treeSum, treeSum,
    treesUpTo_stable T g d A w hd]

/-- Weights of valid trees are nonnegative under a rule-weight hypothesis. -/
theorem weightOf_nonneg_of_valid (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (q : ContextFreeRule T g.NT → ℝ)
    (h : IsRuleWeight T g q) (t : PDerivTree g.NT T)
    (hV : IsValidTree T g t) : 0 ≤ t.weightOf q := by
  have aux : ∀ s : PDerivTree g.NT T, IsValidTree T g s → 0 ≤ s.weightOf q := by
    intro s
    induction s with
    | leaf A' a =>
        intro hVs
        simp only [PDerivTree.weightOf]
        exact h _ hVs
    | node A' B C l r ihl ihr =>
        intro hVs
        obtain ⟨hr, -, -, hVl, hVr⟩ := hVs
        simp only [PDerivTree.weightOf]
        exact mul_nonneg (mul_nonneg (h _ hr) (ihl hVl)) (ihr hVr)
  exact aux t hV

/-- Valid trees give Mathlib derivations from their root. -/
theorem tree_yields_of_mem (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (d : ℕ) (A : g.NT) (w : List T)
    (t : PDerivTree g.NT T) (ht : t ∈ treesUpTo T g d A w) :
    Yields g [Symbol.nonterminal A] w := by
  have hmem := (mem_treesUpTo_iff T g d A w t).mp ht
  have aux : ∀ s : PDerivTree g.NT T, IsValidTree T g s →
      Yields g [Symbol.nonterminal s.rootOf] s.yieldOf := by
    intro s
    induction s with
    | leaf A' a =>
        intro hVs
        exact yields_of_rule hVs (Yields.terminal a Yields.nil)
    | node A' B C l r ihl ihr =>
        intro hVs
        obtain ⟨hr, hBl, hCr, hVl, hVr⟩ := hVs
        have hcat := Yields.append (ihl hVl) (ihr hVr)
        rw [hBl, hCr] at hcat
        exact yields_of_rule hr hcat
  have h := aux t hmem.1
  rw [hmem.2.2.1, hmem.2.2.2] at h
  exact h

/-- Positive inside weight implies CYK acceptance: a tree witnesses the
derivation, and `mem_cykCell_iff` turns it into a cell entry. -/
theorem mem_cykCell_of_inside_pos (T : Type*) (g : ContextFreeGrammar T)
    [DecidableEq T] [DecidableEq g.NT] (hg : IsChomskyNormalForm g)
    (q : ContextFreeRule T g.NT → ℝ) (d : ℕ) (A : g.NT) (w : List T)
    (hw : w ≠ []) (h : 0 < inside T g q d A w) :
    A ∈ cykCell g w.length w := by
  by_cases hE : treesUpTo T g d A w = ∅
  · rw [inside_eq_treeSum, treeSum, hE, Finset.sum_empty] at h
    exact absurd h (lt_irrefl _)
  · have hne : (treesUpTo T g d A w).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hE
    obtain ⟨t, ht⟩ := hne
    exact (mem_cykCell_iff hg w.length hw le_rfl).mpr
      (tree_yields_of_mem T g d A w t ht)

/-- The two-rule ambiguous grammar `A -> A A`, `A -> a` over one
nonterminal and one terminal. -/
def ambG : ContextFreeGrammar Unit where
  NT := Unit
  initial := ()
  rules := {⟨(), [Symbol.nonterminal (), Symbol.nonterminal ()]⟩,
    ⟨(), [Symbol.terminal ()]⟩}

/-- Decidable equality on the nonterminals of the example grammar. -/
instance : DecidableEq ambG.NT := inferInstanceAs (DecidableEq Unit)

/-- Left-associated tree for `a a a`. -/
def ambT₁ : PDerivTree ambG.NT Unit :=
  PDerivTree.node ambG.initial ambG.initial ambG.initial
    (PDerivTree.leaf ambG.initial ())
    (PDerivTree.node ambG.initial ambG.initial ambG.initial
      (PDerivTree.leaf ambG.initial ())
      (PDerivTree.leaf ambG.initial ()))

/-- Right-associated tree for `a a a`. -/
def ambT₂ : PDerivTree ambG.NT Unit :=
  PDerivTree.node ambG.initial ambG.initial ambG.initial
    (PDerivTree.node ambG.initial ambG.initial ambG.initial
      (PDerivTree.leaf ambG.initial ())
      (PDerivTree.leaf ambG.initial ()))
    (PDerivTree.leaf ambG.initial ())

/-- The two trees for `a a a` are distinct. -/
theorem ambT_ne : ambT₁ ≠ ambT₂ := by decide

/-- Both trees yield `a a a`. -/
theorem ambT_yield : ambT₁.yieldOf = [(), (), ()] ∧
    ambT₂.yieldOf = [(), (), ()] := by decide

/-- Both trees are valid derivations of depth three. -/
theorem ambT_mem (d : ℕ) (hd : 3 ≤ d) :
    ambT₁ ∈ treesUpTo Unit ambG d ambG.initial [(), (), ()] ∧
      ambT₂ ∈ treesUpTo Unit ambG d ambG.initial [(), (), ()] := by
  have h1 : ambT₁ ∈ treesUpTo Unit ambG 3 ambG.initial [(), (), ()] := by decide
  have h2 : ambT₂ ∈ treesUpTo Unit ambG 3 ambG.initial [(), (), ()] := by decide
  have e1 : treesUpTo Unit ambG 3 ambG.initial [(), (), ()] ⊆
      treesUpTo Unit ambG d ambG.initial [(), (), ()] := by
    intro t ht
    rw [mem_treesUpTo_iff Unit ambG 3 ambG.initial [(), (), ()] t] at ht
    rw [mem_treesUpTo_iff Unit ambG d ambG.initial [(), (), ()] t]
    obtain ⟨hV, hdd, hy, hroot⟩ := ht
    exact ⟨hV, by omega, hy, hroot⟩
  exact ⟨e1 h1, e1 h2⟩

/-- Boundary: an ambiguous string sums two trees. Under nonnegative rule
weights, the inside value counts both derivations. -/
theorem amb_two_trees_le (q : ContextFreeRule Unit ambG.NT → ℝ)
    (h : IsRuleWeight Unit ambG q) :
    ambT₁.weightOf q + ambT₂.weightOf q ≤
      inside Unit ambG q 3 ambG.initial [(), (), ()] := by
  rw [inside_eq_treeSum]
  simp only [treeSum]
  have hpair : ambT₁.weightOf q + ambT₂.weightOf q =
      ∑ x ∈ ({ambT₁, ambT₂} : Finset (PDerivTree ambG.NT Unit)),
        x.weightOf q := by
    rw [Finset.sum_insert (by simp [ambT_ne]), Finset.sum_singleton]
  rw [hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ _
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (ambT_mem 3 le_rfl).1
    · exact (ambT_mem 3 le_rfl).2
  · intro i hi _
    have hiV : IsValidTree Unit ambG i :=
      ((mem_treesUpTo_iff Unit ambG 3 () [(), (), ()] i).mp hi).1
    exact weightOf_nonneg_of_valid Unit ambG q h i hiV

/-- A constant-one weight function on the two-rule grammar. -/
def badWeightFun : ContextFreeRule Unit ambG.NT → ℝ := fun _ => 1

/-- Boundary: violated normalization still satisfies the recurrence
identity, with per-nonterminal total two instead of one. -/
theorem badWeight_sum :
    ∑ r ∈ ambG.rules.filter (fun r => r.input = ambG.initial), badWeightFun r = 2 := by
  have hF : ambG.rules.filter (fun r => r.input = ambG.initial) = ambG.rules := by
    decide
  rw [hF]
  simp [ambG, badWeightFun]

/-- The constant-one weights are not a probability: the total is two. -/
theorem badWeight_not_normalized : ¬ IsNormalized Unit ambG badWeightFun := by
  intro h
  have hsum := h.2 ambG.initial
  rw [badWeight_sum] at hsum
  norm_num at hsum

/-- The example grammar is in Chomsky normal form. -/
theorem ambG_cnf : IsChomskyNormalForm ambG := by
  have hrules : ambG.rules =
      {⟨(), [Symbol.nonterminal (), Symbol.nonterminal ()]⟩,
        ⟨(), [Symbol.terminal ()]⟩} := rfl
  constructor
  · intro r hr
    rw [hrules, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Or.inl ⟨ambG.initial, ambG.initial, rfl⟩
    · exact Or.inr (Or.inl ⟨(), rfl⟩)
  · right
    intro r hr
    rw [hrules, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp

/-! ## The Chi-Geman counterexample -/

/-- One-nonterminal derivation trees: branching (`node`) expands each `A`
by one rule, termination is finiteness of the tree itself. -/
inductive CGTree where
  | leaf : CGTree
  | node : CGTree → CGTree → CGTree
deriving DecidableEq

/-- Depth of a one-nonterminal tree; leaves have depth one. -/
def CGTree.depth : CGTree → ℕ
  | .leaf => 1
  | .node l r => 1 + max l.depth r.depth

/-- Weight of a one-nonterminal tree: `q` at leaves, `p` at nodes. -/
def CGTree.weight (p q : ℝ) : CGTree → ℝ
  | .leaf => q
  | .node l r => p * l.weight p q * r.weight p q

/-- All one-nonterminal trees of depth at most `h`. -/
def cgTrees : ℕ → Finset CGTree
  | 0 => ∅
  | (h + 1) => {CGTree.leaf} ∪
      ((cgTrees h) ×ˢ (cgTrees h)).image fun p => CGTree.node p.1 p.2

/-- Total weight of one-nonterminal trees of depth at most `h`. -/
def cgTotal (p q : ℝ) (h : ℕ) : ℝ :=
  ∑ t ∈ cgTrees h, t.weight p q

/-- Unfolding `cgTrees` at depth zero. -/
theorem cgTrees_zero : cgTrees 0 = ∅ := rfl

/-- Unfolding `cgTrees` at successor depth. -/
theorem cgTrees_succ (h : ℕ) :
    cgTrees (h + 1) = {CGTree.leaf} ∪
      ((cgTrees h) ×ˢ (cgTrees h)).image
        fun p => CGTree.node p.1 p.2 := rfl

/-- Membership in `cgTrees` is a depth bound. -/
theorem mem_cgTrees_iff (h : ℕ) (t : CGTree) :
    t ∈ cgTrees h ↔ t.depth ≤ h := by
  induction h generalizing t with
  | zero =>
      rw [cgTrees_zero]
      simp only [Finset.notMem_empty, false_iff]
      intro hd
      cases t with
      | leaf =>
          simp only [CGTree.depth] at hd
          omega
      | node _ _ =>
          simp only [CGTree.depth] at hd
          omega
  | succ h ih =>
      constructor
      · intro ht
        rw [cgTrees_succ h, Finset.mem_union] at ht
        rcases ht with ht | ht
        · rw [Finset.mem_singleton] at ht
          subst ht
          simp only [CGTree.depth]
          omega
        · rw [Finset.mem_image] at ht
          obtain ⟨⟨l, r⟩, hprod, rfl⟩ := ht
          rw [Finset.mem_product] at hprod
          have hl := (ih l).mp hprod.1
          have hr := (ih r).mp hprod.2
          simp only [CGTree.depth]
          omega
      · intro hd
        cases t with
        | leaf =>
            rw [cgTrees_succ h, Finset.mem_union]
            exact Or.inl (Finset.mem_singleton_self _)
        | node l r =>
            have hl : l.depth ≤ h := by
              simp only [CGTree.depth] at hd
              omega
            have hr : r.depth ≤ h := by
              simp only [CGTree.depth] at hd
              omega
            rw [cgTrees_succ h, Finset.mem_union]
            exact Or.inr (Finset.mem_image.mpr
              ⟨⟨l, r⟩, Finset.mem_product.mpr ⟨(ih l).mpr hl,
                (ih r).mpr hr⟩, rfl⟩)

/-- Weights of one-nonterminal trees are nonnegative. -/
theorem cgWeight_nonneg (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (t : CGTree) :
    0 ≤ t.weight p q := by
  induction t with
  | leaf =>
      simp only [CGTree.weight]
      exact hq
  | node l r ihl ihr =>
      simp only [CGTree.weight]
      exact mul_nonneg (mul_nonneg hp ihl) ihr

/-- The tree sets grow with depth. -/
theorem cgTrees_mono_subset (h : ℕ) : cgTrees h ⊆ cgTrees (h + 1) := by
  intro t ht
  rw [mem_cgTrees_iff h t] at ht
  rw [mem_cgTrees_iff (h + 1) t]
  omega

/-- The total weight grows with depth. -/
theorem cgTotal_mono (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (h : ℕ) :
    cgTotal p q h ≤ cgTotal p q (h + 1) := by
  simp only [cgTotal]
  apply Finset.sum_le_sum_of_subset_of_nonneg (cgTrees_mono_subset h)
  intro t _ _
  exact cgWeight_nonneg p q hp hq t

/-- The Chi-Geman recurrence from the tree sum:
`cgTotal (h+1) = q + p * (cgTotal h)^2`. -/
theorem cgTotal_succ (p q : ℝ) (h : ℕ) :
    cgTotal p q (h + 1) = q + p * (cgTotal p q h) ^ 2 := by
  have hdisj : Disjoint ({CGTree.leaf} : Finset CGTree)
      (((cgTrees h) ×ˢ (cgTrees h)).image
        (fun p => CGTree.node p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rw [Finset.mem_singleton] at ht1
    rw [Finset.mem_image] at ht2
    obtain ⟨⟨l, r⟩, -, hEq⟩ := ht2
    subst ht1
    have hEq2 : CGTree.node l r = CGTree.leaf := hEq
    cases hEq2
  have hnode_inj : Function.Injective
      (fun p : CGTree × CGTree => CGTree.node p.1 p.2) := by
    intro x y hxy
    obtain ⟨a₁, b₁⟩ := x
    obtain ⟨a₂, b₂⟩ := y
    have h2 : CGTree.node a₁ b₁ = CGTree.node a₂ b₂ := hxy
    cases h2
    rfl
  have hinj : ∀ x ∈ (cgTrees h) ×ˢ (cgTrees h),
      ∀ y ∈ (cgTrees h) ×ˢ (cgTrees h),
      (fun p => CGTree.node p.1 p.2) x =
        (fun p => CGTree.node p.1 p.2) y → x = y := by
    intro x _ y _ heq
    exact hnode_inj heq
  rw [cgTotal, cgTrees_succ h, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton, CGTree.weight]
  congr 1
  rw [Finset.sum_image hinj, Finset.sum_product]
  simp only [CGTree.weight, cgTotal]
  rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
  ring

/-- The Chi-Geman total-weight sequence: `S 0 = S 1 = 0` and the recurrence
for higher indices. -/
def chiGemanS (p q : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => if n = 0 then 0 else q + p * (chiGemanS p q n) ^ 2

/-- `S 0 = 0`. -/
theorem chiGemanS_zero (p q : ℝ) : chiGemanS p q 0 = 0 := rfl

/-- `S 1 = 0`: no tree has depth at most zero (index shift: `S (h + 1)` sums trees of
depth at most `h`; leaves have depth one). -/
theorem chiGemanS_one (p q : ℝ) : chiGemanS p q 1 = 0 := rfl

/-- The recurrence step. -/
theorem chiGemanS_succ_succ (p q : ℝ) (n : ℕ) :
    chiGemanS p q (n + 1 + 1) =
      q + p * (chiGemanS p q (n + 1)) ^ 2 := rfl

/-- `S (h + 1)` is the total weight of trees of depth at most `h`. -/
theorem chiGemanS_link (p q : ℝ) (h : ℕ) :
    chiGemanS p q (h + 1) = cgTotal p q h := by
  induction h with
  | zero =>
      rw [chiGemanS_one, cgTotal, cgTrees_zero, Finset.sum_empty]
  | succ h ih =>
      rw [chiGemanS_succ_succ p q h, cgTotal_succ p q h, ih]

/-- The sequence stays nonnegative. -/
theorem chiGemanS_nonneg (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (h : ℕ) :
    0 ≤ chiGemanS p q h := by
  have pair : ∀ n, 0 ≤ chiGemanS p q n ∧ 0 ≤ chiGemanS p q (n + 1) := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_⟩
        · simp only [chiGemanS_zero p q, le_refl]
        · simp only [chiGemanS_one p q, le_refl]
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        rw [chiGemanS_succ_succ p q n]
        have hsq : 0 ≤ (chiGemanS p q (n + 1)) ^ 2 := by
          rw [pow_two]
          exact mul_self_nonneg _
        exact add_nonneg hq (mul_nonneg hp hsq)
  exact (pair h).1

/-- Any post-fixed point of `x ↦ q + p * x ^ 2` bounds the sequence. -/
theorem chiGemanS_le_bound (p q b : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hb : q + p * b ^ 2 ≤ b) (h : ℕ) : chiGemanS p q h ≤ b := by
  have hnn : ∀ m, 0 ≤ chiGemanS p q m := chiGemanS_nonneg p q hp hq
  have hb0 : 0 ≤ b :=
    le_trans (add_nonneg hq (mul_nonneg hp (by
      rw [pow_two]
      exact mul_self_nonneg _))) hb
  have pair : ∀ n, chiGemanS p q n ≤ b ∧ chiGemanS p q (n + 1) ≤ b := by
    intro n
    induction n with
    | zero =>
        change chiGemanS p q 0 ≤ b ∧ chiGemanS p q 1 ≤ b
        simp only [chiGemanS_zero p q, chiGemanS_one p q]
        exact ⟨hb0, hb0⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        rw [chiGemanS_succ_succ p q n]
        have hsq : (chiGemanS p q (n + 1)) ^ 2 ≤ b ^ 2 := by
          have h1 : 0 ≤ chiGemanS p q (n + 1) := hnn _
          have hfac : b ^ 2 - (chiGemanS p q (n + 1)) ^ 2 =
              (b - chiGemanS p q (n + 1)) *
                (b + chiGemanS p q (n + 1)) := by ring
          have hpos : 0 ≤ (b - chiGemanS p q (n + 1)) *
              (b + chiGemanS p q (n + 1)) :=
            mul_nonneg (sub_nonneg.mpr ih.2) (by linarith)
          linarith
        calc q + p * (chiGemanS p q (n + 1)) ^ 2
            ≤ q + p * b ^ 2 := by
              have hmul := mul_le_mul_of_nonneg_left hsq hp
              linarith
          _ ≤ b := hb
  exact (pair h).1

/-- The sequence is nondecreasing. -/
theorem chiGemanS_mono (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (n : ℕ) :
    chiGemanS p q n ≤ chiGemanS p q (n + 1) := by
  cases n with
  | zero =>
      change chiGemanS p q 0 ≤ chiGemanS p q 1
      rw [chiGemanS_zero, chiGemanS_one]
  | succ n =>
      rw [chiGemanS_link p q (n + 1), chiGemanS_link p q n]
      exact cgTotal_mono p q hp hq n

/-- Main bound (Chi and Geman, p. 300): for `p = 2 / 3` the total weight of
finite trees stays below `1 / 2`, since `1 / 3 + (2 / 3) * (1 / 2)^2 = 1 / 2`. -/
theorem chiGeman_main_half (h : ℕ) :
    chiGemanS (2 / 3) (1 / 3) h ≤ 1 / 2 := by
  apply chiGemanS_le_bound _ _ _ (by norm_num) (by norm_num) ?_ h
  norm_num

/-- Missing mass: the infinite-derivation event has weight at least half. -/
theorem chiGeman_missing_mass (h : ℕ) :
    1 / 2 ≤ 1 - chiGemanS (2 / 3) (1 / 3) h := by
  have hle := chiGeman_main_half h
  linarith

/-- The local rule weights sum to one. -/
theorem chiGeman_weights_sum : (2 / 3 : ℝ) + 1 / 3 = 1 := by norm_num

/-- Boundary `p = 1 / 2`: the constant sequence at one is tight. -/
theorem chiGeman_tight_half (h : ℕ) :
    chiGemanS (1 / 2) (1 / 2) h ≤ 1 := by
  apply chiGemanS_le_bound _ _ _ (by norm_num) (by norm_num) ?_ h
  norm_num

/-- Boundary `p = 1 / 3`: the constant sequence at one is tight. -/
theorem chiGeman_tight_third (h : ℕ) :
    chiGemanS (1 / 3) (2 / 3) h ≤ 1 := by
  apply chiGemanS_le_bound _ _ _ (by norm_num) (by norm_num) ?_ h
  norm_num

/-- Boundary `p = 1 / 2`: one is the unique fixed point. -/
theorem chiGeman_unique_half (x : ℝ) (h : x = 1 / 2 + (1 / 2) * x ^ 2) :
    x = 1 := by
  have h2 : (x - 1) ^ 2 = 0 := by linarith [h]
  have h3 : x - 1 = 0 := by
    by_contra hne
    exact pow_ne_zero 2 hne h2
  linarith

/-- Boundary `p = 1 / 3`: the fixed points are one and two. -/
theorem chiGeman_fixed_third (x : ℝ) (h : x = 2 / 3 + (1 / 3) * x ^ 2) :
    x = 1 ∨ x = 2 := by
  have h2 : (x - 1) * (x - 2) = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    linarith
  · right
    linarith

/-- The first nontrivial value: `S 2 = q`. -/
theorem chiGemanS_two : chiGemanS (2 / 3) (1 / 3) 2 = 1 / 3 := by
  change chiGemanS (2 / 3) (1 / 3) (0 + 1 + 1) = 1 / 3
  rw [chiGemanS_succ_succ, chiGemanS_one]
  norm_num

/-- The next value: `S 3 = q + p * q ^ 2 = 11 / 27`. -/
theorem chiGemanS_three : chiGemanS (2 / 3) (1 / 3) 3 = 11 / 27 := by
  change chiGemanS (2 / 3) (1 / 3) (1 + 1 + 1) = 11 / 27
  rw [chiGemanS_succ_succ, show (1 + 1 : ℕ) = 2 from rfl, chiGemanS_two]
  norm_num

/-- The Chi-Geman weights on the two-rule grammar. -/
noncomputable def cgWeightFun : ContextFreeRule Unit ambG.NT → ℝ
  | ⟨_, [Symbol.terminal _]⟩ => 1 / 3
  | _ => 2 / 3

/-- The Chi-Geman weights are normalized per nonterminal. -/
theorem cgWeightFun_normalized : IsNormalized Unit ambG cgWeightFun := by
  have hrules : ambG.rules =
      {⟨(), [Symbol.nonterminal (), Symbol.nonterminal ()]⟩,
        ⟨(), [Symbol.terminal ()]⟩} := rfl
  constructor
  · intro r hr
    rw [hrules, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · have e1 : cgWeightFun
          ⟨(), [Symbol.nonterminal (), Symbol.nonterminal ()]⟩ =
          2 / 3 := rfl
      rw [e1]
      norm_num
    · have e2 : cgWeightFun ⟨(), [Symbol.terminal ()]⟩ = 1 / 3 := rfl
      rw [e2]
      norm_num
  · intro A
    have hA : A = ambG.initial := by cases A; rfl
    rw [hA]
    have hF : ambG.rules.filter (fun r => r.input = ambG.initial) = ambG.rules := by
      decide
    rw [hF, hrules]
    have hne : (⟨(), [Symbol.nonterminal (), Symbol.nonterminal ()]⟩ :
        ContextFreeRule Unit ambG.NT) ≠
        ⟨(), [Symbol.terminal ()]⟩ := by decide
    rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have e1 : cgWeightFun
        ⟨(), [Symbol.nonterminal (), Symbol.nonterminal ()]⟩ = 2 / 3 := rfl
    have e2 : cgWeightFun ⟨(), [Symbol.terminal ()]⟩ = 1 / 3 := rfl
    rw [e1, e2]
    norm_num

end Cslib.Language
