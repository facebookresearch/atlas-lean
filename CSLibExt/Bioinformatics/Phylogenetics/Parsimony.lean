/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinPruning
public import Mathlib.Algebra.Tropical.BigOperators
import Lean.Elab.Tactic.Omega

/-!
# Small parsimony: Sankoff's and Fitch's algorithms

The *small parsimony problem* asks, for a rooted binary tree with observed character states
`σ : L → S` at the leaves and substitution costs on the edges, for the minimum total cost of a
labeling of the internal vertices. Costs live in `WithTop ℕ` (`⊤` forbids a change).

**Sankoff (1975)** is Felsenstein's pruning algorithm (`FelsensteinPruning.prune`) over the
min-plus (tropical) semiring `MinTropical (WithTop ℕ)`, in which `+` is `min` and `*` is `+`:
the edge weights are the costs `trop (c a b)`, and the leaf weight of state `s` at leaf `l` is
the tropical one (cost `0`) if `s = σ l` and the tropical zero (cost `⊤`) otherwise. The
brute-force "likelihood" of the pruning file then is the minimum, over all labelings, of the
total cost, and pruning computes it bottom-up. On the states `Fin n`, the tabulated
`FelsensteinPruning.pruneTab (leafObs σ)` computes the whole vector of costs of every subtree
once (`pruneTab_get`), with `O(n²)` min-plus operations per internal vertex.

**Fitch (1971)**, for unit costs (`0` for no change, `1` for a change), keeps at every vertex a
set of states and a count: a leaf has `{σ l}` and `0`; an internal vertex with children
`(A, m)` and `(B, n)` has `(A ∩ B, m + n)` if `A ∩ B` is nonempty and `(A ∪ B, m + n + 1)`
otherwise.

## Main results

* `sankoff_eq_inf`: **Sankoff's algorithm computes the minimum cost**: `sankoff σ t s` is the
  minimum of `edgeCost t s x` over the labelings `x` that agree with `σ` at the leaves.
* `sankoff_le_edgeCost`, `exists_edgeCost_eq_sankoff`: the minimum is a lower bound and is
  attained.
* `sankoff_leaf`, `sankoff_node`: Sankoff's recursion in plain min-plus form.
* `fitch_score_eq`: **Fitch's count is the small-parsimony score** for unit costs: it equals the
  minimum over root states of the Sankoff cost.
* `fitch_set_eq`: Fitch's root set is exactly the set of optimal root states.

## References

* D. Sankoff, *Minimal mutation trees of sequences*, SIAM J. Appl. Math. 28 (1975), 35–42.
* W. M. Fitch, *Toward defining the course of evolution: minimum change for a specific tree
  topology*, Syst. Zool. 20 (1971), 406–416.
* J. A. Hartigan, *Minimum mutation fits to a given tree*, Biometrics 29 (1973), 53–65.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Phylogenetics.Parsimony

open FelsensteinPruning Tree MinTropical

universe u v w

variable {L : Type u} {S : Type v}

/-- The cost semiring: `MinTropical (WithTop ℕ)`, with `min` as addition and `+` as
multiplication. -/
abbrev Cost : Type := MinTropical (WithTop ℕ)

/-! ## Sankoff's algorithm -/

section Sankoff

/-- The total substitution cost of a labeling `x` of the non-root vertices of `t` with root
state `s`: the sum over all edges of the cost `untrop (P a b)` from the parent's state `a` to
the child's state `b`. -/
def edgeCost : (t : Tree L S Cost) → S → Labeling t → WithTop ℕ
  | leaf _, _, _ => 0
  | node P l Q r, s, z =>
    (untrop (P s z.1.1) + edgeCost l z.1.1 z.1.2) + (untrop (Q s z.2.1) + edgeCost r z.2.1 z.2.2)

/-- The labeling `x` (with root state `s`) agrees with the observed states `σ` at every leaf. -/
def Agrees (σ : L → S) : (t : Tree L S Cost) → S → Labeling t → Prop
  | leaf l, s, _ => s = σ l
  | node _ l _ r, _, z => Agrees σ l z.1.1 z.1.2 ∧ Agrees σ r z.2.1 z.2.2

/-- Agreement with the leaf states is decidable. -/
instance instDecidableAgrees [DecidableEq S] (σ : L → S) :
    (t : Tree L S Cost) → (s : S) → (x : Labeling t) → Decidable (Agrees σ t s x)
  | leaf l, s, _ => inferInstanceAs (Decidable (s = σ l))
  | node _ l _ r, _, z =>
    letI := instDecidableAgrees σ l z.1.1 z.1.2
    letI := instDecidableAgrees σ r z.2.1 z.2.2
    inferInstanceAs (Decidable (_ ∧ _))

variable [DecidableEq S]

/-- The leaf weights of the observed states `σ`: the tropical one (cost `0`) at the observed
state and the tropical zero (cost `⊤`) at every other state. -/
def leafObs (σ : L → S) (l : L) (s : S) : Cost :=
  if s = σ l then 1 else 0

/-- The weight of a labeling in the tropical semiring is its edge cost if it agrees with the
leaf states and `⊤` otherwise. -/
theorem untrop_weight (σ : L → S) :
    ∀ (t : Tree L S Cost) (s : S) (x : Labeling t),
      untrop (weight (leafObs σ) t s x) = if Agrees σ t s x then edgeCost t s x else ⊤
  | leaf l, s, x => by
      by_cases h : s = σ l <;> simp [weight, leafObs, Agrees, edgeCost, h]
  | node P l Q r, s, z => by
      simp only [weight, untrop_mul, untrop_weight σ l, untrop_weight σ r, Agrees, edgeCost]
      by_cases hl : Agrees σ l z.1.1 z.1.2 <;> by_cases hr : Agrees σ r z.2.1 z.2.2 <;>
        simp [hl, hr]

variable [Fintype S]

/-- **Sankoff's algorithm**: the minimum cost of the subtree `t` given the state `s` at its
root, computed by Felsenstein's pruning recursion over the tropical semiring. -/
def sankoff (σ : L → S) (t : Tree L S Cost) (s : S) : WithTop ℕ :=
  untrop (prune (leafObs σ) t s)

/-- **Sankoff's algorithm computes the small-parsimony cost**: `sankoff σ t s` is the minimum
total edge cost over all labelings of the non-root vertices that agree with the observed states
at the leaves (with root state `s`).

Source: Sankoff (1975). -/
theorem sankoff_eq_inf (σ : L → S) (t : Tree L S Cost) (s : S) :
    sankoff σ t s = (Finset.univ.filter (Agrees σ t s)).inf (edgeCost t s) := by
  rw [sankoff, prune_eq_bruteLik, bruteLik, Finset.untrop_sum']
  simp only [Function.comp_def, untrop_weight]
  rw [Finset.inf_ite, Finset.inf_top, inf_top_eq]

/-- Sankoff's cost is a lower bound for the cost of every labeling that agrees with the leaf
states. -/
theorem sankoff_le_edgeCost (σ : L → S) (t : Tree L S Cost) (s : S) (x : Labeling t)
    (hx : Agrees σ t s x) : sankoff σ t s ≤ edgeCost t s x := by
  rw [sankoff_eq_inf]
  exact Finset.inf_le (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)

/-- Sankoff's cost is attained: if it is finite, some labeling that agrees with the leaf states
has exactly this cost. (It is `⊤` exactly when every agreeing labeling uses a forbidden change,
or when `t` is a single leaf whose observed state is not `s`.) -/
theorem exists_edgeCost_eq_sankoff (σ : L → S) (t : Tree L S Cost) (s : S)
    (h : sankoff σ t s ≠ ⊤) : ∃ x, Agrees σ t s x ∧ edgeCost t s x = sankoff σ t s := by
  rw [sankoff_eq_inf] at h ⊢
  have hne : (Finset.univ.filter (Agrees σ t s)).Nonempty := by
    by_contra hemp
    exact h (by simp [Finset.not_nonempty_iff_eq_empty.1 hemp])
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf _ hne (edgeCost t s)
  exact ⟨x, (Finset.mem_filter.1 hx).2, hxe.symm⟩

/-- Sankoff's recursion at a leaf: cost `0` at the observed state, `⊤` elsewhere. -/
theorem sankoff_leaf (σ : L → S) (l : L) (s : S) :
    sankoff σ (leaf l) s = if s = σ l then 0 else ⊤ := by
  by_cases h : s = σ l <;> simp [sankoff, prune, leafObs, h]

/-- Sankoff's recursion at an internal vertex: the cost of state `s` is the sum, over the two
children, of the minimum over the child's state `a` of the edge cost from `s` to `a` plus the
child's cost at `a`. -/
theorem sankoff_node (σ : L → S) (P Q : S → S → Cost) (l r : Tree L S Cost) (s : S) :
    sankoff σ (node P l Q r) s =
      Finset.univ.inf (fun a => untrop (P s a) + sankoff σ l a) +
        Finset.univ.inf (fun b => untrop (Q s b) + sankoff σ r b) := by
  simp only [sankoff, prune, untrop_mul, Finset.untrop_sum', Function.comp_def]

end Sankoff

/-! ## Fitch's algorithm -/

section Fitch

variable [DecidableEq S]

/-- The unit cost: `0` for no change and `1` for a change of state. -/
def unitCost (a b : S) : Cost :=
  trop (if a = b then 0 else 1)

/-- Every edge of the tree carries the unit cost. -/
def IsUnitCost : Tree L S Cost → Prop
  | leaf _ => True
  | node P l Q r => P = unitCost ∧ Q = unitCost ∧ IsUnitCost l ∧ IsUnitCost r

/-- **Fitch's algorithm**: the set of candidate states at the root of the subtree and the number
of changes counted so far. The edge weights of the tree are ignored. Each child is evaluated
once per node, so the recursion makes one call per vertex. -/
def fitch {R : Type w} (σ : L → S) : Tree L S R → Finset S × ℕ
  | leaf l => ({σ l}, 0)
  | node _ l _ r =>
    let a := fitch σ l
    let b := fitch σ r
    if (a.1 ∩ b.1).Nonempty then (a.1 ∩ b.1, a.2 + b.2) else (a.1 ∪ b.1, a.2 + b.2 + 1)

variable [Fintype S]

private lemma cost_lower {S : Type v}
    (F : Finset S) (m : ℕ) (c : S → WithTop ℕ)
    (hmem : ∀ s ∈ F, c s = (m : WithTop ℕ))
    (hgap : ∀ s ∉ F, ((m + 1 : ℕ) : WithTop ℕ) ≤ c s) (s : S) :
    (m : WithTop ℕ) ≤ c s := by
  by_cases hs : s ∈ F
  · exact le_of_eq (hmem s hs).symm
  · exact (WithTop.coe_le_coe.mpr (Nat.le_succ m)).trans (hgap s hs)

private lemma unit_edge {S : Type v} [DecidableEq S] [Fintype S]
    (F : Finset S) (m : ℕ) (c : S → WithTop ℕ) (hne : F.Nonempty)
    (hmem : ∀ s ∈ F, c s = (m : WithTop ℕ))
    (hgap : ∀ s ∉ F, ((m + 1 : ℕ) : WithTop ℕ) ≤ c s) (s : S) :
    Finset.univ.inf (fun a => (if s = a then 0 else 1) + c a) =
      ((m + if s ∈ F then 0 else 1 : ℕ) : WithTop ℕ) := by
  apply le_antisymm
  · by_cases hs : s ∈ F
    · calc
        Finset.univ.inf (fun a => (if s = a then 0 else 1) + c a) ≤
            (if s = s then 0 else 1) + c s := Finset.inf_le (Finset.mem_univ s)
        _ = ((m + if s ∈ F then 0 else 1 : ℕ) : WithTop ℕ) := by
          simp [hs, hmem s hs]
    · obtain ⟨a, ha⟩ := hne
      have hsa : s ≠ a := by
        intro h
        exact hs (h ▸ ha)
      calc
        Finset.univ.inf (fun a => (if s = a then 0 else 1) + c a) ≤
            (if s = a then 0 else 1) + c a := Finset.inf_le (Finset.mem_univ a)
        _ = ((m + if s ∈ F then 0 else 1 : ℕ) : WithTop ℕ) := by
          simp [hs, hsa, hmem a ha, add_comm]
  · apply Finset.le_inf
    intro a _
    by_cases hsa : s = a
    · subst a
      by_cases hs : s ∈ F
      · simpa [hs] using cost_lower F m c hmem hgap s
      · simpa [hs] using hgap s hs
    · have hl := add_le_add_left (cost_lower F m c hmem hgap a) (1 : WithTop ℕ)
      by_cases hs : s ∈ F
      · have hc : (m : WithTop ℕ) ≤ 1 + c a :=
          (cost_lower F m c hmem hgap a).trans
            (le_add_of_nonneg_left (show (0 : WithTop ℕ) ≤ 1 by simp))
        simpa [hs, hsa] using hc
      · simpa [hs, hsa, WithTop.coe_add, add_comm] using hl

private lemma fitch_invariant {L : Type u} {S : Type v}
    [DecidableEq S] [Fintype S] (σ : L → S) (t : Tree L S Cost)
    (ht : IsUnitCost t) :
    (fitch σ t).1.Nonempty ∧
      (∀ s ∈ (fitch σ t).1, sankoff σ t s = ((fitch σ t).2 : WithTop ℕ)) ∧
      (∀ s ∉ (fitch σ t).1,
        (((fitch σ t).2 + 1 : ℕ) : WithTop ℕ) ≤ sankoff σ t s) := by
  induction t with
  | leaf l =>
    refine ⟨by simp [fitch], ?_, ?_⟩
    · intro s hs
      have h : s = σ l := by simpa [fitch] using hs
      subst s
      simp [sankoff, prune, leafObs, fitch]
    · intro s hs
      have h : s ≠ σ l := by simpa [fitch] using hs
      simp [sankoff, prune, leafObs, fitch, h]
  | node P l Q r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := ht
    obtain ⟨hln, hlm, hlg⟩ := ihl hl
    obtain ⟨hrn, hrm, hrg⟩ := ihr hr
    have hc (s : S) :
        sankoff σ (node unitCost l unitCost r) s =
          (((fitch σ l).2 + (fitch σ r).2 +
            (if s ∈ (fitch σ l).1 then 0 else 1) +
            (if s ∈ (fitch σ r).1 then 0 else 1) : ℕ) : WithTop ℕ) := by
      simp only [sankoff, prune, untrop_mul, MinTropical.Finset.untrop_sum', unitCost]
      change
        Finset.univ.inf (fun a => (if s = a then 0 else 1) + sankoff σ l a) +
          Finset.univ.inf (fun a => (if s = a then 0 else 1) + sankoff σ r a) = _
      rw [unit_edge _ _ _ hln hlm hlg, unit_edge _ _ _ hrn hrm hrg]
      rw [← Nat.cast_add]
      congr 1
      omega
    by_cases hi : ((fitch σ l).1 ∩ (fitch σ r).1).Nonempty
    · simp only [fitch, ite_eq_left hi]
      refine ⟨hi, ?_, ?_⟩
      · intro s hs
        obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hs
        simp [hc s, ha, hb]
      · intro s hs
        rw [hc]
        apply WithTop.coe_le_coe.mpr
        by_cases ha : s ∈ (fitch σ l).1 <;>
          by_cases hb : s ∈ (fitch σ r).1
        · exact False.elim (hs (Finset.mem_inter.mpr ⟨ha, hb⟩))
        all_goals simp [ha, hb]
    · simp only [fitch, ite_eq_right hi]
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨s, hs⟩ := hln
        exact ⟨s, Finset.mem_union_left _ hs⟩
      · intro s hs
        have hab : ¬(s ∈ (fitch σ l).1 ∧ s ∈ (fitch σ r).1) := by
          intro h
          exact hi ⟨s, Finset.mem_inter.mpr h⟩
        rw [hc]
        apply congrArg (fun n : ℕ => (n : WithTop ℕ))
        by_cases ha : s ∈ (fitch σ l).1 <;>
          by_cases hb : s ∈ (fitch σ r).1
        · exact False.elim (hab ⟨ha, hb⟩)
        · simp [ha, hb]
        · simp [ha, hb]
        · simp [ha, hb] at hs
      · intro s hs
        have ha : s ∉ (fitch σ l).1 := fun h => hs (Finset.mem_union_left _ h)
        have hb : s ∉ (fitch σ r).1 := fun h => hs (Finset.mem_union_right _ h)
        simp [hc s, ha, hb]

/-- **Fitch's algorithm computes the small-parsimony score.** On a binary tree with unit costs,
Fitch's count equals the minimum, over root states, of Sankoff's cost.

Source: Fitch (1971); Hartigan (1973). -/
theorem fitch_score_eq (σ : L → S) (t : Tree L S Cost) (ht : IsUnitCost t) :
    ((fitch σ t).2 : WithTop ℕ) = Finset.univ.inf (sankoff σ t) := by
  obtain ⟨hne, hmem, hgap⟩ := fitch_invariant σ t ht
  apply le_antisymm
  · exact Finset.le_inf (fun s _ => cost_lower _ _ _ hmem hgap s)
  · obtain ⟨s, hs⟩ := hne
    calc
      Finset.univ.inf (sankoff σ t) ≤ sankoff σ t s :=
        Finset.inf_le (Finset.mem_univ s)
      _ = ((fitch σ t).2 : WithTop ℕ) := hmem s hs

/-- **Fitch's root set is the set of optimal root states**: on a binary tree with unit costs, a
root state is in Fitch's set if and only if Sankoff's cost at that state is the minimum.

Source: Hartigan (1973). -/
theorem fitch_set_eq (σ : L → S) (t : Tree L S Cost) (ht : IsUnitCost t) :
    (fitch σ t).1 = Finset.univ.filter (fun s => sankoff σ t s = (fitch σ t).2) := by
  obtain ⟨_, hmem, hgap⟩ := fitch_invariant σ t ht
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact hmem s
  · intro h
    by_contra hs
    have hg := hgap s hs
    rw [h] at hg
    have hn : (fitch σ t).2 + 1 ≤ (fitch σ t).2 := WithTop.coe_le_coe.mp hg
    omega

end Fitch

end Cslib.Bioinformatics.Phylogenetics.Parsimony
