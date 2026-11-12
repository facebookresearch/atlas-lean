/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Walls








section WalkParity

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (δ : Finset (Sym2 V))




def walkPar : {x y : V} → G.Walk x y → Bool
  | _, _, .nil => false
  | _, _, .cons (u := u) (v := v) _ p => (decide (s(u, v) ∈ δ)).xor (walkPar p)

@[simp] theorem walkPar_nil {x : V} : walkPar G δ (.nil : G.Walk x x) = false := rfl

@[simp] theorem walkPar_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkPar G δ (.cons h p) = (decide (s(u, v) ∈ δ)).xor (walkPar G δ p) := rfl

variable {G δ}


theorem walkPar_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    walkPar G δ (p.append q) = (walkPar G δ p).xor (walkPar G δ q) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [SimpleGraph.Walk.cons_append, ih]



theorem walkPar_reverse {x y : V} (p : G.Walk x y) :
    walkPar G δ p.reverse = walkPar G δ p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkPar_append, ih, walkPar_cons,
      show walkPar G δ (SimpleGraph.Walk.cons h p)
        = (decide (s(u, v) ∈ δ)).xor (walkPar G δ p) from rfl]
    have hedge : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [walkPar_nil, hedge, Bool.xor_false]
    cases walkPar G δ p <;> cases hb : decide (s(u, v) ∈ δ) <;> simp [Bool.xor_comm]



@[simp] theorem walkPar_singleton {x y : V} (h : G.Adj x y) :
    walkPar G δ (SimpleGraph.Walk.cons h (.nil : G.Walk y y)) = decide (s(x, y) ∈ δ) := by
  simp

end WalkParity









section Cocycle

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {δ : Finset (Sym2 V)}

variable (G δ) in



def EvenOnAllCycles : Prop := ∀ (x : V) (p : G.Walk x x), walkPar G δ p = false




theorem walkPar_eq_of_evenOnAllCycles (hev : EvenOnAllCycles G δ) {x y : V}
    (p q : G.Walk x y) : walkPar G δ p = walkPar G δ q := by
  have hclosed : walkPar G δ (p.append q.reverse) = false := hev _ _
  rw [walkPar_append, walkPar_reverse] at hclosed
  revert hclosed
  cases walkPar G δ p <;> cases walkPar G δ q <;> simp

end Cocycle







section Disagree

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]




def disagree (c : V → Bool) : Finset (Sym2 V) :=
  G.edgeFinset.filter
    (fun e => Sym2.lift ⟨fun x y => decide (c x ≠ c y),
      by intro x y; rw [decide_eq_decide]; exact ne_comm⟩ e)

variable {G}

omit [DecidableEq V] in


theorem mem_disagree_iff (c : V → Bool) {x y : V} (h : G.Adj x y) :
    s(x, y) ∈ disagree G c ↔ c x ≠ c y := by
  unfold disagree
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h2⟩; exact of_decide_eq_true h2
  · intro hne
    exact ⟨by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact h,
      decide_eq_true hne⟩

omit [DecidableEq V] in

theorem disagree_subset_edgeFinset (c : V → Bool) : disagree G c ⊆ G.edgeFinset :=
  Finset.filter_subset _ _

end Disagree









section Handshake

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]





theorem walkPar_disagree_eq_xor (c : V → Bool) {x y : V} (p : G.Walk x y) :
    walkPar G (disagree G c) p = (c x).xor (c y) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkPar_cons, ih]
    have hdecne : ∀ a b : Bool, decide (a ≠ b) = a.xor b := by
      intro a b; cases a <;> cases b <;> simp
    have hedge : decide (s(u, v) ∈ disagree G c) = (c u).xor (c v) := by
      rw [decide_eq_decide.mpr (mem_disagree_iff c h), hdecne]
    rw [hedge]
    
    set a := c u; set b := c v; set d := c w
    cases a <;> cases b <;> cases d <;> rfl





theorem disagree_evenOnAllCycles (c : V → Bool) :
    EvenOnAllCycles G (disagree G c) := by
  intro x p
  rw [walkPar_disagree_eq_xor c p]
  cases c x <;> rfl

end Handshake









section ParityProp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (δ : Finset (Sym2 V))




noncomputable def parityProp (hG : G.Preconnected) (v₀ : V) : V → Bool :=
  fun v => walkPar G δ (hG v₀ v).some

variable {G δ}

omit [Fintype V] [DecidableRel G.Adj] in




theorem parityProp_adj_xor (hev : EvenOnAllCycles G δ) (hG : G.Preconnected) (v₀ : V)
    {x y : V} (h : G.Adj x y) :
    (parityProp G δ hG v₀ x).xor (parityProp G δ hG v₀ y) = decide (s(x, y) ∈ δ) := by
  let px : G.Walk v₀ x := (hG v₀ x).some
  let walkVy : G.Walk v₀ y := px.append (SimpleGraph.Walk.cons h (.nil : G.Walk y y))
  have hpar : parityProp G δ hG v₀ y = walkPar G δ walkVy :=
    walkPar_eq_of_evenOnAllCycles hev (hG v₀ y).some walkVy
  have hwalkVy : walkPar G δ walkVy
      = (parityProp G δ hG v₀ x).xor (decide (s(x, y) ∈ δ)) := by
    rw [walkPar_append, walkPar_singleton]; rfl
  rw [hpar, hwalkVy]
  cases parityProp G δ hG v₀ x <;> cases hb : decide (s(x, y) ∈ δ) <;> simp










theorem disagree_parityProp (hev : EvenOnAllCycles G δ) (hG : G.Preconnected) (v₀ : V)
    (hδ : δ ⊆ G.edgeFinset) :
    disagree G (parityProp G δ hG v₀) = δ := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · 
      intro he
      have hadj : G.Adj x y := by
        have := disagree_subset_edgeFinset (parityProp G δ hG v₀) he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      have hne : (parityProp G δ hG v₀) x ≠ (parityProp G δ hG v₀) y :=
        (mem_disagree_iff (parityProp G δ hG v₀) hadj).mp he
      have hxor : (parityProp G δ hG v₀ x).xor (parityProp G δ hG v₀ y) = true := by
        cases hx : parityProp G δ hG v₀ x <;> cases hy : parityProp G δ hG v₀ y <;>
          simp_all
      rw [parityProp_adj_xor hev hG v₀ hadj] at hxor
      exact of_decide_eq_true hxor
    · 
      intro he
      have hadj : G.Adj x y := by
        have := hδ he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      rw [mem_disagree_iff (parityProp G δ hG v₀) hadj]
      have hxor := parityProp_adj_xor hev hG v₀ hadj
      rw [decide_eq_true he] at hxor
      cases hx : parityProp G δ hG v₀ x <;> cases hy : parityProp G δ hG v₀ y <;>
        simp_all




theorem exists_disagree_eq_of_evenOnAllCycles [Nonempty V] (hG : G.Preconnected)
    (hδ : δ ⊆ G.edgeFinset) (hev : EvenOnAllCycles G δ) :
    ∃ c : V → Bool, disagree G c = δ := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  exact ⟨parityProp G δ hG v₀, disagree_parityProp hev hG v₀ hδ⟩






theorem evenOnAllCycles_iff_exists_disagree [Nonempty V] (hG : G.Preconnected)
    (hδ : δ ⊆ G.edgeFinset) :
    EvenOnAllCycles G δ ↔ ∃ c : V → Bool, disagree G c = δ := by
  constructor
  · intro hev; exact exists_disagree_eq_of_evenOnAllCycles hG hδ hev
  · rintro ⟨c, rfl⟩; exact disagree_evenOnAllCycles c

end ParityProp

end StatMech.Walls
