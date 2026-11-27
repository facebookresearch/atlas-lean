/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-!
# Refutation of Jaeger's modular orientation conjecture

This is the `p = 3` instance of Han, Li, Wu and Zhang, *Counterexamples to Jaeger's Circular Flow
Conjecture*, J. Combin. Theory Ser. B **131** (2018), 1–11, §3, pp. 4–7.
The construction uses an odd wheel with two-terminal gadgets in place of its rim links.
The obstruction is proved using signed divergences; cut sizes are bounded by decomposing a cut
among the spokes and individual gadgets.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.JaegerModularOrientationWanted

/-! Source record `OPG-130`.

We represent a finite undirected multigraph by finite types of vertices and edges together with
two endpoint maps. The endpoint order is only a reference orientation: `isReversed` below chooses
an orientation independently for each edge. This representation allows parallel edges and loops.
-/

/-- **Edges crossing a cut.** Consider a multigraph with vertex set $V$ and edge set $E$ in which
each edge has a first and a second endpoint. For a set $S \subseteq V$, an edge crosses the cut at
$S$ when exactly one of its two endpoints lies in $S$. -/
def CrossesCut {V E : Type} (end₁ end₂ : E → V) (S : Set V) (e : E) : Prop :=
  (end₁ e ∈ S ∧ end₂ e ∉ S) ∨ (end₁ e ∉ S ∧ end₂ e ∈ S)

/-- **Size of a cut.** Consider a multigraph with finitely many edges in which each edge has a
first and a second endpoint. For a set $S$ of vertices, the size of the cut at $S$ is the number
of edges crossing it, that is, having exactly one endpoint in $S$. Distinct parallel edges are
counted separately. -/
noncomputable def cutSize {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (S : Set V) : ℕ := by
  classical
  exact (Finset.univ.filter (CrossesCut end₁ end₂ S)).card

/-- **4k-edge-connected multigraphs.** For a natural number $k$, a finite multigraph is
$4k$-edge-connected when it has at least two vertices and, for every set $S$ of vertices such that
both $S$ and its complement are nonempty, at least $4k$ edges cross the cut at $S$, that is, have
exactly one endpoint in $S$. Parallel edges are counted separately. For $k \ge 1$ the condition
implies that the multigraph is connected.
-/
noncomputable def IsFourKEdgeConnected {V E : Type} [Fintype V] [Fintype E]
    (k : ℕ) (end₁ end₂ : E → V) : Prop :=
  2 ≤ Fintype.card V ∧
    ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → 4 * k ≤ cutSize end₁ end₂ S

/-- **Tail of an oriented edge.** Each edge $e$ of the multigraph has a reference direction from
its first endpoint to its second endpoint, and an orientation chooses for each edge whether to
reverse it. The tail of $e$ is its first endpoint if $e$ is not reversed and its second endpoint
if $e$ is reversed. -/
def orientedTail {V E : Type} (end₁ end₂ : E → V)
    (isReversed : E → Bool) (e : E) : V :=
  if isReversed e = true then end₂ e else end₁ e

/-- **Head of an oriented edge.** Each edge $e$ of the multigraph has a reference direction from
its first endpoint to its second endpoint, and an orientation chooses for each edge whether to
reverse it. The head of $e$ is its second endpoint if $e$ is not reversed and its first endpoint
if $e$ is reversed. -/
def orientedHead {V E : Type} (end₁ end₂ : E → V)
    (isReversed : E → Bool) (e : E) : V :=
  if isReversed e = true then end₁ e else end₂ e

/-- **Indegree.** In a multigraph with finitely many edges and a chosen orientation, the
indegree of a vertex $v$ is the number of edges whose head is $v$, parallel edges counted
separately. -/
noncomputable def indegree {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (isReversed : E → Bool) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => orientedHead end₁ end₂ isReversed e = v)).card

/-- **Outdegree.** In a multigraph with finitely many edges and a chosen orientation, the
outdegree of a vertex $v$ is the number of edges whose tail is $v$, parallel edges counted
separately. -/
noncomputable def outdegree {V E : Type} [Fintype E]
    (end₁ end₂ : E → V) (isReversed : E → Bool) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => orientedTail end₁ end₂ isReversed e = v)).card

/-- **Modular orientations.** For a natural number $k$, an orientation of a multigraph with
finitely many edges is a modulo $(2k+1)$ orientation when at every vertex the indegree minus the
outdegree is congruent to $0$ modulo $2k + 1$. -/
noncomputable def IsModularOrientation {V E : Type} [Fintype E]
    (k : ℕ) (end₁ end₂ : E → V) (isReversed : E → Bool) : Prop :=
  ∀ v : V,
    (indegree end₁ end₂ isReversed v : ZMod (2 * k + 1)) -
        (outdegree end₁ end₂ isReversed v : ZMod (2 * k + 1)) = 0

/-- **Jaeger's modular orientation conjecture.** This is the statement that for every integer
$k \ge 1$, every finite multigraph (loops and parallel edges allowed) that has at least two
vertices, and in which every partition of the vertices into two nonempty sets is crossed by at
least $4k$ edges, admits an orientation of its edges in which, at every vertex, the indegree minus
the outdegree is divisible by $2k + 1$.

The parameter $k$ is positive, as in the source discussion of $(2 + 1/k)$-flows and its
specializations at $k = 1$ and $k = 2$.
-/
def conjecture : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∀ (V E : Type) [Fintype V] [Fintype E] (end₁ end₂ : E → V),
      IsFourKEdgeConnected k end₁ end₂ →
        ∃ isReversed : E → Bool, IsModularOrientation k end₁ end₂ isReversed

end MathlibExt.Combinatorics.JaegerModularOrientationWanted

end

open scoped BigOperators

namespace HanLiWuZhang

open MathlibExt.Combinatorics.JaegerModularOrientationWanted

/-! ### Signed divergence and cuts -/

private def mark {V : Type} [DecidableEq V] (x v : V) : ℤ := if x = v then 1 else 0

private def sign (b : Bool) : ℤ := if b then -1 else 1

private theorem sign_cases (b : Bool) : sign b = 1 ∨ sign b = -1 := by cases b <;> decide

private theorem sign_bounds (b : Bool) : -1 ≤ sign b ∧ sign b ≤ 1 := by cases b <;> decide

private def tally {E : Type} [Fintype E] (f : E → ℤ) : ℤ := ∑ e, f e

private def divg {V E : Type} [DecidableEq V] [Fintype E]
    (a b : E → V) (w : E → ℤ) (v : V) : ℤ :=
  tally fun e ↦ (mark (a e) v - mark (b e) v) * w e

private def deg {V E : Type} [DecidableEq V] [Fintype E] (a b : E → V) (v : V) : ℤ :=
  tally fun e ↦ mark (a e) v + mark (b e) v

private theorem mark_sum {V : Type} [Fintype V] [DecidableEq V] (v : V) : (∑ x, mark v x) = 1 := by
  simp [mark]

private theorem divg_total {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (a b : E → V) (w : E → ℤ) : (∑ v, divg a b w v) = 0 := by
  unfold divg tally
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, Finset.sum_sub_distrib, mark_sum, sub_self, zero_mul,
    Finset.sum_const_zero]

private theorem tally_sub {E : Type} [Fintype E] (f g : E → ℤ) :
    tally (fun e ↦ f e - g e) = tally f - tally g := Finset.sum_sub_distrib _ _

private theorem tally_add {E : Type} [Fintype E] (f g : E → ℤ) :
    tally (fun e ↦ f e + g e) = tally f + tally g := Finset.sum_add_distrib

private theorem tally_sum {I E : Type} [Fintype I] [Fintype E] (f : I × E → ℤ) :
    tally f = ∑ i, tally fun e ↦ f (i, e) := Fintype.sum_prod_type _

private theorem tally_split {E F : Type} [Fintype E] [Fintype F] (f : E ⊕ F → ℤ) :
    tally f = tally (f ∘ Sum.inl) + tally (f ∘ Sum.inr) := Fintype.sum_sum_type _

private theorem tally_congr {E : Type} [Fintype E] {f g : E → ℤ}
    (h : ∀ e, f e = g e) : tally f = tally g := congrArg tally (funext h)

private theorem tally_le {E : Type} [Fintype E] {f g : E → ℤ}
    (h : ∀ e, f e ≤ g e) : tally f ≤ tally g := Finset.sum_le_sum (fun e _ ↦ h e)

-- Use private unfold lemmas to avoid exporting generated equations for the legacy API.
private theorem tail_def {V E : Type} (a b : E → V) (r : E → Bool) (e : E) :
    orientedTail a b r e = (if r e = true then b e else a e) := rfl

private theorem head_def {V E : Type} (a b : E → V) (r : E → Bool) (e : E) :
    orientedHead a b r e = (if r e = true then a e else b e) := rfl

private theorem crosses_def {V E : Type} (a b : E → V) (S : Set V) (e : E) :
    CrossesCut a b S e ↔ (a e ∈ S ∧ b e ∉ S) ∨ (a e ∉ S ∧ b e ∈ S) := Iff.rfl

private theorem deg_divg {V E : Type} [DecidableEq V] [Fintype E]
    (a b : E → V) (r : E → Bool) (v : V) :
    ∃ A B : ℤ, 0 ≤ A ∧ 0 ≤ B ∧ deg a b v = A + B ∧ divg a b (sign ∘ r) v = A - B := by
  let f e := mark (orientedTail a b r e) v
  let g e := mark (orientedHead a b r e) v
  refine ⟨tally f, tally g, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun e _ ↦ by simp only [f, mark]; split <;> decide
  · exact Finset.sum_nonneg fun e _ ↦ by simp only [g, mark]; split <;> decide
  · rw [← tally_add]
    apply tally_congr
    intro e
    cases h : r e <;> simp [f, g, head_def, tail_def, h, add_comm]
  · rw [← tally_sub]
    apply tally_congr
    intro e
    cases h : r e <;> simp [f, g, head_def, tail_def, sign, h]

private theorem tally_indicator {E : Type} [Fintype E] (P : E → Prop) [DecidablePred P] :
    tally (fun e ↦ if P e then 1 else 0) = ((Finset.univ.filter P).card : ℤ) := by
  unfold tally
  rw [Finset.sum_ite]
  simp

private theorem tally_mark {V E : Type} [DecidableEq V] [Fintype E]
    (f : E → V) (v : V) [dec : DecidablePred (fun e ↦ f e = v)] :
    tally (fun e ↦ mark (f e) v) = ((Finset.univ.filter (fun e ↦ f e = v)).card : ℤ) := by
  rw [← tally_indicator]
  apply tally_congr
  intro e
  by_cases he : f e = v <;> simp [mark, he]

private theorem divg_is_out_sub_in {V E : Type} [DecidableEq V] [Fintype E]
    (a b : E → V) (r : E → Bool) (v : V) :
    divg a b (sign ∘ r) v = (outdegree a b r v : ℤ) - indegree a b r v := by
  have ht : tally (fun e ↦ mark (orientedTail a b r e) v) = (outdegree a b r v : ℤ) :=
    tally_mark (orientedTail a b r) v (dec := Classical.decPred _)
  have hh : tally (fun e ↦ mark (orientedHead a b r e) v) = (indegree a b r v : ℤ) :=
    tally_mark (orientedHead a b r) v (dec := Classical.decPred _)
  rw [← ht, ← hh, ← tally_sub]
  apply tally_congr
  intro e
  cases h : r e <;> simp [head_def, tail_def, sign, h]

private theorem modular_divg {V E : Type} [DecidableEq V] [Fintype E]
    {a b : E → V} {r : E → Bool} (h : IsModularOrientation 3 a b r) (v : V) :
    (divg a b (sign ∘ r) v : ZMod 7) = 0 := by
  rw [divg_is_out_sub_in, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  exact sub_eq_zero.mpr (sub_eq_zero.mp (h v)).symm

private theorem dvd_seven {d : ℤ} (h : (d : ZMod 7) = 0) : (7 : ℤ) ∣ d :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd d 7).1 h

private theorem odd_bounded_modular {D A B : ℤ} (ha : 0 ≤ A) (hb : 0 ≤ B)
    (h₁ : A + B = 11 ∨ A + B = 13 ∨ A + B = 7) (h₂ : D = A - B)
    (hm : (D : ZMod 7) = 0) : D = 7 ∨ D = -7 := by
  obtain ⟨z, hz⟩ := dvd_seven hm
  omega

private def cutTerm (a b : Bool) : ℤ := if a ≠ b then 1 else 0

private def countCut {V E : Type} [Fintype E] (a b : E → V) (c : V → Bool) : ℤ :=
  tally fun e ↦ cutTerm (c (a e)) (c (b e))

private theorem cutTerm_nonneg (a b : Bool) : 0 ≤ cutTerm a b := by cases a <;> cases b <;> decide

private theorem countCut_nonneg {V E : Type} [Fintype E] (a b : E → V) (c : V → Bool) :
    0 ≤ countCut a b c := Finset.sum_nonneg fun _ _ ↦ cutTerm_nonneg _ _

private theorem bool_cut {V E : Type} [Fintype E] (a b : E → V) (c : V → Bool) :
    countCut a b c = (cutSize a b {v | c v = true} : ℤ) := by
  classical
  unfold countCut cutTerm cutSize
  rw [tally_indicator]
  have h : (Finset.univ.filter fun e ↦ c (a e) ≠ c (b e)) =
      Finset.univ.filter (CrossesCut a b {v | c v = true}) := by
    ext e
    cases ha : c (a e) <;> cases hb : c (b e) <;> simp [crosses_def, ha, hb]
  rw [h]

private theorem mark_color {V : Type} [Fintype V] [DecidableEq V] (c : V → Bool) (x : V) :
    (∑ v ∈ Finset.univ.filter (fun v ↦ c v = true), mark x v) = if c x then 1 else 0 := by
  simp [mark]

private theorem cut_divg_le {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (a b : E → V) (r : E → Bool) (c : V → Bool) :
    (∑ v ∈ Finset.univ.filter (fun v ↦ c v = true), divg a b (sign ∘ r) v) ≤ countCut a b c := by
  unfold divg tally countCut
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, mark_color, mark_color]
  cases ha : c (a e) <;> cases hb : c (b e) <;> cases hr : r e <;>
    simp_all [sign, cutTerm]

/-! ### The core: a complete graph with two extra triangles (G₁) -/

private abbrev Core := Fin 12
private abbrev Complete := {e : Core × Core // e.1 < e.2}
private abbrev Triangle := Fin 2 × Fin 3
private abbrev CoreEdge := Complete ⊕ Triangle

private def trianglePoint (j : Fin 2) (i : Fin 3) : Core :=
  ⟨3 * j.val + i.val, by omega⟩

private def coreA : CoreEdge → Core
  | .inl e => e.val.1
  | .inr (j, i) => trianglePoint j i

private def coreB : CoreEdge → Core
  | .inl e => e.val.2
  | .inr (j, i) => trianglePoint j (i + 1)

private def last (v : Fin 6) : Core := v.natAdd 6

private theorem core_deg (v : Core) : deg coreA coreB v = if v.val < 6 then 13 else 11 := by
  revert v
  decide +kernel

private def count (c : Core → Bool) : ℕ := (Finset.univ.filter fun v ↦ c v = true).card

private def completeCut_equiv (c : Core → Bool) :
    {e : Complete // c e.val.1 ≠ c e.val.2} ≃
      {v : Core // c v = true} × {v : Core // c v = false} := by
  let f (e : {e : Complete // c e.val.1 ≠ c e.val.2}) :
      {v : Core // c v = true} × {v : Core // c v = false} :=
    if h : c e.val.val.1 = true then
      (⟨e.val.val.1, h⟩, ⟨e.val.val.2, by
        have hn := e.property
        change c e.val.val.1 ≠ c e.val.val.2 at hn
        cases he : c e.val.val.2 <;> simp_all⟩)
    else (⟨e.val.val.2, by
      have hn := e.property
      change c e.val.val.1 ≠ c e.val.val.2 at hn
      cases h₁ : c e.val.val.1 <;> cases h₂ : c e.val.val.2 <;> simp_all⟩,
      ⟨e.val.val.1, by cases he : c e.val.val.1 <;> simp_all⟩)
  let g (p : {v : Core // c v = true} × {v : Core // c v = false}) :
      {e : Complete // c e.val.1 ≠ c e.val.2} :=
    if h : p.1.val < p.2.val then ⟨⟨(p.1.val, p.2.val), h⟩, by simp [p.1.property, p.2.property]⟩
    else ⟨⟨(p.2.val, p.1.val), by
      have hn : p.1.val ≠ p.2.val := by
        intro he
        have hp := p.1.property
        rw [he, p.2.property] at hp
        contradiction
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hn)⟩,
      by simp [p.1.property, p.2.property]⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    have hx := x.val.property
    have hc := x.property
    dsimp at hx hc
    have hn : ¬ x.val.val.2 < x.val.val.1 := not_lt_of_ge (le_of_lt hx)
    apply Subtype.ext
    apply Subtype.ext
    dsimp [f, g]
    split <;> simp_all
  · intro p
    apply Prod.ext <;> apply Subtype.ext
    all_goals
      have hp := p.1.property
      have hq := p.2.property
      dsimp [f, g]
      split <;> simp_all

private theorem complete_cut (c : Core → Bool) :
    (tally fun e : Complete ↦ cutTerm (c e.val.1) (c e.val.2)) =
      (count c : ℤ) * (12 - (count c : ℤ)) := by
  unfold cutTerm
  rw [tally_indicator, ← Fintype.card_subtype]
  rw [Fintype.card_congr (completeCut_equiv c), Fintype.card_prod]
  have hc : Fintype.card {v : Core // c v = true} = count c := Fintype.card_subtype _
  have hsum :
      Fintype.card {v : Core // c v = true} + Fintype.card {v : Core // c v = false} = 12 := by
    have hbool (v : Core) : (¬ c v = true) ↔ c v = false := by cases c v <;> decide
    have e : {v : Core // ¬ c v = true} ≃ {v : Core // c v = false} := Equiv.subtypeEquivRight hbool
    rw [← Fintype.card_congr e, Fintype.card_subtype_compl]
    have hc' : Fintype.card {v : Core // c v = true} ≤ 12 := by
      simpa using Fintype.card_subtype_le (fun v : Core ↦ c v = true)
    simp only [Fintype.card_fin]
    omega
  rw [Int.natCast_mul, hc]
  have hr : (Fintype.card {v : Core // c v = false} : ℤ) = 12 - (count c : ℤ) := by
    rw [hc] at hsum
    omega
  rw [hr]

private theorem triangle_cut (c : Fin 3 → Bool) :
    (tally fun i : Fin 3 ↦ cutTerm (c i) (c (i + 1))) ≤ 2 := by
  revert c
  decide +kernel

private theorem core_cut (c : Core → Bool) :
    countCut coreA coreB c ≤ (count c : ℤ) * (12 - (count c : ℤ)) + 4 := by
  unfold countCut
  rw [tally_split]
  change (tally fun e : Complete ↦ cutTerm (c e.val.1) (c e.val.2)) +
    (tally fun e : Triangle ↦ cutTerm (c (trianglePoint e.1 e.2))
      (c (trianglePoint e.1 (e.2 + 1)))) ≤ _
  rw [complete_cut, tally_sum, Fin.sum_univ_two]
  have h₀ := triangle_cut (c ∘ trianglePoint 0)
  have h₁ := triangle_cut (c ∘ trianglePoint 1)
  change tally (fun i : Fin 3 ↦
    cutTerm (c (trianglePoint 0 i)) (c (trianglePoint 0 (i + 1)))) ≤ 2 at h₀
  change tally (fun i : Fin 3 ↦
    cutTerm (c (trianglePoint 1 i)) (c (trianglePoint 1 (i + 1)))) ≤ 2 at h₁
  change (_ : ℤ) +
    (tally (fun i : Fin 3 ↦ cutTerm (c (trianglePoint 0 i)) (c (trianglePoint 0 (i + 1)))) +
    tally (fun i : Fin 3 ↦ cutTerm (c (trianglePoint 1 i)) (c (trianglePoint 1 (i + 1))))) ≤ _
  omega

private theorem core_impossible (r : CoreEdge → Bool)
    (hm : ∀ v : Core, (divg coreA coreB (sign ∘ r) v : ZMod 7) = 0) : False := by
  let D := divg coreA coreB (sign ∘ r)
  let c : Core → Bool := fun v ↦ decide (D v = 7)
  have hd (v : Core) : D v = 7 ∨ D v = -7 := by
    obtain ⟨A, B, ha, hb, hdeg, hd⟩ := deg_divg coreA coreB r v
    apply odd_bounded_modular ha hb _ hd (hm v)
    rw [core_deg] at hdeg
    split at hdeg <;> omega
  have he (v : Core) : D v = (if c v = true then 7 else -7) := by
    rcases hd v with hp | hn
    · simp [c, hp]
    · simp [c, hn]
  have ht : (∑ v : Core, D v) = 0 := divg_total _ _ _
  have ht' : (∑ v : Core, (if c v = true then 7 else -7 : ℤ)) = 0 := by
    simpa only [← he] using ht
  rw [Finset.sum_ite] at ht'
  simp only [Finset.sum_const, nsmul_eq_mul] at ht'
  have hc' := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Core))
    (p := fun v ↦ c v = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc'
  have hc : count c = 6 := by unfold count; omega
  have hs := cut_divg_le coreA coreB r c
  have hp : (∑ v ∈ Finset.univ.filter (fun v ↦ c v = true), D v) = 42 := by
    calc
      _ = ∑ _v ∈ Finset.univ.filter (fun v ↦ c v = true), (7 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [he, ite_eq_left (Finset.mem_filter.1 hv).2]
      _ = 42 := by
        simpa [Finset.sum_const, nsmul_eq_mul, count] using congrArg (fun n : ℕ ↦ (n : ℤ) * 7) hc
  change (∑ v ∈ Finset.univ.filter (fun v ↦ c v = true), D v) ≤ _ at hs
  rw [hp] at hs
  have hcub := core_cut c
  rw [hc] at hcub
  omega

/-! ### Add two terminals to the core (G₂) -/

private abbrev Gate := Core ⊕ Bool
private abbrev Attachment := Bool × Fin 6
private abbrev GateEdge := CoreEdge ⊕ (Attachment ⊕ Unit)

private def attach (z : Bool) (i : Fin 6) : GateEdge := .inr (.inl (z, i))
private def bridge : GateEdge := .inr (.inr ())

private def gateA : GateEdge → Gate
  | .inl e => .inl (coreA e)
  | .inr (.inl (z, _)) => .inr z
  | .inr (.inr ()) => .inr false

private def gateB : GateEdge → Gate
  | .inl e => .inl (coreB e)
  | .inr (.inl (_, i)) => .inl (last i)
  | .inr (.inr ()) => .inr true

private theorem tally_bool {f : Bool → ℤ} : tally f = f false + f true := by
  simp [tally, add_comm]

private theorem tally_unit {f : Unit → ℤ} : tally f = f () := by simp [tally]

private theorem tally_gate (f : GateEdge → ℤ) : tally f =
    tally (f ∘ Sum.inl) + ((tally (f ∘ attach false) + tally (f ∘ attach true)) + f bridge) := by
  rw [tally_split f, tally_split (f ∘ Sum.inr), tally_sum, tally_unit]
  change tally (f ∘ Sum.inl) + (tally (fun z : Bool ↦ tally (f ∘ attach z)) + f bridge) = _
  rw [tally_bool]

private theorem gate_core_div (w : GateEdge → ℤ) (v : Core) :
    divg gateA gateB w (.inl v) = divg coreA coreB (w ∘ Sum.inl) v -
      tally (fun i : Fin 6 ↦ mark (last i) v * (w (attach false i) + w (attach true i))) := by
  let f (e : GateEdge) := (mark (gateA e) (.inl v) - mark (gateB e) (.inl v)) * w e
  change tally f = _
  rw [tally_gate f]
  have hcore : tally (f ∘ Sum.inl) = divg coreA coreB (w ∘ Sum.inl) v := by
    apply tally_congr
    intro e
    simp [f, gateA, gateB, mark]
  have hbridge : f bridge = 0 := by simp [f, gateA, gateB, bridge, mark]
  have hside (z : Bool) : tally (f ∘ attach z) =
      -(tally fun i : Fin 6 ↦ mark (last i) v * w (attach z i)) := by
    rw [show -(tally fun i : Fin 6 ↦ mark (last i) v * w (attach z i)) =
      (tally fun i : Fin 6 ↦ -(mark (last i) v * w (attach z i)))
      from (Finset.sum_neg_distrib _).symm]
    apply tally_congr
    intro i
    simp [f, gateA, gateB, attach, mark]
  rw [hcore, hbridge, hside, hside]
  simp only [mul_add, tally_add]
  omega

private theorem gate_terminal_div (w : GateEdge → ℤ) (z : Bool) :
    divg gateA gateB w (.inr z) = tally (fun i : Fin 6 ↦ w (attach z i)) + sign z * w bridge := by
  unfold divg
  rw [tally_gate]
  cases z <;> simp [gateA, gateB, mark, sign, attach, bridge, tally]

private theorem extreme_gate (u : Fin 6 → ℤ) (t D : ℤ) (hu : ∀ i, -1 ≤ u i ∧ u i ≤ 1)
    (ht : t = 1 ∨ t = -1) (hD : D = tally u + t) (hM : (D : ZMod 7) = 0)
    (hodd : ∃ a, tally u = 2 * a) : ∀ i, u i = t := by
  obtain ⟨k, hk⟩ := dvd_seven hM
  have hul : -6 ≤ tally u := by
    simpa [tally] using (tally_le (f := fun _ : Fin 6 ↦ -1) (fun i ↦ (hu i).1))
  have hur : tally u ≤ 6 := by
    simpa [tally] using (tally_le (g := fun _ : Fin 6 ↦ 1) (fun i ↦ (hu i).2))
  have hs : tally u = 6 * t := by omega
  let residual (i : Fin 6) : ℤ := 1 - t * u i
  have hn (i : Fin 6) : 0 ≤ residual i := by
    obtain ⟨hl, hr⟩ := hu i
    rcases ht with h | h <;> simp [residual, h] <;> omega
  have hz : tally residual = 0 := by
    dsimp [residual]
    rw [tally_sub]
    simp only [tally, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    change 6 - t * tally u = 0
    rw [hs]
    rcases ht with h | h <;> simp [h]
  intro i
  have he : residual i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hn j)).1 hz i (by simp)
  rcases ht with h | h <;> simp [residual, h] at he ⊢ <;> omega

private theorem tally_sign_even (r : Fin 6 → Bool) : ∃ a : ℤ, tally (sign ∘ r) = 2 * a := by
  let f (i : Fin 6) : ℤ := if r i then -1 else 0
  refine ⟨3 + tally f, ?_⟩
  have h : tally (sign ∘ r) = tally (fun i ↦ 1 + 2 * f i) := by
    apply tally_congr
    intro i
    cases h : r i <;> simp [sign, f, h]
  rw [h,tally_add]
  simp only [tally, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  omega

private theorem gate_impossible (r : GateEdge → Bool)
    (hm : ∀ v : Gate, (divg gateA gateB (sign ∘ r) v : ZMod 7) = 0) : False := by
  let w := sign ∘ r
  let t := w bridge
  have h₀ (i : Fin 6) : w (attach false i) = t := by
    apply extreme_gate _ _ _ (fun i ↦ sign_bounds _) (sign_cases _) ?_ (hm (.inr false))
      (tally_sign_even (r ∘ attach false))
    simpa [w, t, sign] using gate_terminal_div w false
  have h₁ (i : Fin 6) : w (attach true i) = -t := by
    have ht : -t = 1 ∨ -t = -1 := by rcases sign_cases (r bridge) with h | h <;> simp [w, t, h]
    apply extreme_gate _ _ _ (fun i ↦ sign_bounds _) ht ?_ (hm (.inr true))
      (tally_sign_even (r ∘ attach true))
    change divg gateA gateB w (.inr true) = tally (fun i : Fin 6 ↦ w (attach true i)) + -t
    simpa only [show sign true = -1 from rfl, neg_one_mul, t] using gate_terminal_div w true
  apply core_impossible (r ∘ Sum.inl)
  intro v
  have h := gate_core_div w v
  have hz :
      tally (fun i : Fin 6 ↦ mark (last i) v * (w (attach false i) + w (attach true i))) = 0 := by
    simp [h₀, h₁, tally]
  rw [hz, sub_zero] at h
  change (divg coreA coreB (w ∘ Sum.inl) v : ZMod 7) = 0
  rw [← h]
  exact hm (.inl v)

private theorem gate_terminal_residues (r : GateEdge → Bool)
    (hm : ∀ v : Core, (divg gateA gateB (sign ∘ r) (.inl v) : ZMod 7) = 0) :
    let L : ZMod 7 := ↑(divg gateA gateB (sign ∘ r) (.inr false))
    let R : ZMod 7 := ↑(divg gateA gateB (sign ∘ r) (.inr true))
    L ≠ 0 ∧ L + R = 0 := by
  let D := divg gateA gateB (sign ∘ r)
  have h := divg_total gateA gateB (sign ∘ r)
  change tally D = 0 at h
  rw [tally_split, tally_bool] at h
  have hsum : (↑(tally (D ∘ (Sum.inl : Core → Gate))) : ZMod 7) = 0 := by
    simp only [tally, Int.cast_sum]
    exact Finset.sum_eq_zero (fun v _ ↦ hm v)
  have h' := congrArg (fun x : ℤ ↦ (x : ZMod 7)) h
  simp only [Function.comp_apply, Int.cast_add, Int.cast_zero] at h'
  rw [hsum, zero_add] at h'
  refine ⟨?_, h'⟩
  intro hL
  change (D (.inr false) : ZMod 7) = 0 at hL
  have hR : (D (.inr true) : ZMod 7) = 0 := by simpa [hL] using h'
  apply gate_impossible r
  rintro (v | z)
  · exact hm v
  · cases z
    · exact hL
    · exact hR

/-! ### Cut bounds inside G₂ -/

private theorem gate_cut_decomp (c : Gate → Bool) :
    countCut gateA gateB c = countCut coreA coreB (c ∘ Sum.inl) +
      (tally (fun i : Fin 6 ↦ cutTerm (c (.inr false)) (c (.inl (last i))) +
        cutTerm (c (.inr true)) (c (.inl (last i)))) +
        cutTerm (c (.inr false)) (c (.inr true))) := by
  unfold countCut
  rw [tally_gate, tally_add]
  rfl

private theorem split_gate_cut (c : Gate → Bool) (h : c (.inr false) ≠ c (.inr true)) :
    7 ≤ countCut gateA gateB c := by
  rw [gate_cut_decomp]
  have hb (v : Bool) : cutTerm (c (.inr false)) v + cutTerm (c (.inr true)) v = 1 := by
    cases h₀ : c (.inr false) <;> cases h₁ : c (.inr true) <;> cases v <;> simp_all [cutTerm]
  have hsum : tally (fun i : Fin 6 ↦ cutTerm (c (.inr false)) (c (.inl (last i))) +
      cutTerm (c (.inr true)) (c (.inl (last i)))) = 6 := by
    simp [hb, tally]
  rw [hsum]
  have hn := countCut_nonneg coreA coreB (c ∘ Sum.inl)
  simp [cutTerm, h]
  omega

private theorem gate_loopless (e : GateEdge) : gateA e ≠ gateB e := by
  revert e
  decide +kernel

private theorem gate_core_degree (v : Core) : deg gateA gateB (.inl v) = 13 := by
  revert v
  decide +kernel

private theorem col_flip (a b z : Bool) :
    cutTerm a b = cutTerm (a != z) (b != z) := by cases a <;> cases b <;> cases z <;> decide

private theorem gate_complete_lower (c : Gate → Bool) (z : Bool) :
    (count (fun v ↦ c (.inl v) != z) : ℤ) * (12 - (count (fun v ↦ c (.inl v) != z) : ℤ)) ≤
      countCut coreA coreB (c ∘ Sum.inl) := by
  rw [countCut, tally_split, ← complete_cut]
  have h : (tally fun e : Complete ↦ cutTerm (c (.inl e.val.1) != z) (c (.inl e.val.2) != z)) =
      tally ((fun e : CoreEdge ↦ cutTerm (c (.inl (coreA e))) (c (.inl (coreB e)))) ∘ Sum.inl) := by
    apply tally_congr
    intro e
    exact (col_flip (c (.inl e.val.1)) (c (.inl e.val.2)) z).symm
  rw [h]
  have hb : 0 ≤ tally ((fun e : CoreEdge ↦
      cutTerm (c (.inl (coreA e))) (c (.inl (coreB e)))) ∘ Sum.inr) :=
    Finset.sum_nonneg (fun _ _ ↦ cutTerm_nonneg _ _)
  simpa only [Function.comp_apply] using le_add_of_nonneg_right hb

private theorem single_gate_cut (c : Gate → Bool) (z : Bool) (v : Core)
    (hs : ∀ x : Gate, c x ≠ z ↔ x = .inl v) : countCut gateA gateB c = 13 := by
  rw [← gate_core_degree v]
  apply tally_congr
  intro e
  have ha := hs (gateA e)
  have hb := hs (gateB e)
  have he := gate_loopless e
  cases hz : z <;> cases h₁ : c (gateA e) <;> cases h₂ : c (gateB e) <;>
    simp_all [cutTerm, mark]

private theorem count_le (d : Core → Bool) : count d ≤ 12 := by
  simpa [count] using Finset.card_filter_le (Finset.univ : Finset Core) (fun v ↦ d v = true)

private theorem count_full (d : Core → Bool) (h : count d = 12) (v : Core) : d v = true := by
  have he : (Finset.univ.filter fun v ↦ d v = true) = (Finset.univ : Finset Core) := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa [count] using ge_of_eq h
  have hv : v ∈ Finset.univ.filter (fun x ↦ d x = true) := by rw [he]; simp
  exact (Finset.mem_filter.1 hv).2

private theorem last_ne : last 0 ≠ last 1 := by decide

private theorem count_le_of_two_false (d : Core → Bool) (h₀ : d (last 0) = false)
    (h₁ : d (last 1) = false) : count d ≤ 10 := by
  have hi : (Finset.univ.filter fun v ↦ d v = true) ⊆
      ((Finset.univ : Finset Core).erase (last 0)).erase (last 1) := by
    intro v hv
    have hd := (Finset.mem_filter.1 hv).2
    have hn₀ : v ≠ last 0 := by intro h; rw [h, h₀] at hd; contradiction
    have hn₁ : v ≠ last 1 := by intro h; rw [h, h₁] at hd; contradiction
    simp [Finset.mem_erase, hn₀, hn₁]
  have h := Finset.card_le_card hi
  have hm : last 1 ∈ (Finset.univ : Finset Core).erase (last 0) := by
    simp [Finset.mem_erase, Ne.symm last_ne]
  simpa [count, Finset.card_erase_of_mem hm,
    Finset.card_erase_of_mem (Finset.mem_univ (last 0))] using h

private theorem same_gate_cut (c : Gate → Bool) (z : Bool)
    (h₀ : c (.inr false) = z) (h₁ : c (.inr true) = z) (hcore : ∃ v : Core, c (.inl v) ≠ z) :
    12 ≤ countCut gateA gateB c := by
  let d : Core → Bool := fun v ↦ c (.inl v) != z
  let s := count d
  have hs : 1 ≤ s := by
    obtain ⟨v, hv⟩ := hcore
    apply Finset.card_pos.mpr
    exact ⟨v, by simp [d, hv]⟩
  have hsle := count_le d
  change s ≤ 12 at hsle
  have hl := gate_complete_lower c z
  change (s : ℤ) * (12 - (s : ℤ)) ≤ countCut coreA coreB (c ∘ Sum.inl) at hl
  have hn := countCut_nonneg coreA coreB (c ∘ Sum.inl)
  have hc (v : Core) : cutTerm z (c (.inl v)) = if d v then 1 else 0 := by
    cases hc : c (.inl v) <;> cases z <;> simp_all [cutTerm, d]
  let A := countCut coreA coreB (c ∘ Sum.inl)
  let B := tally fun i : Fin 6 ↦ (if d (last i) then (1 : ℤ) else 0)
  have heq : countCut gateA gateB c = A + 2 * B := by
    rw [gate_cut_decomp]
    simp only [h₀, h₁, hc, show cutTerm z z = 0 from by simp [cutTerm], add_zero, tally_add]
    change A + (B + B) = A + 2 * B
    omega
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ by split <;> decide
  by_cases hsmall : s = 1
  · let T : Finset Core := Finset.univ.filter fun v ↦ d v = true
    have ht : T.card = 1 := hsmall
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp ht
    have hsingle (x : Gate) : c x ≠ z ↔ x = .inl v := by
      cases x with
      | inl x =>
        have ht₁ : x ∈ T ↔ c (.inl x) ≠ z := by simp [T, d]
        rw [← ht₁, hv]
        simp
      | inr x => cases x <;> simp [h₀, h₁]
    rw [single_gate_cut c z v hsingle]
    decide
  by_cases hfull : s = 12
  · have hB' : B = 6 := by
      simp only [B, count_full d hfull, ↓reduceIte, tally, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    rw [heq, hB']
    change 0 ≤ A at hn
    omega
  by_cases hlarge : s = 11
  · have hlast : ∃ j : Fin 6, d (last j) = true := by
      by_contra nh
      push Not at nh
      have hfalse (i : Fin 6) : d (last i) = false := by cases h : d (last i) <;> simp_all
      have h := count_le_of_two_false d (hfalse 0) (hfalse 1)
      change s ≤ 10 at h
      omega
    obtain ⟨j, hj⟩ := hlast
    have hj' : 1 ≤ B := by
      have h := Finset.single_le_sum (f := fun i : Fin 6 ↦ if d (last i) then (1 : ℤ) else 0)
        (fun i _ ↦ by split <;> decide) (Finset.mem_univ j)
      simpa [B, tally, hj] using h
    rw [heq]
    change (s : ℤ) * (12 - (s : ℤ)) ≤ A at hl
    rw [hlarge] at hl
    omega
  have h2 : (2 : ℤ) ≤ (s : ℤ) := by omega
  have h10 : (s : ℤ) ≤ 10 := by omega
  have hm : 20 ≤ (s : ℤ) * (12 - (s : ℤ)) := by
    have hh := mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h10)
    nlinarith
  change (s : ℤ) * (12 - (s : ℤ)) ≤ A at hl
  rw [heq]
  omega

/-! ### The odd wheel obstruction -/

private abbrev Rim := ZMod 13

private theorem shift_sum (f : Rim → ℤ) : (∑ i, f (i + 1)) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.addRight 1) f

private theorem odd_wheel (w s : Rim → ℤ) (hw : ∀ i, -5 ≤ w i ∧ w i ≤ 5 ∧ w i % 2 = 1)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hm : ∀ i, ((w i - w (i - 1) + s i : ℤ) : ZMod 7) = 0) : False := by
  let D (i : Rim) := w i - w (i - 1) + s i
  have hd (i : Rim) : D i = 7 ∨ D i = -7 := by
    obtain ⟨h₁, h₂, h₃⟩ := hw i
    obtain ⟨h₄, h₅, h₆⟩ := hw (i - 1)
    obtain ⟨z, hz⟩ := dvd_seven (hm i)
    have hs' := hs i
    dsimp only [D]
    omega
  have hsub (i : Rim) : i + 1 - 1 = i := add_sub_cancel_right _ _
  have hd_pair (i : Rim) : D i + D (i + 1) = 0 := by
    have h₁ := (hw (i + 1)).1
    have h₂ := (hw (i + 1)).2.1
    have h₃ := (hw (i - 1)).1
    have h₄ := (hw (i - 1)).2.1
    have h₅ := hs i
    have h₆ := hs (i + 1)
    have hh₁ := hd i
    have hh₂ := hd (i + 1)
    have hh : D i + D (i + 1) = w (i + 1) - w (i - 1) + s i + s (i + 1) := by
      dsimp only [D]
      rw [hsub]
      omega
    omega
  have hz : (∑ i : Rim, D i) = 0 := by
    have h : (∑ i : Rim, (D i + D (i + 1))) = 0 := Finset.sum_eq_zero (fun i _ ↦ hd_pair i)
    rw [Finset.sum_add_distrib, shift_sum] at h
    omega
  have he (i : Rim) : D i = if D i = 7 then 7 else -7 := by
    rcases hd i with hp | hn
    · simp [hp]
    · simp [hn]
  have hh : (∑ i : Rim, (if D i = 7 then 7 else -7 : ℤ)) = 0 := by
    simpa only [← he] using hz
  rw [Finset.sum_ite] at hh
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Rim))
    (p := fun i ↦ D i = 7)
  rw [Finset.card_univ, ZMod.card] at hc
  omega

private theorem rim_const_of_no_jump (c : Rim → Bool) (h : ∀ i, c i = c (i + 1)) (i : Rim) :
    c i = c 0 := by
  have H (n : ℕ) : c (n : Rim) = c 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, ← h (n : Rim), ih]
  simpa using H i.val

private theorem rim_two_jumps (c : Rim → Bool) (i : Rim) (hi : c i ≠ c (i + 1)) :
    ∃ j : Rim, j ≠ i ∧ c j ≠ c (j + 1) := by
  by_contra h
  push Not at h
  let f (j : Rim) : ℤ := (c j).toNat
  have hh : ∑ j : Rim, (f j - f (j + 1)) = 0 := by
    rw [Finset.sum_sub_distrib, shift_sum, sub_self]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [f, h j hji]) (by simp)] at hh
  have hf : f i = f (i + 1) := by omega
  exact hi (by
    cases h₀ : c i <;> cases h₁ : c (i + 1) <;> simp_all [f])

private theorem residue_representative (z : ZMod 7) (hz : z ≠ 0) :
    ∃ j : Fin 6, ((2 * (j.val : ℤ) - 5 : ℤ) : ZMod 7) = z := by
  revert z
  decide +kernel

/-! ### Replace the rim links by copies of G₂ -/

private abbrev Vertex := Option Rim ⊕ (Rim × Core)
private abbrev Edge := Rim ⊕ (Rim × GateEdge)

private def hub : Vertex := .inl none
private def rim (i : Rim) : Vertex := .inl (some i)
private def inner (i : Rim) (v : Core) : Vertex := .inr (i, v)

/-- Attach terminal `false` to rim point `i`, and terminal `true` to its successor. -/
private def embed (i : Rim) : Gate → Vertex
  | .inl v => inner i v
  | .inr false => rim i
  | .inr true => rim (i + 1)

private theorem rim_ne_succ (i : Rim) : i ≠ i + 1 := by
  intro h
  have he : (0 : Rim) = 1 := add_left_cancel (a := i) (by simpa only [add_zero] using h)
  exact (by decide : (0 : Rim) ≠ 1) he

private theorem embed_inj (i : Rim) : Function.Injective (embed i) := by
  rintro (v | z) (v' | z') h
  · simpa [embed, inner] using h
  · cases z' <;> simp [embed, inner, rim] at h
  · cases z <;> simp [embed, inner, rim] at h
  · cases z <;> cases z' <;> simp_all [embed, rim, show (1 : Rim) ≠ 0 by decide]

private def endA : Edge → Vertex
  | .inl i => rim i
  | .inr (i, e) => embed i (gateA e)

private def endB : Edge → Vertex
  | .inl _ => hub
  | .inr (i, e) => embed i (gateB e)

private def localSign (r : Edge → Bool) (i : Rim) : GateEdge → Bool := fun e ↦ r (.inr (i, e))
private def spokeSign (r : Edge → Bool) (i : Rim) : ℤ := sign (r (.inl i))
private def localDiv (r : Edge → Bool) (i : Rim) (v : Gate) : ℤ :=
  divg gateA gateB (sign ∘ localSign r i) v

private theorem tally_rim_edges (f : Edge → ℤ) : tally f =
    (tally fun i : Rim ↦ f (.inl i)) + ∑ i : Rim, (tally fun e : GateEdge ↦ f (.inr (i, e))) := by
  rw [tally_split f, tally_sum]
  rfl

private theorem div_split (r : Edge → Bool) (v : Vertex) : divg endA endB (sign ∘ r) v =
    (tally (fun i : Rim ↦ (mark (rim i) v - mark hub v) * spokeSign r i)) +
      ∑ i : Rim, divg (embed i ∘ gateA) (embed i ∘ gateB) (sign ∘ localSign r i) v := by
  unfold divg
  rw [tally_rim_edges]
  rfl

private theorem div_embed (i : Rim) (w : GateEdge → ℤ) (v : Gate) :
    divg (embed i ∘ gateA) (embed i ∘ gateB) w (embed i v) = divg gateA gateB w v := by
  apply tally_congr
  intro e
  simp [mark, (embed_inj i).eq_iff]

private theorem div_off (i : Rim) (w : GateEdge → ℤ) (v : Vertex)
    (h : ∀ u : Gate, embed i u ≠ v) : divg (embed i ∘ gateA) (embed i ∘ gateB) w v = 0 := by
  simp [divg, mark, h, tally]

private theorem core_global_div (r : Edge → Bool) (i : Rim) (v : Core) :
    divg endA endB (sign ∘ r) (inner i v) = localDiv r i (.inl v) := by
  rw [div_split]
  have hs : (tally fun j : Rim ↦
      (mark (rim j) (inner i v) - mark hub (inner i v)) * spokeSign r j) = 0 := by
    simp [tally, mark, rim, inner, hub]
  rw [hs, zero_add, Finset.sum_eq_single i]
  · exact div_embed i _ (.inl v)
  · intro j _ hj
    apply div_off
    rintro (u | z)
    · simp [embed, inner, hj]
    · cases z <;> simp [embed, rim, inner]
  · simp

private theorem rim_global_div (r : Edge → Bool) (i : Rim) :
    divg endA endB (sign ∘ r) (rim i) =
      spokeSign r i + localDiv r i (.inr false) + localDiv r (i - 1) (.inr true) := by
  rw [div_split]
  have hs : (tally fun j : Rim ↦ (mark (rim j) (rim i) - mark hub (rim i)) * spokeSign r j) =
      spokeSign r i := by
    simp [tally, mark, rim, hub]
  rw [hs]
  let F (j : Rim) := divg (embed j ∘ gateA) (embed j ∘ gateB) (sign ∘ localSign r j) (rim i)
  have hp : i - 1 + 1 = i := sub_add_cancel _ _
  have hne : i ≠ i - 1 := by
    intro h
    have hh := rim_ne_succ (i - 1)
    exact hh (h.symm.trans hp.symm)
  have hF (j : Rim) : F j =
      (if j = i then localDiv r i (.inr false) else 0) +
        (if j = i - 1 then localDiv r (i - 1) (.inr true) else 0) := by
    by_cases hji : j = i
    · subst j
      simp only [hne, ↓reduceIte, add_zero]
      exact div_embed i (sign ∘ localSign r i) (.inr false)
    by_cases hjp : j = i - 1
    · subst j
      simp only [Ne.symm hne, ↓reduceIte, zero_add]
      have hp' : embed (i - 1) (.inr true) = rim i := congrArg rim hp
      have hd := div_embed (i - 1) (sign ∘ localSign r (i - 1)) (.inr true)
      rw [hp'] at hd
      exact hd
    rw [ite_eq_right hji, ite_eq_right hjp, add_zero]
    apply div_off
    rintro (v | z)
    · simp [embed, inner, rim]
    · cases z
      · simp [embed, rim, hji]
      · have hh : j + 1 ≠ i := by
          intro h
          exact hjp (eq_sub_of_add_eq h)
        simp [embed, rim, hh]
  change spokeSign r i + (∑ j : Rim, F j) = _
  simp only [hF, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  omega

private theorem no_modular_orientation (r : Edge → Bool) :
    ¬ IsModularOrientation 3 endA endB r := by
  intro h
  have hCore (i : Rim) (v : Core) : (localDiv r i (.inl v) : ZMod 7) = 0 := by
    rw [← core_global_div]
    exact modular_divg h (inner i v)
  have hTerms (i : Rim) : (localDiv r i (.inr false) : ZMod 7) ≠ 0 ∧
      (localDiv r i (.inr false) : ZMod 7) + (localDiv r i (.inr true) : ZMod 7) = 0 :=
    gate_terminal_residues (localSign r i) (hCore i)
  classical
  choose j hj using fun i : Rim ↦ residue_representative (localDiv r i (.inr false)) (hTerms i).1
  let w (i : Rim) : ℤ := 2 * (j i).val - 5
  apply odd_wheel w (spokeSign r)
  · intro i
    have hb := (j i).isLt
    dsimp [w]
    omega
  · exact fun i ↦ sign_cases (r (.inl i))
  · intro i
    have hm := modular_divg h (rim i)
    rw [rim_global_div] at hm
    simp only [Int.cast_add] at hm
    have hR : (localDiv r (i - 1) (.inr true) : ZMod 7) = -(w (i - 1) : ZMod 7) := by
      have ht := (hTerms (i - 1)).2
      rw [← hj (i - 1)] at ht
      exact eq_neg_of_add_eq_zero_right ht
    rw [Int.cast_add, Int.cast_sub, show (w i : ZMod 7) = _ from hj i, sub_eq_add_neg, ← hR]
    simpa only [add_comm (spokeSign r i : ZMod 7), add_assoc, add_left_comm, add_comm] using hm

/-! ### Twelve-edge-connectivity of the constructed graph -/

private theorem global_cut_decomp (c : Vertex → Bool) : countCut endA endB c =
    (tally fun i : Rim ↦ cutTerm (c (rim i)) (c hub)) +
      ∑ i : Rim, countCut gateA gateB (c ∘ embed i) := by
  unfold countCut
  rw [tally_rim_edges]
  rfl

private theorem local_ge_zero (c : Vertex → Bool) (i : Rim) :
    0 ≤ countCut gateA gateB (c ∘ embed i) := countCut_nonneg _ _ _

private theorem global_cut_lower (c : Vertex → Bool) (h : ∃ v : Vertex, c v ≠ c (rim 0)) :
    12 ≤ countCut endA endB c := by
  let z := c (rim 0)
  let Q (i : Rim) := countCut gateA gateB (c ∘ embed i)
  let S := tally fun i : Rim ↦ cutTerm (c (rim i)) (c hub)
  have hQ (i : Rim) : 0 ≤ Q i := local_ge_zero c i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ cutTerm_nonneg _ _)
  rw [global_cut_decomp]
  change 12 ≤ S + ∑ i, Q i
  by_cases hr : ∀ i : Rim, c (rim i) = c (rim (i + 1))
  · have hrim (i : Rim) : c (rim i) = z := rim_const_of_no_jump (c ∘ rim) hr i
    by_cases hhub : c hub = z
    · obtain ⟨v, hv⟩ := h
      have hv' : c v ≠ z := hv
      rcases v with (o | ⟨i, v⟩)
      · cases o with
        | none => exact False.elim (hv' hhub)
        | some j => exact False.elim (hv' (hrim j))
      have hi : 12 ≤ Q i := same_gate_cut (c ∘ embed i) z (hrim i) (hrim (i + 1)) ⟨v, hv'⟩
      have hsum : Q i ≤ ∑ j, Q j := Finset.single_le_sum (fun j _ ↦ hQ j) (Finset.mem_univ i)
      omega
    · have hsp : S = 13 := by
        change tally (fun i : Rim ↦ cutTerm (c (rim i)) (c hub)) = _
        have hb : cutTerm z (c hub) = 1 := by simp [cutTerm, Ne.symm hhub]
        simp only [hrim, hb, tally, Finset.sum_const, Finset.card_univ, ZMod.card,
          nsmul_eq_mul, Nat.cast_ofNat, mul_one]
      have hNon : 0 ≤ ∑ i : Rim, Q i := Finset.sum_nonneg fun i _ ↦ hQ i
      omega
  · push Not at hr
    obtain ⟨i, hi⟩ := hr
    obtain ⟨j, hji, hj⟩ := rim_two_jumps (c ∘ rim) i hi
    have hi' : 7 ≤ Q i := split_gate_cut (c ∘ embed i) hi
    have hj' : 7 ≤ Q j := split_gate_cut (c ∘ embed j) hj
    have hsum : Q i + Q j ≤ ∑ l, Q l := by
      have hh : (∑ l ∈ ({i, j} : Finset Rim), Q l) ≤ ∑ l, Q l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ ↦ hQ l)
      simpa [Finset.sum_pair (Ne.symm hji)] using hh
    omega

private theorem twelve_connected : IsFourKEdgeConnected 3 endA endB := by
  refine ⟨?_, ?_⟩
  · have h : Fintype.card Vertex = 170 := by decide +kernel
    omega
  · intro A hA hAc
    classical
    let c (v : Vertex) := decide (v ∈ A)
    have he : {v : Vertex | c v = true} = A := by ext v; simp [c]
    have hne : ∃ v : Vertex, c v ≠ c (rim 0) := by
      by_cases hb : rim 0 ∈ A
      · obtain ⟨v, hv⟩ := hAc
        exact ⟨v, by simp [c, hb, show v ∉ A from hv]⟩
      · obtain ⟨v, hv⟩ := hA
        exact ⟨v, by simp [c, hb, hv]⟩
    have h := global_cut_lower c hne
    rw [bool_cut, he] at h
    omega

end HanLiWuZhang

namespace MathlibExt.Combinatorics.JaegerModularOrientationWanted

/-- **Jaeger's modular orientation conjecture is false.** There exist an integer $k \ge 1$ and a
finite multigraph (loops and parallel edges allowed) with at least two vertices, in which every
partition of the vertices into two nonempty sets is crossed by at least $4k$ edges, such that no
orientation of the edges makes the indegree minus the outdegree of every vertex divisible by
$2k + 1$.

Han, Li, Wu and Zhang (J. Combin. Theory Ser. B 131 (2018) 1-11) construct, for every $k \ge 3$,
a $4k$-edge-connected graph with no circular $(2+1/k)$-flow, equivalently no modulo $(2k+1)$
orientation; the cases $k = 1$ (Tutte's 3-flow conjecture) and $k = 2$ remain open.

Source: Daniel W. Cranston and Jiaao Li, Circular flows in planar graphs, SIAM J. Discrete
Math. (2020), arXiv:1812.09833, https://arxiv.org/abs/1812.09833. Moved from
`OpenConjectures/Combinatorics/JaegerModularOrientation`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨r, hr⟩ := h 3 (by decide) HanLiWuZhang.Vertex HanLiWuZhang.Edge
    HanLiWuZhang.endA HanLiWuZhang.endB HanLiWuZhang.twelve_connected
  exact HanLiWuZhang.no_modular_orientation r hr

end MathlibExt.Combinatorics.JaegerModularOrientationWanted
