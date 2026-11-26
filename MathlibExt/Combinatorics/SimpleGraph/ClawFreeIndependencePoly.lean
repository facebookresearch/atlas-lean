/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
Real-rootedness of the independence polynomial of a claw-free graph
(Chudnovsky–Seymour theorem), via half-plane stability of a weighted
independence sum.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Claw-free finite graph.** A simple graph $G$ on a finite vertex set $V$ is claw-free if it
has no induced claw $K_{1,3}$: there are no vertices $c, \ell_1, \ell_2, \ell_3 \in V$ such that
$\ell_1, \ell_2, \ell_3$ are pairwise distinct, each is adjacent to $c$ and different from $c$,
and no two of them are adjacent.

Source: Moussa Benoumhani, "On the Modes of the Independence Polynomial of
the Centipede," Journal of Integer Sequences 15 (2012), Article 12.5.1,
unnumbered Chudnovsky–Seymour theorem, lines 142–144,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Benoumhani/benoumhani8.tex
quoting M. Chudnovsky and P. Seymour, "The roots of the independence
polynomial of a clawfree graph," J. Combin. Theory Ser. B 97 (2007), 350–357
(biblio lines 499–501). -/
public def clawFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ¬ ∃ c l₁ l₂ l₃ : V, c ≠ l₁ ∧ c ≠ l₂ ∧ c ≠ l₃ ∧ l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    G.Adj c l₁ ∧ G.Adj c l₂ ∧ G.Adj c l₃ ∧ ¬ G.Adj l₁ l₂ ∧ ¬ G.Adj l₁ l₃ ∧ ¬ G.Adj l₂ l₃

open Classical in
public noncomputable def independencePoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Polynomial ℤ :=
  Finset.sum (Finset.range (Fintype.card V + 1)) (fun k =>
    ((Finset.univ.filter
      (fun s : Finset V => s.card = k ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b)).card : ℤ) •
      Polynomial.X ^ k)

end

/-! ## Private helpers: weighted independence sum and claw-free analysis -/

open Classical in
/-- Independence predicate: all distinct members of `J` are non-adjacent. -/
private def cfIndep {V : Type*} (G : SimpleGraph V) (J : Finset V) : Prop :=
  ∀ a ∈ J, ∀ b ∈ J, a ≠ b → ¬ G.Adj a b

open Classical in
/-- Weighted independence sum: `∑ J ⊆ S, [indep J] ∏ x ∈ J, w x * z`. -/
private noncomputable def cfZ {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ)
    (S : Finset V) (z : ℂ) : ℂ :=
  ∑ J ∈ S.powerset, (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * z) else 0)

open Classical in
/-- `S` minus the closed neighbourhood of `v`. -/
private noncomputable def cfDel {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (v : V) : Finset V :=
  S.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)

/-- Claw-freeness relativized to a finset, in positive form. -/
private noncomputable def cfClawFreeOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ c ∈ S, ∀ a ∈ S, ∀ b ∈ S, ∀ d ∈ S, G.Adj c a → G.Adj c b → G.Adj c d →
    a ≠ b → a ≠ d → b ≠ d → G.Adj a b ∨ G.Adj a d ∨ G.Adj b d

open Classical in
/-- Private neighbours of `u` (w.r.t. `v`): adjacent to `u`, not to `v`. -/
private noncomputable def cfPrivA {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  S.filter (fun x => G.Adj u x ∧ x ≠ v ∧ ¬ G.Adj v x)

open Classical in
/-- Private neighbours of `v` (w.r.t. `u`). -/
private noncomputable def cfPrivB {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  S.filter (fun x => G.Adj v x ∧ x ≠ u ∧ ¬ G.Adj u x)

open Classical in
/-- Vertices of `S` outside both closed neighbourhoods. -/
private noncomputable def cfR {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  S.filter (fun x => (x ≠ u ∧ ¬ G.Adj u x) ∧ (x ≠ v ∧ ¬ G.Adj v x))

/-- Contracted vertex set `R ∪ A ∪ B`. -/
private noncomputable def cfS' {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (u v : V) : Finset V :=
  cfR G S u v ∪ cfPrivA G S u v ∪ cfPrivB G S u v

/-- Contracted graph: add all edges between `A` and `B`. -/
private noncomputable def cfContract {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromRel (fun x y => x ∈ A ∧ y ∈ B)

open Classical in
/-- Rescaled weight for the contraction: `B` scaled by `s/(s+t)`, `A` by `t/(s+t)`. -/
private noncomputable def cfW {V : Type*} [DecidableEq V] (w : V → ℝ)
    (A B : Finset V) (s t : ℝ) : V → ℝ :=
  fun x => if x ∈ B then (s / (s + t)) * w x
    else if x ∈ A then (t / (s + t)) * w x else w x

/-- The upper half-plane plus the point `1`. -/
private def cfD : Set ℂ := {z : ℂ | 0 < z.im} ∪ {1}

/-- Vertex recurrence for the weighted independence sum. -/
private lemma cf_vertex_recurrence {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : V → ℝ) (S : Finset V) (v : V) (hv : v ∈ S) (z : ℂ) :
    cfZ G w S z = cfZ G w (S.erase v) z + (w v : ℂ) * z * cfZ G w (cfDel G S v) z := by
  classical
  have hne : v ∉ S.erase v := Finset.notMem_erase v S
  have hSu : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
  have hJnotmem : ∀ J ∈ (S.erase v).powerset, v ∉ J := by
    intro J hJ hmem
    exact hne ((Finset.mem_powerset.mp hJ) hmem)
  have hindep_insert : ∀ J ∈ (S.erase v).powerset,
      cfIndep G (insert v J) ↔ (cfIndep G J ∧ ∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b) := by
    intro J hJ
    constructor
    · intro h
      refine ⟨fun a ha b hb hne2 => h a (Finset.mem_insert_of_mem ha) b
        (Finset.mem_insert_of_mem hb) hne2, fun b hb => ?_⟩
      refine ⟨(fun heq : b = v => hJnotmem J hJ (heq ▸ hb)), ?_⟩
      exact h v (Finset.mem_insert_self v J) b (Finset.mem_insert_of_mem hb)
        (fun heq : v = b => hJnotmem J hJ (heq.symm ▸ hb))
    · rintro ⟨hJ', hav⟩ a ha b hb hne2
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hne2
      · exact (hav b hb).2
      · exact fun hadj => (hav a ha).2 hadj.symm
      · exact hJ' a ha b hb hne2
  have hprod : ∀ J ∈ (S.erase v).powerset,
      ∏ x ∈ insert v J, ((w x : ℂ) * z)
        = ((w v : ℂ) * z) * ∏ x ∈ J, ((w x : ℂ) * z) := by
    intro J hJ
    exact Finset.prod_insert (hJnotmem J hJ)
  have hT1 : ∀ J ∈ (S.erase v).powerset,
      (if cfIndep G (insert v J) then ∏ x ∈ insert v J, ((w x : ℂ) * z) else 0) =
      (w v : ℂ) * z * (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
        then ∏ x ∈ J, ((w x : ℂ) * z) else 0) := by
    intro J hJ
    by_cases h1 : cfIndep G (insert v J)
    · by_cases h2 : cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
      · have e1 : (if cfIndep G (insert v J)
            then ∏ x ∈ insert v J, ((w x : ℂ) * z) else 0) =
            ∏ x ∈ insert v J, ((w x : ℂ) * z) := ite_eq_left h1
        have e2 : (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
            then ∏ x ∈ J, ((w x : ℂ) * z) else 0) =
            ∏ x ∈ J, ((w x : ℂ) * z) := ite_eq_left h2
        rw [e1, e2, hprod J hJ]
      · exact False.elim (h2 ((hindep_insert J hJ).mp h1))
    · by_cases h2 : cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
      · exact False.elim (h1 ((hindep_insert J hJ).mpr h2))
      · have e1 : (if cfIndep G (insert v J)
            then ∏ x ∈ insert v J, ((w x : ℂ) * z) else 0) = (0 : ℂ) :=
            ite_eq_right h1
        have e2 : (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
            then ∏ x ∈ J, ((w x : ℂ) * z) else 0) = (0 : ℂ) := ite_eq_right h2
        rw [e1, e2, mul_zero]
  have hsub : cfDel G S v ⊆ S.erase v := by
    intro x hx
    simp only [cfDel, Finset.mem_filter] at hx
    exact Finset.mem_erase.mpr ⟨hx.2.1, hx.1⟩
  have hU : ∀ J ∈ (S.erase v).powerset, J ∉ (cfDel G S v).powerset →
      (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
        then ∏ x ∈ J, ((w x : ℂ) * z) else 0) = 0 := by
    intro J hJ hJD
    have e0 : (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
        then ∏ x ∈ J, ((w x : ℂ) * z) else 0) = (0 : ℂ) := by
      apply ite_eq_right
      intro hcon
      apply hJD
      rw [Finset.mem_powerset]
      intro b hb
      have hbE : b ∈ S.erase v := (Finset.mem_powerset.mp hJ) hb
      have hbS : b ∈ S := Finset.mem_of_mem_erase hbE
      simp only [cfDel, Finset.mem_filter]
      exact ⟨hbS, hcon.2 b hb⟩
    exact e0
  have hU2 : ∀ T ∈ (cfDel G S v).powerset,
      (if cfIndep G T ∧ (∀ b ∈ T, b ≠ v ∧ ¬ G.Adj v b)
        then ∏ x ∈ T, ((w x : ℂ) * z) else 0) =
      (if cfIndep G T then ∏ x ∈ T, ((w x : ℂ) * z) else 0) := by
    intro T hT
    have hTD : T ⊆ cfDel G S v := Finset.mem_powerset.mp hT
    have hav : ∀ b ∈ T, b ≠ v ∧ ¬ G.Adj v b := by
      intro b hb
      have hbD := hTD hb
      simp only [cfDel, Finset.mem_filter] at hbD
      exact hbD.2
    by_cases h1 : cfIndep G T ∧ (∀ b ∈ T, b ≠ v ∧ ¬ G.Adj v b)
    · by_cases h2 : cfIndep G T
      · have e1 : (if cfIndep G T ∧ (∀ b ∈ T, b ≠ v ∧ ¬ G.Adj v b)
            then ∏ x ∈ T, ((w x : ℂ) * z) else 0) =
            ∏ x ∈ T, ((w x : ℂ) * z) := ite_eq_left h1
        have e2 : (if cfIndep G T then ∏ x ∈ T, ((w x : ℂ) * z) else 0) =
            ∏ x ∈ T, ((w x : ℂ) * z) := ite_eq_left h2
        rw [e1, e2]
      · exact False.elim (h2 h1.1)
    · by_cases h2 : cfIndep G T
      · exact False.elim (h1 ⟨h2, hav⟩)
      · have e1 : (if cfIndep G T ∧ (∀ b ∈ T, b ≠ v ∧ ¬ G.Adj v b)
            then ∏ x ∈ T, ((w x : ℂ) * z) else 0) = (0 : ℂ) := ite_eq_right h1
        have e2 : (if cfIndep G T then ∏ x ∈ T, ((w x : ℂ) * z) else 0) = (0 : ℂ) :=
          ite_eq_right h2
        rw [e1, e2]
  have hsplit : cfZ G w (insert v (S.erase v)) z =
      cfZ G w (S.erase v) z + (∑ J ∈ (S.erase v).powerset,
        (if cfIndep G (insert v J) then ∏ x ∈ insert v J, ((w x : ℂ) * z) else 0)) := by
    simp only [cfZ]
    exact Finset.sum_powerset_insert hne _
  have hsum : (∑ J ∈ (S.erase v).powerset,
        (if cfIndep G (insert v J) then ∏ x ∈ insert v J, ((w x : ℂ) * z) else 0)) =
      (w v : ℂ) * z * cfZ G w (cfDel G S v) z := by
    have e1 : (∑ J ∈ (S.erase v).powerset,
          (if cfIndep G (insert v J) then ∏ x ∈ insert v J, ((w x : ℂ) * z) else 0)) =
        (w v : ℂ) * z * (∑ J ∈ (S.erase v).powerset,
          (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
            then ∏ x ∈ J, ((w x : ℂ) * z) else 0)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun J hJ => hT1 J hJ)
    have e2 : (∑ J ∈ (S.erase v).powerset,
          (if cfIndep G J ∧ (∀ b ∈ J, b ≠ v ∧ ¬ G.Adj v b)
            then ∏ x ∈ J, ((w x : ℂ) * z) else 0)) =
        cfZ G w (cfDel G S v) z := by
      simp only [cfZ]
      rw [← Finset.sum_subset (Finset.powerset_mono.mpr hsub)
        (fun J hJ hJD => hU J hJ hJD)]
      exact Finset.sum_congr rfl (fun T hT => hU2 T hT)
    rw [e1, e2]
  conv_lhs => rw [hSu, hsplit, hsum]

/-- Base case: the sum over the empty set is `1`. -/
private lemma cf_empty_Z {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ)
    (z : ℂ) : cfZ G w ∅ z = 1 := by
  classical
  have hindep : cfIndep G ∅ := fun a ha => absurd ha (Finset.notMem_empty a)
  simp only [cfZ, Finset.powerset_empty, Finset.sum_singleton]
  rw [show (if cfIndep G ∅ then ∏ x ∈ (∅ : Finset V), ((w x : ℂ) * z) else 0) =
    ∏ x ∈ (∅ : Finset V), ((w x : ℂ) * z) from ite_eq_left hindep, Finset.prod_empty]

/-- `cfZ` depends only on the graph restricted to `S` and weights on `S`. -/
private lemma cf_congr {V : Type*} [DecidableEq V] (G₁ G₂ : SimpleGraph V) (w₁ w₂ : V → ℝ)
    (S : Finset V) (z : ℂ)
    (hadj : ∀ x ∈ S, ∀ y ∈ S, (G₁.Adj x y ↔ G₂.Adj x y))
    (hw : ∀ x ∈ S, w₁ x = w₂ x) :
    cfZ G₁ w₁ S z = cfZ G₂ w₂ S z := by
  classical
  simp only [cfZ]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJsub : J ⊆ S := Finset.mem_powerset.mp hJ
  have hindep : cfIndep G₁ J ↔ cfIndep G₂ J := by
    constructor
    · intro h a ha b hb hne hbadj
      exact h a ha b hb hne ((hadj a (hJsub ha) b (hJsub hb)).mpr hbadj)
    · intro h a ha b hb hne hbadj
      exact h a ha b hb hne ((hadj a (hJsub ha) b (hJsub hb)).mp hbadj)
  by_cases h1 : cfIndep G₁ J
  · by_cases h2 : cfIndep G₂ J
    · have e1 : (if cfIndep G₁ J then ∏ x ∈ J, ((w₁ x : ℂ) * z) else 0) =
          ∏ x ∈ J, ((w₁ x : ℂ) * z) := ite_eq_left h1
      have e2 : (if cfIndep G₂ J then ∏ x ∈ J, ((w₂ x : ℂ) * z) else 0) =
          ∏ x ∈ J, ((w₂ x : ℂ) * z) := ite_eq_left h2
      rw [e1, e2]
      apply Finset.prod_congr rfl
      intro x hx
      rw [hw x (hJsub hx)]
    · exact False.elim (h2 (hindep.mp h1))
  · by_cases h2 : cfIndep G₂ J
    · exact False.elim (h1 (hindep.mpr h2))
    · have e1 : (if cfIndep G₁ J then ∏ x ∈ J, ((w₁ x : ℂ) * z) else 0) = (0 : ℂ) :=
        ite_eq_right h1
      have e2 : (if cfIndep G₂ J then ∏ x ∈ J, ((w₂ x : ℂ) * z) else 0) = (0 : ℂ) :=
        ite_eq_right h2
      rw [e1, e2]

/-- Corollary: changing the weight outside `S` does not change `cfZ`. -/
private lemma cf_congr_update_outside {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : V → ℝ) (S : Finset V) (z : ℂ) (v : V) (hv : v ∉ S) (r : ℝ) :
    cfZ G (Function.update w v r) S z = cfZ G w S z := by
  refine cf_congr _ _ _ _ _ _ (fun x _ y _ => Iff.rfl) ?_
  intro x hx
  exact Function.update_of_ne (fun heq : x = v => hv (heq ▸ hx)) r w

/-- Corollary: `cfDel` depends only on pairs `(x, y)` with `y ∈ S`. -/
private lemma cfDel_congr {V : Type*} [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    (S : Finset V) (x : V)
    (hadj : ∀ y ∈ S, (G₁.Adj x y ↔ G₂.Adj x y)) :
    cfDel G₁ S x = cfDel G₂ S x := by
  ext y
  simp only [cfDel, Finset.mem_filter]
  constructor
  · rintro ⟨hS, hne, hnadj⟩
    exact ⟨hS, hne, fun h => hnadj ((hadj y hS).mpr h)⟩
  · rintro ⟨hS, hne, hnadj⟩
    exact ⟨hS, hne, fun h => hnadj ((hadj y hS).mp h)⟩

/-- `cfZ` is continuous in `z`. -/
private lemma cf_continuous {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ)
    (S : Finset V) : Continuous (fun z => cfZ G w S z) := by
  classical
  simp only [cfZ]
  refine continuous_finsetSum _ (fun J _ => ?_)
  by_cases hJ : cfIndep G J
  · have heq : (fun z => (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * z) else 0)) =
        (fun z => ∏ x ∈ J, ((w x : ℂ) * z)) :=
      funext fun z => ite_eq_left hJ
    rw [heq]
    refine continuous_finsetProd _ (fun x _ => ?_)
    exact continuous_const.mul continuous_id
  · have heq : (fun z => (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * z) else (0 : ℂ))) =
        (fun _ => (0 : ℂ)) :=
      funext fun z => ite_eq_right hJ
    rw [heq]
    exact continuous_const

/-- At `z = 1` with nonnegative weights, `cfZ` is a real number `≥ 1`. -/
private lemma cf_at_one {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ)
    (S : Finset V) (hpos : ∀ x ∈ S, 0 ≤ w x) :
    ∃ r : ℝ, 1 ≤ r ∧ cfZ G w S 1 = (r : ℂ) := by
  classical
  have hcast : ∀ J : Finset V,
      (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * 1) else 0) =
      (((if cfIndep G J then ∏ x ∈ J, w x else 0 : ℝ)) : ℂ) := by
    intro J
    by_cases hJ : cfIndep G J
    · have e1 : (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * 1) else 0) =
          ∏ x ∈ J, ((w x : ℂ) * 1) := ite_eq_left hJ
      have e2 : ((if cfIndep G J then ∏ x ∈ J, w x else 0 : ℝ)) = ∏ x ∈ J, w x :=
        ite_eq_left hJ
      rw [e1, e2]
      simp only [mul_one, Complex.ofReal_prod]
    · have e1 : (if cfIndep G J then ∏ x ∈ J, ((w x : ℂ) * 1) else 0) = (0 : ℂ) :=
        ite_eq_right hJ
      have e2 : ((if cfIndep G J then ∏ x ∈ J, w x else 0 : ℝ)) = (0 : ℝ) :=
        ite_eq_right hJ
      rw [e1, e2]
      simp
  have hterm : ∀ J ∈ S.powerset,
      (0 : ℝ) ≤ (if cfIndep G J then ∏ x ∈ J, w x else 0) := by
    intro J hJ
    by_cases hJ' : cfIndep G J
    · have e1 : (if cfIndep G J then ∏ x ∈ J, w x else 0) = ∏ x ∈ J, w x :=
        ite_eq_left hJ'
      rw [e1]
      apply Finset.prod_nonneg
      intro x hx
      exact hpos x (Finset.mem_powerset.mp hJ hx)
    · have e1 : (if cfIndep G J then ∏ x ∈ J, w x else 0) = (0 : ℝ) :=
        ite_eq_right hJ'
      rw [e1]
  have hindep_empty : cfIndep G ∅ := fun a ha => absurd ha (Finset.notMem_empty a)
  have h0 : (if cfIndep G ∅ then ∏ x ∈ (∅ : Finset V), w x else 0) = 1 := by
    have e1 : (if cfIndep G ∅ then ∏ x ∈ (∅ : Finset V), w x else 0) =
        ∏ x ∈ (∅ : Finset V), w x := ite_eq_left hindep_empty
    rw [e1, Finset.prod_empty]
  refine ⟨∑ J ∈ S.powerset, (if cfIndep G J then ∏ x ∈ J, w x else 0), ?_, ?_⟩
  · have h1 := Finset.single_le_sum hterm (Finset.empty_mem_powerset S)
    rwa [h0] at h1
  · simp only [cfZ]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro J _
    exact hcast J

/-- The Wanted `clawFree` gives `cfClawFreeOn` over `univ`. -/
private lemma cf_clawFree_univ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : clawFree G) : cfClawFreeOn G Finset.univ := by
  intro c _ a _ b _ d _ hca hcb hcd hab had hbd
  by_contra hcon
  push Not at hcon
  exact h ⟨c, a, b, d, G.ne_of_adj hca, G.ne_of_adj hcb, G.ne_of_adj hcd,
    hab, had, hbd, hca, hcb, hcd, hcon.1, hcon.2.1, hcon.2.2⟩

/-- `cfClawFreeOn` is monotone in the set. -/
private lemma cf_clawFree_mono {V : Type*} (G : SimpleGraph V) (S T : Finset V)
    (h : cfClawFreeOn G S) (hTS : T ⊆ S) : cfClawFreeOn G T := by
  intro c hc a ha b hb d hd h1 h2 h3 h4 h5 h6
  exact h c (hTS hc) a (hTS ha) b (hTS hb) d (hTS hd) h1 h2 h3 h4 h5 h6

/-- Private neighbourhoods of adjacent vertices are cliques. -/
private lemma cf_clique_priv {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hadj : G.Adj u v)
    (hcf : cfClawFreeOn G S) :
    (∀ a ∈ cfPrivA G S u v, ∀ b ∈ cfPrivA G S u v, a ≠ b → G.Adj a b) ∧
    (∀ a ∈ cfPrivB G S u v, ∀ b ∈ cfPrivB G S u v, a ≠ b → G.Adj a b) := by
  constructor
  · intro a ha b hb hne
    simp only [cfPrivA, Finset.mem_filter] at ha hb
    obtain ⟨haS, haua, hanv, hnva⟩ := ha
    obtain ⟨hbS, hub, hbnv, hnvb⟩ := hb
    by_contra hnab
    have h := hcf u hu v hv a haS b hbS hadj haua hub
      hanv.symm hbnv.symm hne
    rcases h with h1 | h1 | h1
    · exact hnva h1
    · exact hnvb h1
    · exact hnab h1
  · intro a ha b hb hne
    simp only [cfPrivB, Finset.mem_filter] at ha hb
    obtain ⟨haS, hava, hanu, hnua⟩ := ha
    obtain ⟨hbS, hvb, hbnu, hnub⟩ := hb
    by_contra hnab
    have h := hcf v hv u hu a haS b hbS hadj.symm hava hvb
      hanu.symm hbnu.symm hne
    rcases h with h1 | h1 | h1
    · exact hnua h1
    · exact hnub h1
    · exact hnab h1

/-- Expansion of `cfZ` along a clique. -/
private lemma cf_clique_expansion {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : V → ℝ) (S C : Finset V) (hCsub : C ⊆ S)
    (hclique : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → G.Adj a b) (z : ℂ) :
    cfZ G w S z = cfZ G w (S \ C) z +
      ∑ c ∈ C, (w c : ℂ) * z * cfZ G w (cfDel G S c) z := by
  classical
  revert S hCsub hclique
  refine Finset.induction_on (motive := fun C => ∀ S : Finset V, C ⊆ S →
    (∀ a ∈ C, ∀ b ∈ C, a ≠ b → G.Adj a b) → cfZ G w S z =
      cfZ G w (S \ C) z + ∑ c ∈ C, (w c : ℂ) * z * cfZ G w (cfDel G S c) z) C ?_ ?_
  · intro S hCsub hclique
    simp [Finset.sdiff_empty]
  · intro c C0 hc0 IH S hCsub hclique
    have hcS : c ∈ S := hCsub (Finset.mem_insert_self c C0)
    have hC0sub : C0 ⊆ S.erase c := by
      intro x hx
      have hxS := hCsub (Finset.mem_insert_of_mem hx)
      rw [Finset.mem_erase]
      refine ⟨?_, hxS⟩
      intro heq
      exact hc0 (heq ▸ hx)
    have hclique0 : ∀ a ∈ C0, ∀ b ∈ C0, a ≠ b → G.Adj a b := by
      intro a ha b hb hne2
      exact hclique a (Finset.mem_insert_of_mem ha) b
        (Finset.mem_insert_of_mem hb) hne2
    have hN1 := cf_vertex_recurrence G w S c hcS z
    have hIH := IH (S.erase c) hC0sub hclique0
    have hsdiff : (S.erase c) \ C0 = S \ insert c C0 := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    have hdel : ∀ c' ∈ C0, cfDel G (S.erase c) c' = cfDel G S c' := by
      intro c' hc'
      have hcc' : c ≠ c' := fun heq => hc0 (heq ▸ hc')
      have hadj : G.Adj c c' :=
        hclique c (Finset.mem_insert_self c C0) c' (Finset.mem_insert_of_mem hc') hcc'
      ext x
      simp only [cfDel, Finset.mem_filter]
      constructor
      · rintro ⟨hxE, hne2, hnadj⟩
        exact ⟨Finset.mem_of_mem_erase hxE, hne2, hnadj⟩
      · rintro ⟨hxS, hne2, hnadj⟩
        refine ⟨?_, hne2, hnadj⟩
        rw [Finset.mem_erase]
        refine ⟨?_, hxS⟩
        intro heq
        apply hnadj
        rw [heq]
        exact hadj.symm
    rw [hN1, hIH, hsdiff]
    have hsum : (∑ c' ∈ C0, (w c' : ℂ) * z * cfZ G w (cfDel G (S.erase c) c') z) =
        (∑ c' ∈ C0, (w c' : ℂ) * z * cfZ G w (cfDel G S c') z) :=
      Finset.sum_congr rfl (fun c' hc' => by rw [hdel c' hc'])
    rw [hsum, Finset.sum_insert hc0]
    ac_rfl

/-- Membership in `cfPrivA` is the defining conjunction. -/
private lemma cf_mem_privA {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v x : V) :
    x ∈ cfPrivA G S u v ↔ x ∈ S ∧ G.Adj u x ∧ x ≠ v ∧ ¬ G.Adj v x := by
  classical
  unfold cfPrivA
  rw [Finset.mem_filter]

/-- Membership in `cfPrivB` is the defining conjunction. -/
private lemma cf_mem_privB {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v x : V) :
    x ∈ cfPrivB G S u v ↔ x ∈ S ∧ G.Adj v x ∧ x ≠ u ∧ ¬ G.Adj u x := by
  classical
  unfold cfPrivB
  rw [Finset.mem_filter]

/-- Membership in `cfR` is the defining conjunction. -/
private lemma cf_mem_R {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v x : V) :
    x ∈ cfR G S u v ↔ x ∈ S ∧ (x ≠ u ∧ ¬ G.Adj u x) ∧ (x ≠ v ∧ ¬ G.Adj v x) := by
  classical
  unfold cfR
  rw [Finset.mem_filter]

/-- Membership in `cfS'` is the three-way disjunction. -/
private lemma cf_mem_S' {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v x : V) :
    x ∈ cfS' G S u v ↔ (x ∈ cfR G S u v ∨ x ∈ cfPrivA G S u v) ∨
      x ∈ cfPrivB G S u v := by
  unfold cfS'
  rw [Finset.mem_union, Finset.mem_union]

/-- `A`, `B`, `R` are pairwise disjoint. -/
private lemma cf_contract_disjoint {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) :
    Disjoint (cfPrivA G S u v) (cfPrivB G S u v) ∧
    Disjoint (cfR G S u v) (cfPrivA G S u v) ∧
    Disjoint (cfR G S u v) (cfPrivB G S u v) := by
  classical
  have hAB : Disjoint (cfPrivA G S u v) (cfPrivB G S u v) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [cf_mem_privA] at hxA
    rw [cf_mem_privB] at hxB
    obtain ⟨-, -, -, hnAdjV⟩ := hxA
    obtain ⟨-, hAdjV, -, -⟩ := hxB
    exact hnAdjV hAdjV
  have hRA : Disjoint (cfR G S u v) (cfPrivA G S u v) := by
    rw [Finset.disjoint_left]
    intro x hxR hxA
    rw [cf_mem_R] at hxR
    rw [cf_mem_privA] at hxA
    obtain ⟨-, ⟨⟨-, hnAdjU⟩, -⟩⟩ := hxR
    obtain ⟨-, hAdjU, -, -⟩ := hxA
    exact hnAdjU hAdjU
  have hRB : Disjoint (cfR G S u v) (cfPrivB G S u v) := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    rw [cf_mem_R] at hxR
    rw [cf_mem_privB] at hxB
    obtain ⟨-, -, ⟨-, hnAdjV⟩⟩ := hxR
    obtain ⟨-, hAdjV, -, -⟩ := hxB
    exact hnAdjV hAdjV
  exact ⟨hAB, hRA, hRB⟩

/-- The contracted set is a strict subset missing `u` and `v`. -/
private lemma cf_contract_ssubset {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (hu : u ∈ S) :
    u ∉ cfS' G S u v ∧ v ∉ cfS' G S u v ∧ cfS' G S u v ⊆ S ∧ cfS' G S u v ⊂ S := by
  classical
  have hsub : cfS' G S u v ⊆ S := by
    intro x hx
    rw [cf_mem_S'] at hx
    obtain ((hR | hA) | hB) := hx
    · rw [cf_mem_R] at hR
      exact hR.1
    · rw [cf_mem_privA] at hA
      exact hA.1
    · rw [cf_mem_privB] at hB
      exact hB.1
  have hnu : u ∉ cfS' G S u v := by
    intro hu'
    rw [cf_mem_S'] at hu'
    obtain ((hR | hA) | hB) := hu'
    · rw [cf_mem_R] at hR
      exact hR.2.1.1 rfl
    · rw [cf_mem_privA] at hA
      exact G.ne_of_adj hA.2.1 rfl
    · rw [cf_mem_privB] at hB
      exact hB.2.2.1 rfl
  have hnv : v ∉ cfS' G S u v := by
    intro hv'
    rw [cf_mem_S'] at hv'
    obtain ((hR | hA) | hB) := hv'
    · rw [cf_mem_R] at hR
      exact hR.2.2.1 rfl
    · rw [cf_mem_privA] at hA
      exact hA.2.2.1 rfl
    · rw [cf_mem_privB] at hB
      exact G.ne_of_adj hB.2.1 rfl
  have hss : cfS' G S u v ⊂ S := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, fun heq => hnu ?_⟩
    rw [heq]
    exact hu
  exact ⟨hnu, hnv, hsub, hss⟩

/-- The contracted graph is claw-free on the contracted set. -/
private lemma cf_contract_clawFreeOn {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hadj : G.Adj u v)
    (hcf : cfClawFreeOn G S) :
    cfClawFreeOn (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)) (cfS' G S u v) := by
  classical
  have hSsub : cfS' G S u v ⊆ S := (cf_contract_ssubset G S u v hu).2.2.1
  obtain ⟨hdisjAB, hdisjRA, hdisjRB⟩ := cf_contract_disjoint G S u v
  obtain ⟨hclA, hclB⟩ := cf_clique_priv G S u v hu hv hadj hcf
  have hcliqueAB : ∀ x ∈ cfPrivA G S u v ∪ cfPrivB G S u v,
      ∀ y ∈ cfPrivA G S u v ∪ cfPrivB G S u v, x ≠ y →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj x y := by
    intro x hx y hy hne
    rw [Finset.mem_union] at hx hy
    rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl (hclA x hxA y hyA hne))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr
        ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl ⟨hxA, hyB⟩⟩))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr
        ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr ⟨hyA, hxB⟩⟩))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl (hclB x hxB y hyB hne))
  have hGofG' : ∀ x y,
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj x y →
      ¬ G.Adj x y := by
    intro x y hnn hadj2
    exact hnn ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl hadj2))
  have hGR : ∀ c w, (c ∈ cfR G S u v ∨ w ∈ cfR G S u v) →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c w → G.Adj c w := by
    intro c w hR hcw
    have hcw' := (SimpleGraph.sup_adj _ _ _ _).mp hcw
    rcases hcw' with h | h
    · exact h
    · rw [SimpleGraph.fromRel_adj] at h
      obtain ⟨hne, hnew | hnew⟩ := h
      · obtain ⟨hcA, hwB⟩ := hnew
        rcases hR with hcR | hwR
        · exact absurd hcA (Finset.disjoint_left.mp hdisjRA hcR)
        · exact absurd hwB (Finset.disjoint_left.mp hdisjRB hwR)
      · obtain ⟨hwA, hcB⟩ := hnew
        rcases hR with hcR | hwR
        · exact absurd hcB (Finset.disjoint_left.mp hdisjRB hcR)
        · exact absurd hwA (Finset.disjoint_left.mp hdisjRA hwR)
  have hABmem : ∀ x ∈ cfS' G S u v, x ∉ cfR G S u v →
      x ∈ cfPrivA G S u v ∪ cfPrivB G S u v := by
    intro x hx hxR
    rw [cf_mem_S'] at hx
    obtain ((hxR' | hxA) | hxB) := hx
    · exact absurd hxR' hxR
    · exact Finset.mem_union_left _ hxA
    · exact Finset.mem_union_right _ hxB
  have hlpR : ∀ c a b d, c ∈ cfR G S u v → a ∈ cfS' G S u v → b ∈ cfS' G S u v →
      d ∈ cfS' G S u v →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c a →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c b →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c d →
      a ≠ b → a ≠ d → b ≠ d →
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj a b →
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj a d →
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj b d → False := by
    intro c a b d hcR haS hbS hdS hca hcb hcd hab had hbd nab nad nbd
    obtain ⟨hcS, -⟩ := (cf_mem_R G S u v c).mp hcR
    have gca := hGR c a (Or.inl hcR) hca
    have gcb := hGR c b (Or.inl hcR) hcb
    have gcd := hGR c d (Or.inl hcR) hcd
    have h := hcf c hcS a (hSsub haS) b (hSsub hbS) d (hSsub hdS)
      gca gcb gcd hab had hbd
    rcases h with h | h | h
    · exact hGofG' a b nab h
    · exact hGofG' a d nad h
    · exact hGofG' b d nbd h
  have hlpA : ∀ c x y, c ∈ cfPrivA G S u v → x ∈ cfR G S u v → y ∈ cfR G S u v →
      x ≠ y →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c x →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c y →
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj x y → False := by
    intro c x y hcA hxR hyR hxy hcx hcy hnxy
    have hxRm : x ∈ cfR G S u v := hxR
    have hyRm : y ∈ cfR G S u v := hyR
    rw [cf_mem_privA] at hcA
    rw [cf_mem_R] at hxR hyR
    obtain ⟨hcS, hcuAdj, -, -⟩ := hcA
    obtain ⟨hxS, ⟨⟨hxneU, hxnAdjU⟩, -⟩⟩ := hxR
    obtain ⟨hyS, ⟨⟨hyneU, hynAdjU⟩, -⟩⟩ := hyR
    have hcu : G.Adj c u := hcuAdj.symm
    have hcx := hGR c x (Or.inr hxRm) hcx
    have hcy := hGR c y (Or.inr hyRm) hcy
    have hux : u ≠ x := fun heq => hxneU heq.symm
    have huy : u ≠ y := fun heq => hyneU heq.symm
    have h := hcf c hcS u hu x hxS y hyS hcu hcx hcy hux huy hxy
    rcases h with h | h | h
    · exact hxnAdjU h
    · exact hynAdjU h
    · exact hGofG' x y hnxy h
  have hlpB : ∀ c x y, c ∈ cfPrivB G S u v → x ∈ cfR G S u v → y ∈ cfR G S u v →
      x ≠ y →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c x →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c y →
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj x y → False := by
    intro c x y hcB hxR hyR hxy hcx hcy hnxy
    have hxRm : x ∈ cfR G S u v := hxR
    have hyRm : y ∈ cfR G S u v := hyR
    rw [cf_mem_privB] at hcB
    rw [cf_mem_R] at hxR hyR
    obtain ⟨hcS, hcvAdj, -, -⟩ := hcB
    obtain ⟨hxS, -, hxneV, hxnAdjV⟩ := hxR
    obtain ⟨hyS, -, hyneV, hynAdjV⟩ := hyR
    have hcv : G.Adj c v := hcvAdj.symm
    have hcx := hGR c x (Or.inr hxRm) hcx
    have hcy := hGR c y (Or.inr hyRm) hcy
    have hvx : v ≠ x := fun heq => hxneV heq.symm
    have hvy : v ≠ y := fun heq => hyneV heq.symm
    have h := hcf c hcS v hv x hxS y hyS hcv hcx hcy hvx hvy hxy
    rcases h with h | h | h
    · exact hxnAdjV h
    · exact hynAdjV h
    · exact hGofG' x y hnxy h
  intro c hcS a haS b hbS d hdS hca hcb hcd hab had hbd
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨nab, nad, nbd⟩ := hcon
  have hpair : (a ∈ cfR G S u v ∧ b ∈ cfR G S u v) ∨
      (a ∈ cfR G S u v ∧ d ∈ cfR G S u v) ∨
      (b ∈ cfR G S u v ∧ d ∈ cfR G S u v) := by
    by_contra hcon2
    rw [not_or, not_or, not_and, not_and, not_and] at hcon2
    obtain ⟨habI, hadI, hbdI⟩ := hcon2
    by_cases haR : a ∈ cfR G S u v
    · have hbAB := hABmem b hbS (habI haR)
      have hdAB := hABmem d hdS (hadI haR)
      exact nbd (hcliqueAB b hbAB d hdAB hbd)
    · by_cases hbR : b ∈ cfR G S u v
      · by_cases hdR : d ∈ cfR G S u v
        · exact (hbdI hbR) hdR
        · have haAB := hABmem a haS haR
          have hdAB := hABmem d hdS hdR
          exact nad (hcliqueAB a haAB d hdAB had)
      · have haAB := hABmem a haS haR
        have hbAB := hABmem b hbS hbR
        exact nab (hcliqueAB a haAB b hbAB hab)
  have hcU : c ∈ cfS' G S u v := hcS
  rw [cf_mem_S'] at hcU
  rcases hpair with ⟨hxR, hyR⟩ | ⟨hxR, hyR⟩ | ⟨hxR, hyR⟩
  · obtain ((hcR | hcA) | hcB) := hcU
    · exact hlpR c a b d hcR haS hbS hdS hca hcb hcd hab had hbd nab nad nbd
    · exact hlpA c a b hcA hxR hyR hab hca hcb nab
    · exact hlpB c a b hcB hxR hyR hab hca hcb nab
  · obtain ((hcR | hcA) | hcB) := hcU
    · exact hlpR c a b d hcR haS hbS hdS hca hcb hcd hab had hbd nab nad nbd
    · exact hlpA c a d hcA hxR hyR had hca hcd nad
    · exact hlpB c a d hcB hxR hyR had hca hcd nad
  · obtain ((hcR | hcA) | hcB) := hcU
    · exact hlpR c a b d hcR haS hbS hdS hca hcb hcd hab had hbd nab nad nbd
    · exact hlpA c b d hcA hxR hyR hbd hcb hcd nbd
    · exact hlpB c b d hcB hxR hyR hbd hcb hcd nbd

/-- Membership in `cfDel` is the defining conjunction. -/
private lemma cf_mem_del {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (v x : V) :
    x ∈ cfDel G S v ↔ x ∈ S ∧ x ≠ v ∧ ¬ G.Adj v x := by
  classical
  unfold cfDel
  rw [Finset.mem_filter]

/-- Contraction identity, plus positivity of the rescaled weight. -/
private lemma cf_contract_identity {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (w : V → ℝ) (s t : ℝ) (hu : u ∈ S) (hv : v ∈ S)
    (hadj : G.Adj u v) (hcf : cfClawFreeOn G S)
    (hw : ∀ x ∈ S, 0 < w x) (hs : 0 < s) (ht : 0 < t) (z : ℂ) :
    (s : ℂ) * cfZ G w (cfDel G S u) z + (t : ℂ) * cfZ G w (cfDel G S v) z =
      (((s + t : ℝ)) : ℂ) * cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) (cfS' G S u v) z ∧
    ∀ x ∈ cfS' G S u v, 0 < cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x := by
  classical
  obtain ⟨hdisjAB, hdisjRA, hdisjRB⟩ := cf_contract_disjoint G S u v
  obtain ⟨hclA, hclB⟩ := cf_clique_priv G S u v hu hv hadj hcf
  have hSsub : cfS' G S u v ⊆ S := (cf_contract_ssubset G S u v hu).2.2.1
  have hstpos : 0 < s + t := add_pos hs ht
  have hDelU : cfDel G S u = cfR G S u v ∪ cfPrivB G S u v := by
    ext x
    rw [cf_mem_del, Finset.mem_union]
    constructor
    · rintro ⟨hxS, hxneU, hxnAdjU⟩
      by_cases hxAdjV : G.Adj v x
      · exact Or.inr ((cf_mem_privB G S u v x).mpr ⟨hxS, hxAdjV, hxneU, hxnAdjU⟩)
      · have hxneV : x ≠ v := by
          intro heq
          apply hxnAdjU
          rw [heq]
          exact hadj
        exact Or.inl ((cf_mem_R G S u v x).mpr
          ⟨hxS, ⟨hxneU, hxnAdjU⟩, ⟨hxneV, hxAdjV⟩⟩)
    · rintro (hR | hB)
      · rw [cf_mem_R] at hR
        obtain ⟨hxS, ⟨⟨hxneU, hxnAdjU⟩, -⟩⟩ := hR
        exact ⟨hxS, hxneU, hxnAdjU⟩
      · rw [cf_mem_privB] at hB
        obtain ⟨hxS, -, hxneU, hxnAdjU⟩ := hB
        exact ⟨hxS, hxneU, hxnAdjU⟩
  have hDelV : cfDel G S v = cfR G S u v ∪ cfPrivA G S u v := by
    ext x
    rw [cf_mem_del, Finset.mem_union]
    constructor
    · rintro ⟨hxS, hxneV, hxnAdjV⟩
      by_cases hxAdjU : G.Adj u x
      · exact Or.inr ((cf_mem_privA G S u v x).mpr ⟨hxS, hxAdjU, hxneV, hxnAdjV⟩)
      · have hxneU : x ≠ u := by
          intro heq
          apply hxnAdjV
          rw [heq]
          exact hadj.symm
        exact Or.inl ((cf_mem_R G S u v x).mpr
          ⟨hxS, ⟨hxneU, hxAdjU⟩, ⟨hxneV, hxnAdjV⟩⟩)
    · rintro (hR | hA)
      · rw [cf_mem_R] at hR
        obtain ⟨hxS, -, hxneV, hxnAdjV⟩ := hR
        exact ⟨hxS, hxneV, hxnAdjV⟩
      · rw [cf_mem_privA] at hA
        obtain ⟨hxS, -, hxneV, hxnAdjV⟩ := hA
        exact ⟨hxS, hxneV, hxnAdjV⟩
  have hsdB : (cfR G S u v ∪ cfPrivB G S u v) \ cfPrivB G S u v = cfR G S u v := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hnB⟩
      · exact h
      · exact absurd h hnB
    · intro hxR
      exact ⟨Or.inl hxR, Finset.disjoint_left.mp hdisjRB hxR⟩
  have hsdA : (cfR G S u v ∪ cfPrivA G S u v) \ cfPrivA G S u v = cfR G S u v := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hnA⟩
      · exact h
      · exact absurd h hnA
    · intro hxR
      exact ⟨Or.inl hxR, Finset.disjoint_left.mp hdisjRA hxR⟩
  have hsdAB : cfS' G S u v \ (cfPrivA G S u v ∪ cfPrivB G S u v) = cfR G S u v := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, cf_mem_S']
    constructor
    · rintro ⟨(hR | hA) | hB, hnAB⟩
      · exact hR
      · exact absurd (Or.inl hA) hnAB
      · exact absurd (Or.inr hB) hnAB
    · intro hxR
      exact ⟨Or.inl (Or.inl hxR),
        not_or.mpr ⟨Finset.disjoint_left.mp hdisjRA hxR,
          Finset.disjoint_left.mp hdisjRB hxR⟩⟩
  have hdelRB : ∀ b ∈ cfPrivB G S u v,
      cfDel G (cfR G S u v ∪ cfPrivB G S u v) b = cfDel G (cfR G S u v) b := by
    intro b hbB
    ext x
    rw [cf_mem_del, cf_mem_del, Finset.mem_union]
    constructor
    · rintro ⟨hR | hB, hxne, hxnadj⟩
      · exact ⟨hR, hxne, hxnadj⟩
      · exfalso
        exact hxnadj (hclB b hbB x hB (Ne.symm hxne))
    · rintro ⟨hR, hxne, hxnadj⟩
      exact ⟨Or.inl hR, hxne, hxnadj⟩
  have hdelRA : ∀ a ∈ cfPrivA G S u v,
      cfDel G (cfR G S u v ∪ cfPrivA G S u v) a = cfDel G (cfR G S u v) a := by
    intro a haA
    ext x
    rw [cf_mem_del, cf_mem_del, Finset.mem_union]
    constructor
    · rintro ⟨hR | hA, hxne, hxnadj⟩
      · exact ⟨hR, hxne, hxnadj⟩
      · exfalso
        exact hxnadj (hclA a haA x hA (Ne.symm hxne))
    · rintro ⟨hR, hxne, hxnadj⟩
      exact ⟨Or.inl hR, hxne, hxnadj⟩
  have hBsub : cfPrivB G S u v ⊆ cfR G S u v ∪ cfPrivB G S u v :=
    fun x hx => Finset.mem_union.mpr (Or.inr hx)
  have hAsub : cfPrivA G S u v ⊆ cfR G S u v ∪ cfPrivA G S u v :=
    fun x hx => Finset.mem_union.mpr (Or.inr hx)
  have hexpB := cf_clique_expansion G w
    (cfR G S u v ∪ cfPrivB G S u v) (cfPrivB G S u v) hBsub hclB z
  have eBsum : (∑ b ∈ cfPrivB G S u v, (w b : ℂ) * z *
      cfZ G w (cfDel G (cfR G S u v ∪ cfPrivB G S u v) b) z) =
      (∑ b ∈ cfPrivB G S u v, (w b : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) b) z) :=
    Finset.sum_congr rfl (fun b hb => by rw [hdelRB b hb])
  have hexpB' : cfZ G w (cfR G S u v ∪ cfPrivB G S u v) z = cfZ G w (cfR G S u v) z +
      (∑ b ∈ cfPrivB G S u v, (w b : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) b) z) := by
    rw [hexpB, hsdB, eBsum]
  have hexpA := cf_clique_expansion G w
    (cfR G S u v ∪ cfPrivA G S u v) (cfPrivA G S u v) hAsub hclA z
  have eAsum : (∑ a ∈ cfPrivA G S u v, (w a : ℂ) * z *
      cfZ G w (cfDel G (cfR G S u v ∪ cfPrivA G S u v) a) z) =
      (∑ a ∈ cfPrivA G S u v, (w a : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) a) z) :=
    Finset.sum_congr rfl (fun a ha => by rw [hdelRA a ha])
  have hexpA' : cfZ G w (cfR G S u v ∪ cfPrivA G S u v) z = cfZ G w (cfR G S u v) z +
      (∑ a ∈ cfPrivA G S u v, (w a : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) a) z) := by
    rw [hexpA, hsdA, eAsum]
  have hcliqueAB : ∀ x ∈ cfPrivA G S u v ∪ cfPrivB G S u v,
      ∀ y ∈ cfPrivA G S u v ∪ cfPrivB G S u v, x ≠ y →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj x y := by
    intro x hx y hy hne
    rw [Finset.mem_union] at hx hy
    rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl (hclA x hxA y hyA hne))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr
        ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl ⟨hxA, hyB⟩⟩))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr
        ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr ⟨hyA, hxB⟩⟩))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl (hclB x hxB y hyB hne))
  have hGofG' : ∀ x y,
      ¬ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj x y →
      ¬ G.Adj x y := by
    intro x y hnn hadj2
    exact hnn ((SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl hadj2))
  have hGR : ∀ c w, (c ∈ cfR G S u v ∨ w ∈ cfR G S u v) →
      (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)).Adj c w → G.Adj c w := by
    intro c w hR hcw
    have hcw' := (SimpleGraph.sup_adj _ _ _ _).mp hcw
    rcases hcw' with h | h
    · exact h
    · rw [SimpleGraph.fromRel_adj] at h
      obtain ⟨hne, hnew | hnew⟩ := h
      · obtain ⟨hcA, hwB⟩ := hnew
        rcases hR with hcR | hwR
        · exact absurd hcA (Finset.disjoint_left.mp hdisjRA hcR)
        · exact absurd hwB (Finset.disjoint_left.mp hdisjRB hwR)
      · obtain ⟨hwA, hcB⟩ := hnew
        rcases hR with hcR | hwR
        · exact absurd hcB (Finset.disjoint_left.mp hdisjRB hcR)
        · exact absurd hwA (Finset.disjoint_left.mp hdisjRA hwR)
  have hW : ∀ x ∈ cfR G S u v,
      cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x = w x := by
    intro x hxR
    have hnB : x ∉ cfPrivB G S u v := Finset.disjoint_left.mp hdisjRB hxR
    have hnA : x ∉ cfPrivA G S u v := Finset.disjoint_left.mp hdisjRA hxR
    unfold cfW
    rw [ite_eq_right hnB, ite_eq_right hnA]
  have hdelSub : ∀ x, cfDel G (cfR G S u v) x ⊆ cfR G S u v := by
    intro x y hy
    exact ((cf_mem_del G (cfR G S u v) x y).mp hy).1
  have htrans : ∀ T : Finset V, T ⊆ cfR G S u v →
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) T z = cfZ G w T z := by
    intro T hTR
    apply cf_congr _ _ _ _ _
    · intro x hxT y hyT
      have hxR := hTR hxT
      have hyR := hTR hyT
      constructor
      · intro hG'
        exact hGR x y (Or.inl hxR) hG'
      · intro hG
        exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl hG)
    · intro x hxT
      exact hW x (hTR hxT)
  have hABsub : cfPrivA G S u v ∪ cfPrivB G S u v ⊆ cfS' G S u v := by
    intro y hyAB
    rw [Finset.mem_union] at hyAB
    rw [cf_mem_S']
    rcases hyAB with hyA | hyB
    · exact Or.inl (Or.inr hyA)
    · exact Or.inr hyB
  have hdelG' : ∀ x ∈ cfPrivA G S u v ∪ cfPrivB G S u v,
      cfDel (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)) (cfS' G S u v) x =
      cfDel G (cfR G S u v) x := by
    intro x hxAB
    ext y
    rw [cf_mem_del, cf_mem_del]
    constructor
    · rintro ⟨hyS, hynex, hynG'⟩
      rw [cf_mem_S'] at hyS
      obtain ((hyR | hyA) | hyB) := hyS
      · exact ⟨hyR, hynex, hGofG' x y hynG'⟩
      · exfalso
        exact hynG' (hcliqueAB x hxAB y
          (Finset.mem_union_left _ hyA) (Ne.symm hynex))
      · exfalso
        exact hynG' (hcliqueAB x hxAB y
          (Finset.mem_union_right _ hyB) (Ne.symm hynex))
    · rintro ⟨hyR, hynex, hynG⟩
      refine ⟨?_, hynex, ?_⟩
      · rw [cf_mem_S']
        exact Or.inl (Or.inl hyR)
      · intro hG'
        exact hynG (hGR x y (Or.inr hyR) hG')
  have hexpG := cf_clique_expansion
    (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
    (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) (cfS' G S u v)
    (cfPrivA G S u v ∪ cfPrivB G S u v) hABsub hcliqueAB z
  have esumGA : (∑ x ∈ cfPrivA G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x : ℝ) : ℂ) * z *
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
        (cfDel (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)) (cfS' G S u v) x) z) =
      (∑ x ∈ cfPrivA G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x : ℝ) : ℂ) * z *
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
        (cfDel G (cfR G S u v) x) z) :=
    Finset.sum_congr rfl (fun x hx => by rw [hdelG' x (Finset.mem_union_left _ hx)])
  have esumGB : (∑ x ∈ cfPrivB G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x : ℝ) : ℂ) * z *
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
        (cfDel (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)) (cfS' G S u v) x) z) =
      (∑ x ∈ cfPrivB G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x : ℝ) : ℂ) * z *
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
        (cfDel G (cfR G S u v) x) z) :=
    Finset.sum_congr rfl (fun x hx => by rw [hdelG' x (Finset.mem_union_right _ hx)])
  have hexpG1 : cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
      (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) (cfS' G S u v) z =
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) (cfR G S u v) z +
      ((∑ a ∈ cfPrivA G S u v,
        ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t a : ℝ) : ℂ) * z *
        cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
          (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
          (cfDel G (cfR G S u v) a) z) +
       (∑ b ∈ cfPrivB G S u v,
        ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t b : ℝ) : ℂ) * z *
        cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
          (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
          (cfDel G (cfR G S u v) b) z)) := by
    rw [hexpG, hsdAB, Finset.sum_union hdisjAB, esumGA, esumGB]
  have hTR : cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
      (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) (cfR G S u v) z =
      cfZ G w (cfR G S u v) z :=
    htrans _ Finset.Subset.rfl
  have hTA : (∑ a ∈ cfPrivA G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t a : ℝ) : ℂ) * z *
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
        (cfDel G (cfR G S u v) a) z) =
      (∑ a ∈ cfPrivA G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t a : ℝ) : ℂ) * z *
      cfZ G w (cfDel G (cfR G S u v) a) z) :=
    Finset.sum_congr rfl (fun a _ => by rw [htrans _ (hdelSub a)])
  have hTB : (∑ b ∈ cfPrivB G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t b : ℝ) : ℂ) * z *
      cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t)
        (cfDel G (cfR G S u v) b) z) =
      (∑ b ∈ cfPrivB G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t b : ℝ) : ℂ) * z *
      cfZ G w (cfDel G (cfR G S u v) b) z) :=
    Finset.sum_congr rfl (fun b _ => by rw [htrans _ (hdelSub b)])
  have hWA : ∀ a ∈ cfPrivA G S u v,
      cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t a = t / (s + t) * w a := by
    intro a haA
    have hnB : a ∉ cfPrivB G S u v := Finset.disjoint_left.mp hdisjAB haA
    unfold cfW
    rw [ite_eq_right hnB, ite_eq_left haA]
  have hWB : ∀ b ∈ cfPrivB G S u v,
      cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t b = s / (s + t) * w b := by
    intro b hbB
    unfold cfW
    rw [ite_eq_left hbB]
  have hstC : (((s + t : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hstpos)
  have ecs : ((s : ℂ) + (t : ℂ)) * ((((s / (s + t) : ℝ))) : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_add, Complex.ofReal_div, mul_div_cancel₀ _ hstC]
  have ect : ((s : ℂ) + (t : ℂ)) * ((((t / (s + t) : ℝ))) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_add, Complex.ofReal_div, mul_div_cancel₀ _ hstC]
  have eTAw : (∑ a ∈ cfPrivA G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t a : ℝ) : ℂ) * z *
      cfZ G w (cfDel G (cfR G S u v) a) z) =
      ((((t / (s + t) : ℝ))) : ℂ) *
      (∑ a ∈ cfPrivA G S u v, (w a : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) a) z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a haA
    rw [hWA a haA, Complex.ofReal_mul]
    ring
  have eTBw : (∑ b ∈ cfPrivB G S u v,
      ((cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t b : ℝ) : ℂ) * z *
      cfZ G w (cfDel G (cfR G S u v) b) z) =
      ((((s / (s + t) : ℝ))) : ℂ) *
      (∑ b ∈ cfPrivB G S u v, (w b : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) b) z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hbB
    rw [hWB b hbB, Complex.ofReal_mul]
    ring
  have hid : (s : ℂ) * cfZ G w (cfDel G S u) z + (t : ℂ) * cfZ G w (cfDel G S v) z =
      (((s + t : ℝ)) : ℂ) * cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
        (cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t) (cfS' G S u v) z := by
    rw [hDelU, hDelV, hexpB', hexpA', hexpG1, hTR, hTA, hTB, eTAw, eTBw,
      Complex.ofReal_add]
    linear_combination
      (-(∑ a ∈ cfPrivA G S u v, (w a : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) a) z)) * ect +
      (-(∑ b ∈ cfPrivB G S u v, (w b : ℂ) * z * cfZ G w (cfDel G (cfR G S u v) b) z)) * ecs
  have hpos : ∀ x ∈ cfS' G S u v,
      0 < cfW w (cfPrivA G S u v) (cfPrivB G S u v) s t x := by
    intro x hxS
    rw [cf_mem_S'] at hxS
    obtain ((hxR | hxA) | hxB) := hxS
    · rw [hW x hxR]
      exact hw x (hSsub ((cf_mem_S' G S u v x).mpr (Or.inl (Or.inl hxR))))
    · rw [hWA x hxA]
      have hxS' : x ∈ S :=
        hSsub ((cf_mem_S' G S u v x).mpr (Or.inl (Or.inr hxA)))
      exact mul_pos (div_pos ht hstpos) (hw x hxS')
    · rw [hWB x hxB]
      have hxS' : x ∈ S := hSsub ((cf_mem_S' G S u v x).mpr (Or.inr hxB))
      exact mul_pos (div_pos hs hstpos) (hw x hxS')
  exact ⟨hid, hpos⟩

/-- Argument additivity along the preconnected domain `cfD`. -/
private lemma cf_arg_add_on_D (g₁₂ g₂₃ g₁₃ : ℂ → ℂ)
    (hcont₁₂ : ContinuousOn g₁₂ cfD) (hcont₂₃ : ContinuousOn g₂₃ cfD)
    (hmul : ∀ z ∈ cfD, g₁₃ z = g₁₂ z * g₂₃ z)
    (hslit₁₂ : ∀ z ∈ cfD, g₁₂ z ∈ Complex.slitPlane)
    (hslit₂₃ : ∀ z ∈ cfD, g₂₃ z ∈ Complex.slitPlane)
    (hslit₁₃ : ∀ z ∈ cfD, g₁₃ z ∈ Complex.slitPlane)
    (h1 : ∃ r₁₂ : ℝ, 0 < r₁₂ ∧ g₁₂ 1 = r₁₂)
    (h2 : ∃ r₂₃ : ℝ, 0 < r₂₃ ∧ g₂₃ 1 = r₂₃) :
    ∀ z ∈ cfD, Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) ∈ Set.Ioo (-Real.pi) Real.pi ∧
      Complex.arg (g₁₃ z) = Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) := by
  classical
  have hHconv : Convex ℝ {z : ℂ | 0 < z.im} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    have him : (a • x + b • y).im = a * x.im + b * y.im := by
      rw [Complex.add_im, Complex.real_smul, Complex.real_smul,
        Complex.im_ofReal_mul, Complex.im_ofReal_mul]
    rw [him]
    rcases le_total a b with hle | hle
    · have hbpos : 0 < b := by linarith
      have h1 : 0 < b * y.im := mul_pos hbpos hy
      have h0 : 0 ≤ a * x.im := mul_nonneg ha hx.le
      linarith
    · have hapos : 0 < a := by linarith
      have h1 : 0 < a * x.im := mul_pos hapos hx
      have h0 : 0 ≤ b * y.im := mul_nonneg hb hy.le
      linarith
  have hHpre : IsPreconnected {z : ℂ | 0 < z.im} := hHconv.isPreconnected
  have hDpre : IsPreconnected cfD := by
    apply hHpre.subset_closure
    · intro z hz
      exact Or.inl hz
    · intro z hz
      simp only [cfD, Set.mem_union, Set.mem_ofPred_eq] at hz
      rcases hz with hz | rfl
      · exact subset_closure hz
      · rw [Metric.mem_closure_iff]
        intro ε hε
        refine ⟨1 + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
        · simp only [Set.mem_ofPred_eq]
          have him2 : (1 + ((ε / 2 : ℝ) : ℂ) * Complex.I).im = ε / 2 := by
            simp [Complex.add_im, Complex.mul_im]
          rw [him2]
          linarith
        · rw [dist_eq_norm]
          have hsub : (1 : ℂ) - (1 + ((ε / 2 : ℝ) : ℂ) * Complex.I) =
              -(((ε / 2 : ℝ) : ℂ) * Complex.I) := by ring
          rw [hsub, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
          linarith
  have h1mem : (1 : ℂ) ∈ cfD := Or.inr rfl
  have hmaps12 : Set.MapsTo g₁₂ cfD Complex.slitPlane := fun z hz => hslit₁₂ z hz
  have hmaps23 : Set.MapsTo g₂₃ cfD Complex.slitPlane := fun z hz => hslit₂₃ z hz
  have harg12 : ContinuousOn (fun z => Complex.arg (g₁₂ z)) cfD :=
    Complex.continuousOn_arg.comp hcont₁₂ hmaps12
  have harg23 : ContinuousOn (fun z => Complex.arg (g₂₃ z)) cfD :=
    Complex.continuousOn_arg.comp hcont₂₃ hmaps23
  have hφ : ContinuousOn (fun z => Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z)) cfD :=
    harg12.add harg23
  obtain ⟨r₁₂, hr12pos, hr12⟩ := h1
  obtain ⟨r₂₃, hr23pos, hr23⟩ := h2
  have hφ1 : (fun z => Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z)) 1 = 0 := by
    change Complex.arg (g₁₂ 1) + Complex.arg (g₂₃ 1) = 0
    rw [hr12, hr23, Complex.arg_ofReal_of_nonneg hr12pos.le,
      Complex.arg_ofReal_of_nonneg hr23pos.le, add_zero]
  have hne : ∀ z ∈ cfD, ∀ θ : ℝ, θ = Real.pi ∨ θ = -Real.pi →
      Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) ≠ θ := by
    intro z hz θ hθ harg
    have hpos : (0 : ℝ) < ‖g₁₂ z‖ * ‖g₂₃ z‖ := mul_pos
      (norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hslit₁₂ z hz)))
      (norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hslit₂₃ z hz)))
    have h12 := Complex.norm_mul_exp_arg_mul_I (g₁₂ z)
    have h23 := Complex.norm_mul_exp_arg_mul_I (g₂₃ z)
    have hexp : Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I) *
        Complex.exp ((Complex.arg (g₂₃ z) : ℂ) * Complex.I) = -1 := by
      rw [← Complex.exp_add]
      rcases hθ with rfl | rfl
      · have hcast : ((Complex.arg (g₁₂ z) : ℂ) * Complex.I) +
            ((Complex.arg (g₂₃ z) : ℂ) * Complex.I) =
            ((Real.pi : ℝ) : ℂ) * Complex.I := by
          calc ((Complex.arg (g₁₂ z) : ℂ) * Complex.I) +
                ((Complex.arg (g₂₃ z) : ℂ) * Complex.I)
              = ((((Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) : ℝ))) : ℂ) *
                Complex.I := by push_cast; ring
            _ = ((Real.pi : ℝ) : ℂ) * Complex.I := by rw [harg]
        rw [hcast, Complex.exp_pi_mul_I]
      · have hcast : ((Complex.arg (g₁₂ z) : ℂ) * Complex.I) +
            ((Complex.arg (g₂₃ z) : ℂ) * Complex.I) =
            -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
          calc ((Complex.arg (g₁₂ z) : ℂ) * Complex.I) +
                ((Complex.arg (g₂₃ z) : ℂ) * Complex.I)
              = ((((Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) : ℝ))) : ℂ) *
                Complex.I := by push_cast; ring
            _ = -(((Real.pi : ℝ) : ℂ) * Complex.I) := by rw [harg]; push_cast; ring
        rw [hcast, Complex.exp_neg_pi_mul_I]
    have eprod : g₁₂ z * g₂₃ z = -((((‖g₁₂ z‖ * ‖g₂₃ z‖ : ℝ))) : ℂ) := by
      calc g₁₂ z * g₂₃ z
          = (↑‖g₁₂ z‖ * Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I)) *
            (↑‖g₂₃ z‖ * Complex.exp ((Complex.arg (g₂₃ z) : ℂ) * Complex.I)) := by
              conv_lhs => rw [← h12, ← h23]
        _ = ↑(‖g₁₂ z‖ * ‖g₂₃ z‖) *
            (Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I) *
              Complex.exp ((Complex.arg (g₂₃ z) : ℂ) * Complex.I)) := by
              rw [Complex.ofReal_mul]; ring
        _ = -↑(‖g₁₂ z‖ * ‖g₂₃ z‖) := by rw [hexp]; ring
    have e13 : g₁₃ z = -((((‖g₁₂ z‖ * ‖g₂₃ z‖ : ℝ))) : ℂ) := by
      rw [hmul z hz, eprod]
    have hmem : (-((((‖g₁₂ z‖ * ‖g₂₃ z‖ : ℝ))) : ℂ)) ∈ Complex.slitPlane := by
      have h := hslit₁₃ z hz
      rwa [e13] at h
    rw [Complex.mem_slitPlane_iff] at hmem
    have hre : (-((((‖g₁₂ z‖ * ‖g₂₃ z‖ : ℝ))) : ℂ)).re = -(‖g₁₂ z‖ * ‖g₂₃ z‖) := by
      simp
    have him0 : (-((((‖g₁₂ z‖ * ‖g₂₃ z‖ : ℝ))) : ℂ)).im = 0 := by simp
    rw [hre, him0] at hmem
    rcases hmem with h | h
    · linarith
    · exact absurd rfl h
  have hbound : ∀ z ∈ cfD,
      Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) ∈ Set.Ioo (-Real.pi) Real.pi := by
    intro z hz
    by_contra hcon
    rw [Set.mem_Ioo, not_and] at hcon
    by_cases hlt : -Real.pi < Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z)
    · have hle : Real.pi ≤ Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) :=
        le_of_not_gt (hcon hlt)
      have hmemIcc : Real.pi ∈ Set.Icc ((fun z => Complex.arg (g₁₂ z) +
          Complex.arg (g₂₃ z)) 1) ((fun z => Complex.arg (g₁₂ z) +
          Complex.arg (g₂₃ z)) z) := by
        refine ⟨?_, hle⟩
        rw [hφ1]
        exact Real.pi_pos.le
      have hsub := hDpre.intermediate_value h1mem hz hφ hmemIcc
      rw [Set.mem_image] at hsub
      obtain ⟨z₁, hz₁mem, hz₁eq⟩ := hsub
      exact hne z₁ hz₁mem Real.pi (Or.inl rfl) hz₁eq
    · have hle : Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) ≤ -Real.pi :=
        le_of_not_gt hlt
      have hmemIcc : -Real.pi ∈ Set.Icc ((fun z => Complex.arg (g₁₂ z) +
          Complex.arg (g₂₃ z)) z) ((fun z => Complex.arg (g₁₂ z) +
          Complex.arg (g₂₃ z)) 1) := by
        refine ⟨hle, ?_⟩
        rw [hφ1]
        exact neg_nonpos.mpr Real.pi_pos.le
      have hsub := hDpre.intermediate_value hz h1mem hφ hmemIcc
      rw [Set.mem_image] at hsub
      obtain ⟨z₁, hz₁mem, hz₁eq⟩ := hsub
      exact hne z₁ hz₁mem (-Real.pi) (Or.inr rfl) hz₁eq
  intro z hz
  have hne12 : g₁₂ z ≠ 0 := Complex.slitPlane_ne_zero (hslit₁₂ z hz)
  have hne23 : g₂₃ z ≠ 0 := Complex.slitPlane_ne_zero (hslit₂₃ z hz)
  have hmemIoc : Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h := hbound z hz
    rw [Set.mem_Ioo] at h
    rw [Set.mem_Ioc]
    exact ⟨h.1, h.2.le⟩
  have hadd : Complex.arg (g₁₃ z) = Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) := by
    rw [hmul z hz]
    exact (Complex.arg_mul_eq_add_arg_iff hne12 hne23).mpr hmemIoc
  exact ⟨hbound z hz, hadd⟩

/-- A positive combination of vectors in an open half-plane is nonzero. -/
private lemma cf_sum_rays_ne_zero {ι : Type*} (s : Finset ι) (α : ι → ℝ) (ρ : ι → ℝ)
    (hne : s.Nonempty) (hρ : ∀ i ∈ s, 0 < ρ i)
    (hα : ∀ i ∈ s, ∀ j ∈ s, |α i - α j| < Real.pi) :
    ∑ i ∈ s, (ρ i : ℂ) * Complex.exp ((α i : ℂ) * Complex.I) ≠ 0 := by
  classical
  have hre_sum : ∀ (t : Finset ι) (f : ι → ℂ),
      (∑ i ∈ t, f i).re = ∑ i ∈ t, (f i).re := by
    intro t
    refine Finset.induction_on (motive := fun t => ∀ f : ι → ℂ,
      (∑ i ∈ t, f i).re = ∑ i ∈ t, (f i).re) t ?_ ?_
    · intro f
      simp
    · intro a t ha IH f
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, IH]
  have hmem : ∀ i ∈ s, α i ∈ s.image α :=
    fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hne_img : (s.image α).Nonempty := hne.image α
  have hle : ∀ i ∈ s, α i ≤ (s.image α).max' hne_img :=
    fun i his => Finset.le_max' _ _ (hmem i his)
  have hge : ∀ i ∈ s, (s.image α).min' hne_img ≤ α i := by
    intro i his
    apply Finset.min'_le
    exact hmem i his
  obtain ⟨j₁, hj₁s, hj₁⟩ := Finset.mem_image.mp (Finset.max'_mem (s.image α) hne_img)
  obtain ⟨j₂, hj₂s, hj₂⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image α) hne_img)
  have hrange : (s.image α).max' hne_img - (s.image α).min' hne_img < Real.pi := by
    have h := hα j₁ hj₁s j₂ hj₂s
    have h1 : α j₁ - α j₂ ≤ |α j₁ - α j₂| := le_abs_self _
    linarith
  suffices key : ∀ lo hi : ℝ, (∀ i ∈ s, lo ≤ α i ∧ α i ≤ hi) → hi - lo < Real.pi →
      ∑ i ∈ s, (ρ i : ℂ) * Complex.exp ((α i : ℂ) * Complex.I) ≠ 0 from
    key _ _ (fun i his => ⟨hge i his, hle i his⟩) hrange
  intro lo hi hbound hrange2 hsum
  set m : ℝ := (hi + lo) / 2 with hm
  have hIoo : ∀ i ∈ s, α i - m ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro i his
    obtain ⟨hloi, hhii⟩ := hbound i his
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hcos : ∀ i ∈ s, 0 < Real.cos (α i - m) :=
    fun i his => Real.cos_pos_of_mem_Ioo (hIoo i his)
  have hterm : ∀ i ∈ s, Complex.exp (-(m : ℂ) * Complex.I) *
      ((ρ i : ℂ) * Complex.exp ((α i : ℂ) * Complex.I)) =
      (ρ i : ℂ) * Complex.exp (↑(α i - m) * Complex.I) := by
    intro i _
    have hexp : (-(m : ℂ) * Complex.I) + ((α i : ℂ) * Complex.I) =
        (↑(α i - m) * Complex.I) := by
      push_cast
      ring
    calc Complex.exp (-(m : ℂ) * Complex.I) *
          ((ρ i : ℂ) * Complex.exp ((α i : ℂ) * Complex.I))
        = (ρ i : ℂ) * (Complex.exp (-(m : ℂ) * Complex.I) *
          Complex.exp ((α i : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [← Complex.exp_add, hexp]
  have hre_term : ∀ i ∈ s, ((ρ i : ℂ) *
      Complex.exp (↑(α i - m) * Complex.I)).re
      = ρ i * Real.cos (α i - m) := by
    intro i _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hpos : 0 < (Complex.exp (-(m : ℂ) * Complex.I) *
      (∑ i ∈ s, (ρ i : ℂ) * Complex.exp ((α i : ℂ) * Complex.I))).re := by
    rw [Finset.mul_sum, hre_sum]
    refine Finset.sum_pos (fun i his => ?_) hne
    rw [hterm i his, hre_term i his]
    exact mul_pos (hρ i his) (hcos i his)
  rw [hsum] at hpos
  simp at hpos

/-- Corollary: the argument of a slit-plane-valued continuous function with
positive-real value at `1` stays in `(-π, π)` on `cfD`. -/
private lemma cf_arg_mem_Ioo (g : ℂ → ℂ) (hcont : ContinuousOn g cfD)
    (hslit : ∀ z ∈ cfD, g z ∈ Complex.slitPlane)
    (h1 : ∃ r : ℝ, 0 < r ∧ g 1 = (r : ℂ)) :
    ∀ z ∈ cfD, Complex.arg (g z) ∈ Set.Ioo (-Real.pi) Real.pi := by
  classical
  have h1one : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_one, Complex.ofReal_mem_slitPlane]
    exact one_pos
  have h := cf_arg_add_on_D (fun _ => 1) g g continuous_const.continuousOn hcont
    (fun z _ => (one_mul (g z)).symm) (fun z _ => h1one) hslit hslit
    ⟨1, one_pos, Complex.ofReal_one.symm⟩ h1
  intro z hz
  obtain ⟨hIoo, -⟩ := h z hz
  have hIoo' : Complex.arg (1 : ℂ) + Complex.arg (g z) ∈ Set.Ioo (-Real.pi) Real.pi :=
    hIoo
  rw [Complex.arg_one, zero_add] at hIoo'
  exact hIoo'

/-- Helper for the three-term compatibility lemma: a ratio `b / a` with `a + r * b ≠ 0` for all
`r > 0` lies in the slit plane. -/
private lemma cf_slit_of_pair (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : ∀ r : ℝ, 0 < r → a + (r : ℂ) * b ≠ 0) :
    b / a ∈ Complex.slitPlane := by
  classical
  by_contra hcon
  rw [Complex.mem_slitPlane_iff, not_or] at hcon
  obtain ⟨hre, him⟩ := hcon
  rw [not_lt] at hre
  have him0 : (b / a).im = 0 := not_not.mp him
  have hcast : (((b / a).re : ℝ) : ℂ) = b / a := by
    have h := Complex.re_add_im (b / a)
    rw [him0, Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h
  have hb_eq : b = (((b / a).re : ℝ) : ℂ) * a := (div_eq_iff ha).mp hcast.symm
  by_cases hq0 : (b / a).re = 0
  · have hb0 : b = 0 := by
      rw [hb_eq, hq0, Complex.ofReal_zero, zero_mul]
    exact absurd hb0 hb
  · have hqlt : (b / a).re < 0 := lt_of_le_of_ne hre hq0
    set s : ℝ := -1 / (b / a).re with hs
    have hspos : 0 < s := by
      rw [hs]
      exact div_pos_of_neg_of_neg (by norm_num) hqlt
    have hsq : s * (b / a).re = -1 := by
      rw [hs, neg_div, neg_mul, div_mul_cancel₀ _ hq0]
    have hcon2 : a + ((s : ℝ) : ℂ) * b = 0 := by
      have e : ((s : ℝ) : ℂ) * b = -a := by
        rw [hb_eq, ← mul_assoc, ← Complex.ofReal_mul, hsq]
        simp
      rw [e]
      exact add_neg_cancel _
    exact hp s hspos hcon2

/-- Three-term compatibility from pairwise compatibility. -/
private lemma cf_three_compat (f₁ f₂ f₃ : ℂ → ℂ)
    (hcont₁ : Continuous f₁) (hcont₂ : Continuous f₂) (hcont₃ : Continuous f₃)
    (h1 : ∃ r₁ : ℝ, 0 < r₁ ∧ f₁ 1 = (r₁ : ℂ))
    (h2 : ∃ r₂ : ℝ, 0 < r₂ ∧ f₂ 1 = (r₂ : ℂ))
    (h3 : ∃ r₃ : ℝ, 0 < r₃ ∧ f₃ 1 = (r₃ : ℂ))
    (hnz : ∀ z : ℂ, 0 < z.im → f₁ z ≠ 0 ∧ f₂ z ≠ 0 ∧ f₃ z ≠ 0)
    (hp₁₂ : ∀ z : ℂ, 0 < z.im → ∀ r : ℝ, 0 < r → f₁ z + (r : ℂ) * f₂ z ≠ 0)
    (hp₁₃ : ∀ z : ℂ, 0 < z.im → ∀ r : ℝ, 0 < r → f₁ z + (r : ℂ) * f₃ z ≠ 0)
    (hp₂₃ : ∀ z : ℂ, 0 < z.im → ∀ r : ℝ, 0 < r → f₂ z + (r : ℂ) * f₃ z ≠ 0) :
    ∀ z : ℂ, 0 < z.im → ∀ c₁ c₂ c₃ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ →
      (c₁ : ℂ) * f₁ z + (c₂ : ℂ) * f₂ z + (c₃ : ℂ) * f₃ z ≠ 0 := by
  classical
  obtain ⟨r₁, hr1pos, hr1eq⟩ := h1
  obtain ⟨r₂, hr2pos, hr2eq⟩ := h2
  obtain ⟨r₃, hr3pos, hr3eq⟩ := h3
  have hne1 : ∀ z ∈ cfD, f₁ z ≠ 0 := by
    intro z hz
    have hzU : z ∈ ({z : ℂ | 0 < z.im} ∪ {1}) := hz
    rw [Set.mem_union] at hzU
    rcases hzU with hzH | rfl
    · exact (hnz _ hzH).1
    · rw [hr1eq]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr1pos)
  have hne2 : ∀ z ∈ cfD, f₂ z ≠ 0 := by
    intro z hz
    have hzU : z ∈ ({z : ℂ | 0 < z.im} ∪ {1}) := hz
    rw [Set.mem_union] at hzU
    rcases hzU with hzH | rfl
    · exact (hnz _ hzH).2.1
    · rw [hr2eq]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr2pos)
  have hne3 : ∀ z ∈ cfD, f₃ z ≠ 0 := by
    intro z hz
    have hzU : z ∈ ({z : ℂ | 0 < z.im} ∪ {1}) := hz
    rw [Set.mem_union] at hzU
    rcases hzU with hzH | rfl
    · exact (hnz _ hzH).2.2
    · rw [hr3eq]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr3pos)
  set g₁₂ : ℂ → ℂ := fun z => f₂ z / f₁ z
  set g₂₃ : ℂ → ℂ := fun z => f₃ z / f₂ z
  set g₁₃ : ℂ → ℂ := fun z => f₃ z / f₁ z
  have hcont12 : ContinuousOn g₁₂ cfD := by
    change ContinuousOn (fun z => f₂ z / f₁ z) cfD
    exact hcont₂.continuousOn.div hcont₁.continuousOn (fun z hz => hne1 z hz)
  have hcont23 : ContinuousOn g₂₃ cfD := by
    change ContinuousOn (fun z => f₃ z / f₂ z) cfD
    exact hcont₃.continuousOn.div hcont₂.continuousOn (fun z hz => hne2 z hz)
  have hcont13 : ContinuousOn g₁₃ cfD := by
    change ContinuousOn (fun z => f₃ z / f₁ z) cfD
    exact hcont₃.continuousOn.div hcont₁.continuousOn (fun z hz => hne1 z hz)
  have hg1 : ∃ rr : ℝ, 0 < rr ∧ g₁₂ 1 = (rr : ℂ) := by
    refine ⟨r₂ / r₁, div_pos hr2pos hr1pos, ?_⟩
    change f₂ 1 / f₁ 1 = ((r₂ / r₁ : ℝ) : ℂ)
    rw [hr2eq, hr1eq, Complex.ofReal_div]
  have hg2 : ∃ rr : ℝ, 0 < rr ∧ g₂₃ 1 = (rr : ℂ) := by
    refine ⟨r₃ / r₂, div_pos hr3pos hr2pos, ?_⟩
    change f₃ 1 / f₂ 1 = ((r₃ / r₂ : ℝ) : ℂ)
    rw [hr3eq, hr2eq, Complex.ofReal_div]
  have hg3 : ∃ rr : ℝ, 0 < rr ∧ g₁₃ 1 = (rr : ℂ) := by
    refine ⟨r₃ / r₁, div_pos hr3pos hr1pos, ?_⟩
    change f₃ 1 / f₁ 1 = ((r₃ / r₁ : ℝ) : ℂ)
    rw [hr3eq, hr1eq, Complex.ofReal_div]
  have hmul : ∀ z ∈ cfD, g₁₃ z = g₁₂ z * g₂₃ z := by
    intro z hz
    change f₃ z / f₁ z = (f₂ z / f₁ z) * (f₃ z / f₂ z)
    rw [div_mul_div_cancel₀' (hne2 z hz) _ _]
  have hs12 : ∀ z ∈ cfD, g₁₂ z ∈ Complex.slitPlane := by
    intro z hz
    change f₂ z / f₁ z ∈ Complex.slitPlane
    have hzU : z ∈ ({z : ℂ | 0 < z.im} ∪ {1}) := hz
    rw [Set.mem_union] at hzU
    rcases hzU with hzH | rfl
    · exact cf_slit_of_pair _ _ (hne1 z (Or.inl hzH)) (hne2 z (Or.inl hzH))
        (hp₁₂ z hzH)
    · change f₂ 1 / f₁ 1 ∈ Complex.slitPlane
      rw [hr2eq, hr1eq, ← Complex.ofReal_div, Complex.ofReal_mem_slitPlane]
      exact div_pos hr2pos hr1pos
  have hs23 : ∀ z ∈ cfD, g₂₃ z ∈ Complex.slitPlane := by
    intro z hz
    change f₃ z / f₂ z ∈ Complex.slitPlane
    have hzU : z ∈ ({z : ℂ | 0 < z.im} ∪ {1}) := hz
    rw [Set.mem_union] at hzU
    rcases hzU with hzH | rfl
    · exact cf_slit_of_pair _ _ (hne2 z (Or.inl hzH)) (hne3 z (Or.inl hzH))
        (hp₂₃ z hzH)
    · change f₃ 1 / f₂ 1 ∈ Complex.slitPlane
      rw [hr3eq, hr2eq, ← Complex.ofReal_div, Complex.ofReal_mem_slitPlane]
      exact div_pos hr3pos hr2pos
  have hs13 : ∀ z ∈ cfD, g₁₃ z ∈ Complex.slitPlane := by
    intro z hz
    change f₃ z / f₁ z ∈ Complex.slitPlane
    have hzU : z ∈ ({z : ℂ | 0 < z.im} ∪ {1}) := hz
    rw [Set.mem_union] at hzU
    rcases hzU with hzH | rfl
    · exact cf_slit_of_pair _ _ (hne1 z (Or.inl hzH)) (hne3 z (Or.inl hzH))
        (hp₁₃ z hzH)
    · change f₃ 1 / f₁ 1 ∈ Complex.slitPlane
      rw [hr3eq, hr1eq, ← Complex.ofReal_div, Complex.ofReal_mem_slitPlane]
      exact div_pos hr3pos hr1pos
  intro z hz c₁ c₂ c₃ hc₁ hc₂ hc₃
  have hzD : z ∈ cfD := Or.inl hz
  have ha12 := cf_arg_mem_Ioo g₁₂ hcont12 hs12 hg1 z hzD
  have ha23 := cf_arg_mem_Ioo g₂₃ hcont23 hs23 hg2 z hzD
  have ha13 := cf_arg_mem_Ioo g₁₃ hcont13 hs13 hg3 z hzD
  have hadd : Complex.arg (g₁₃ z) = Complex.arg (g₁₂ z) + Complex.arg (g₂₃ z) :=
    (cf_arg_add_on_D g₁₂ g₂₃ g₁₃ hcont12 hcont23 hmul hs12 hs23 hs13 hg1 hg2
      z hzD).2
  have hA12 : |Complex.arg (g₁₂ z)| < Real.pi :=
    abs_lt.mpr (Set.mem_Ioo.mp ha12)
  have hA23 : |Complex.arg (g₂₃ z)| < Real.pi :=
    abs_lt.mpr (Set.mem_Ioo.mp ha23)
  have hA13 : |Complex.arg (g₁₃ z)| < Real.pi :=
    abs_lt.mpr (Set.mem_Ioo.mp ha13)
  have hdiff : Complex.arg (g₁₂ z) - Complex.arg (g₁₃ z) = -Complex.arg (g₂₃ z) := by
    rw [hadd]; ring
  have hdiff2 : Complex.arg (g₁₃ z) - Complex.arg (g₁₂ z) = Complex.arg (g₂₃ z) := by
    rw [hadd]; ring
  set α : Fin 3 → ℝ := ![0, Complex.arg (g₁₂ z), Complex.arg (g₁₃ z)]
  set ρ : Fin 3 → ℝ := ![c₁, c₂ * ‖g₁₂ z‖, c₃ * ‖g₁₃ z‖]
  have hmemα : ∀ i : Fin 3, α i = 0 ∨ α i = Complex.arg (g₁₂ z) ∨
      α i = Complex.arg (g₁₃ z) := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hmemρ : ∀ i : Fin 3, ρ i = c₁ ∨ ρ i = c₂ * ‖g₁₂ z‖ ∨
      ρ i = c₃ * ‖g₁₃ z‖ := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hkey : ∀ x y : ℝ, (x = 0 ∨ x = Complex.arg (g₁₂ z) ∨ x = Complex.arg (g₁₃ z)) →
      (y = 0 ∨ y = Complex.arg (g₁₂ z) ∨ y = Complex.arg (g₁₃ z)) →
      |x - y| < Real.pi := by
    rintro x y (rfl | rfl | rfl) (rfl | rfl | rfl)
    · rw [sub_self, abs_zero]
      exact Real.pi_pos
    · rw [zero_sub, abs_neg]
      exact hA12
    · rw [zero_sub, abs_neg]
      exact hA13
    · rw [sub_zero]
      exact hA12
    · rw [sub_self, abs_zero]
      exact Real.pi_pos
    · rw [hdiff, abs_neg]
      exact hA23
    · rw [sub_zero]
      exact hA13
    · rw [hdiff2]
      exact hA23
    · rw [sub_self, abs_zero]
      exact Real.pi_pos
  have hpair : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ Finset.univ,
      |α i - α j| < Real.pi := by
    intro i _ j _
    exact hkey _ _ (hmemα i) (hmemα j)
  have hρpos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < ρ i := by
    intro i _
    rcases hmemρ i with h | h | h
    · rw [h]; exact hc₁
    · rw [h]
      exact mul_pos hc₂ (norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hs12 z hzD)))
    · rw [h]
      exact mul_pos hc₃ (norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hs13 z hzD)))
  have hN9 := cf_sum_rays_ne_zero (Finset.univ : Finset (Fin 3)) α ρ
    ⟨0, Finset.mem_univ 0⟩ hρpos hpair
  rw [Fin.sum_univ_three] at hN9
  have e12 : f₁ z * g₁₂ z = f₂ z := by
    change f₁ z * (f₂ z / f₁ z) = f₂ z
    exact mul_div_cancel₀ _ (hne1 z hzD)
  have e13 : f₁ z * g₁₃ z = f₃ z := by
    change f₁ z * (f₃ z / f₁ z) = f₃ z
    exact mul_div_cancel₀ _ (hne1 z hzD)
  have n12 : g₁₂ z = ↑‖g₁₂ z‖ * Complex.exp (↑(Complex.arg (g₁₂ z)) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have n13 : g₁₃ z = ↑‖g₁₃ z‖ * Complex.exp (↑(Complex.arg (g₁₃ z)) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hS : (((c₁ : ℂ) * Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I)) +
      ((((c₂ * ‖g₁₂ z‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I))) +
      ((((c₃ * ‖g₁₃ z‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg (g₁₃ z) : ℂ) * Complex.I)) ≠
      0 := hN9
  have t0 : (c₁ : ℂ) * Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I) = (c₁ : ℂ) := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have t1 : ((((c₂ * ‖g₁₂ z‖ : ℝ)) : ℂ) *
      Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I)) = (c₂ : ℂ) * g₁₂ z := by
    rw [Complex.ofReal_mul]
    conv_rhs => rw [n12]
    ring
  have t2 : ((((c₃ * ‖g₁₃ z‖ : ℝ)) : ℂ) *
      Complex.exp ((Complex.arg (g₁₃ z) : ℂ) * Complex.I)) = (c₃ : ℂ) * g₁₃ z := by
    rw [Complex.ofReal_mul]
    conv_rhs => rw [n13]
    ring
  have hfactor : (c₁ : ℂ) * f₁ z + (c₂ : ℂ) * f₂ z + (c₃ : ℂ) * f₃ z =
      f₁ z * ((((c₁ : ℂ) * Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I)) +
      ((((c₂ * ‖g₁₂ z‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I))) +
      ((((c₃ * ‖g₁₃ z‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg (g₁₃ z) : ℂ) * Complex.I))) := by
    rw [t0, t1, t2, ← e12, ← e13]
    ring
  intro hcon
  have hzero : f₁ z * ((((c₁ : ℂ) * Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I)) +
      ((((c₂ * ‖g₁₂ z‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg (g₁₂ z) : ℂ) * Complex.I))) +
      ((((c₃ * ‖g₁₃ z‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg (g₁₃ z) : ℂ) * Complex.I))) =
      0 := by
    rw [← hfactor]
    exact hcon
  exact mul_ne_zero (hne1 z hzD) hS hzero

/-- The weighted independence sum has no zeros in the upper half-plane. -/
private lemma cf_main_nonvanishing {V : Type*} [DecidableEq V] (S : Finset V)
    (G : SimpleGraph V) (w : V → ℝ) (hcf : cfClawFreeOn G S)
    (hpos : ∀ x ∈ S, 0 < w x) (z : ℂ) (hz : 0 < z.im) : cfZ G w S z ≠ 0 := by
  classical
  revert G w hcf hpos z hz
  refine Finset.strongInduction
    (p := fun S => ∀ (G : SimpleGraph V) (w : V → ℝ), cfClawFreeOn G S →
      (∀ x ∈ S, 0 < w x) → ∀ (z : ℂ), 0 < z.im → cfZ G w S z ≠ 0) ?_ S
  intro S IH G w hcf hpos z hz
  rcases Finset.eq_empty_or_nonempty S with rfl | ⟨v, hv⟩
  · rw [cf_empty_Z]
    exact one_ne_zero
  · by_cases hN : ∃ u ∈ S, G.Adj v u
    · obtain ⟨u, huS, hadjVU⟩ := hN
      have hadj : G.Adj u v := hadjVU.symm
      have hneUV : u ≠ v := Ne.symm (G.ne_of_adj hadjVU)
      have huE : u ∈ S.erase v := Finset.mem_erase.mpr ⟨hneUV, huS⟩
      have hDelU2 : cfDel G (S.erase v) u = cfDel G S u := by
        ext x
        rw [cf_mem_del, cf_mem_del]
        constructor
        · rintro ⟨hxE, hxne, hxnadj⟩
          rw [Finset.mem_erase] at hxE
          exact ⟨hxE.2, hxne, hxnadj⟩
        · rintro ⟨hxS, hxne, hxnadj⟩
          refine ⟨?_, hxne, hxnadj⟩
          rw [Finset.mem_erase]
          refine ⟨?_, hxS⟩
          intro heq
          apply hxnadj
          rw [heq]
          exact hadj
      have hN1v := cf_vertex_recurrence G w S v hv z
      have hN1u := cf_vertex_recurrence G w (S.erase v) u huE z
      rw [hDelU2] at hN1u
      have hz0 : ∀ z : ℂ, 0 < z.im → z ≠ 0 := by
        intro z hz heq
        rw [heq] at hz
        simp at hz
      have hsubEE : (S.erase v).erase u ⊂ S :=
        lt_trans (Finset.erase_ssubset huE) (Finset.erase_ssubset hv)
      have hsubEEsub : (S.erase v).erase u ⊆ S :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hDelUsub : cfDel G S u ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun x hx => ((cf_mem_del G S u x).mp hx).1, ?_⟩
        intro heq
        have hmem : u ∈ cfDel G S u := by
          rw [heq]; exact huS
        rw [cf_mem_del] at hmem
        exact hmem.2.1 rfl
      have hDelVsub : cfDel G S v ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun x hx => ((cf_mem_del G S v x).mp hx).1, ?_⟩
        intro heq
        have hmem : v ∈ cfDel G S v := by
          rw [heq]; exact hv
        rw [cf_mem_del] at hmem
        exact hmem.2.1 rfl
      have huDelU : u ∉ cfDel G S u := by
        intro h
        exact ((cf_mem_del G S u u).mp h).2.1 rfl
      have hnzF1 : ∀ z : ℂ, 0 < z.im → cfZ G w ((S.erase v).erase u) z ≠ 0 := by
        intro z hz
        exact IH _ hsubEE G w (cf_clawFree_mono G S _ hcf hsubEEsub)
          (fun x hx => hpos x (hsubEEsub hx)) z hz
      have hnzF2 : ∀ z : ℂ, 0 < z.im →
          (w u : ℂ) * z * cfZ G w (cfDel G S u) z ≠ 0 := by
        intro z hz
        exact mul_ne_zero (mul_ne_zero
          (Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos u huS))) (hz0 z hz))
          (IH _ hDelUsub G w
            (cf_clawFree_mono G S _ hcf
              (fun x hx => ((cf_mem_del G S u x).mp hx).1))
            (fun x hx => hpos x ((cf_mem_del G S u x).mp hx).1) z hz)
      have hnzF3 : ∀ z : ℂ, 0 < z.im → z * cfZ G w (cfDel G S v) z ≠ 0 := by
        intro z hz
        exact mul_ne_zero (hz0 z hz)
          (IH _ hDelVsub G w
            (cf_clawFree_mono G S _ hcf
              (fun x hx => ((cf_mem_del G S v x).mp hx).1))
            (fun x hx => hpos x ((cf_mem_del G S v x).mp hx).1) z hz)
      have hc1 : Continuous (fun z => cfZ G w ((S.erase v).erase u) z) :=
        cf_continuous G w _
      have hc2 : Continuous
          (fun z => (w u : ℂ) * z * cfZ G w (cfDel G S u) z) :=
        (continuous_const.mul continuous_id).mul (cf_continuous G w _)
      have hc3 : Continuous (fun z => z * cfZ G w (cfDel G S v) z) :=
        continuous_id.mul (cf_continuous G w _)
      obtain ⟨R1, hR1ge, hR1val⟩ := cf_at_one G w ((S.erase v).erase u)
        (fun x hx => (hpos x (hsubEEsub hx)).le)
      obtain ⟨R2, hR2ge, hR2val⟩ := cf_at_one G w (cfDel G S u)
        (fun x hx => (hpos x ((cf_mem_del G S u x).mp hx).1).le)
      obtain ⟨R3, hR3ge, hR3val⟩ := cf_at_one G w (cfDel G S v)
        (fun x hx => (hpos x ((cf_mem_del G S v x).mp hx).1).le)
      have hg1 : ∃ r : ℝ, 0 < r ∧
          (fun z => cfZ G w ((S.erase v).erase u) z) 1 = (r : ℂ) :=
        ⟨R1, lt_of_lt_of_le one_pos hR1ge, hR1val⟩
      have hg2 : ∃ r : ℝ, 0 < r ∧
          (fun z => (w u : ℂ) * z * cfZ G w (cfDel G S u) z) 1 = (r : ℂ) := by
        refine ⟨w u * R2, mul_pos (hpos u huS)
          (lt_of_lt_of_le one_pos hR2ge), ?_⟩
        change (w u : ℂ) * 1 * cfZ G w (cfDel G S u) 1 = ((w u * R2 : ℝ) : ℂ)
        rw [mul_one, hR2val, Complex.ofReal_mul]
      have hg3 : ∃ r : ℝ, 0 < r ∧
          (fun z => z * cfZ G w (cfDel G S v) z) 1 = (r : ℂ) := by
        refine ⟨R3, lt_of_lt_of_le one_pos hR3ge, ?_⟩
        change (1 : ℂ) * cfZ G w (cfDel G S v) 1 = ((R3 : ℝ) : ℂ)
        rw [one_mul, hR3val]
      have hnz : ∀ z : ℂ, 0 < z.im →
          (fun z => cfZ G w ((S.erase v).erase u) z) z ≠ 0 ∧
          (fun z => (w u : ℂ) * z * cfZ G w (cfDel G S u) z) z ≠ 0 ∧
          (fun z => z * cfZ G w (cfDel G S v) z) z ≠ 0 := by
        intro z hz
        exact ⟨hnzF1 z hz, hnzF2 z hz, hnzF3 z hz⟩
      have hp12 : ∀ z : ℂ, 0 < z.im → ∀ r : ℝ, 0 < r →
          (fun z => cfZ G w ((S.erase v).erase u) z) z +
          (r : ℂ) * ((fun z => (w u : ℂ) * z * cfZ G w (cfDel G S u) z) z) ≠ 0 := by
        intro z hz r hr
        change cfZ G w ((S.erase v).erase u) z +
          (r : ℂ) * ((w u : ℂ) * z * cfZ G w (cfDel G S u) z) ≠ 0
        have h1N1 := cf_vertex_recurrence G (Function.update w u (r * w u))
          (S.erase v) u huE z
        have hwu : Function.update w u (r * w u) u = r * w u := by
          simp only [Function.update_self]
        have hUpdEE : cfZ G (Function.update w u (r * w u)) ((S.erase v).erase u) z =
            cfZ G w ((S.erase v).erase u) z :=
          cf_congr_update_outside G w ((S.erase v).erase u) z u
            (Finset.notMem_erase u (S.erase v)) (r * w u)
        have hUpdDel : cfZ G (Function.update w u (r * w u)) (cfDel G S u) z =
            cfZ G w (cfDel G S u) z :=
          cf_congr_update_outside G w (cfDel G S u) z u huDelU (r * w u)
        have hposU' : ∀ x ∈ S.erase v, 0 < Function.update w u (r * w u) x := by
          intro x hx
          rw [Finset.mem_erase] at hx
          by_cases hequ : x = u
          · rw [hequ]
            simp only [Function.update_self]
            exact mul_pos hr (hpos u huS)
          · rw [Function.update_of_ne hequ (r * w u) w]
            exact hpos x hx.2
        have eEq : cfZ G w ((S.erase v).erase u) z +
            (r : ℂ) * ((w u : ℂ) * z * cfZ G w (cfDel G S u) z) =
            cfZ G (Function.update w u (r * w u)) (S.erase v) z := by
          rw [h1N1, hDelU2, ← hUpdEE, ← hUpdDel, hwu, Complex.ofReal_mul]
          ring
        rw [eEq]
        exact IH _ (Finset.erase_ssubset hv) G (Function.update w u (r * w u))
          (cf_clawFree_mono G S _ hcf (Finset.erase_subset v S)) hposU' z hz
      have hp13 : ∀ z : ℂ, 0 < z.im → ∀ r : ℝ, 0 < r →
          (fun z => cfZ G w ((S.erase v).erase u) z) z +
          (r : ℂ) * ((fun z => z * cfZ G w (cfDel G S v) z) z) ≠ 0 := by
        intro z hz r hr
        change cfZ G w ((S.erase v).erase u) z +
          (r : ℂ) * (z * cfZ G w (cfDel G S v) z) ≠ 0
        have hDelV2 : cfDel G (S.erase u) v = cfDel G S v := by
          ext x
          rw [cf_mem_del, cf_mem_del]
          constructor
          · rintro ⟨hxE, hxne, hxnadj⟩
            rw [Finset.mem_erase] at hxE
            exact ⟨hxE.2, hxne, hxnadj⟩
          · rintro ⟨hxS, hxne, hxnadj⟩
            refine ⟨?_, hxne, hxnadj⟩
            rw [Finset.mem_erase]
            refine ⟨?_, hxS⟩
            intro heq
            apply hxnadj
            rw [heq]
            exact hadjVU
        have hvE : v ∈ S.erase u :=
          Finset.mem_erase.mpr ⟨Ne.symm hneUV, hv⟩
        have hEE : (S.erase u).erase v = (S.erase v).erase u :=
          Finset.erase_right_comm
        have h1N1 := cf_vertex_recurrence G (Function.update w v r)
          (S.erase u) v hvE z
        have hwv : Function.update w v r v = r := by
          simp only [Function.update_self]
        have hvEE : v ∉ (S.erase v).erase u :=
          fun h => Finset.notMem_erase v S ((Finset.erase_subset _ _) h)
        have hvDel : v ∉ cfDel G S v := by
          intro h
          exact ((cf_mem_del G S v v).mp h).2.1 rfl
        have hUpdEE : cfZ G (Function.update w v r) ((S.erase v).erase u) z =
            cfZ G w ((S.erase v).erase u) z :=
          cf_congr_update_outside G w ((S.erase v).erase u) z v hvEE r
        have hUpdDel : cfZ G (Function.update w v r) (cfDel G S v) z =
            cfZ G w (cfDel G S v) z :=
          cf_congr_update_outside G w (cfDel G S v) z v hvDel r
        have hposU'' : ∀ x ∈ S.erase u, 0 < Function.update w v r x := by
          intro x hx
          rw [Finset.mem_erase] at hx
          by_cases heqv : x = v
          · rw [heqv]
            simp only [Function.update_self]
            exact hr
          · rw [Function.update_of_ne heqv r w]
            exact hpos x hx.2
        have eEq : cfZ G w ((S.erase v).erase u) z +
            (r : ℂ) * (z * cfZ G w (cfDel G S v) z) =
            cfZ G (Function.update w v r) (S.erase u) z := by
          rw [h1N1, hEE, hDelV2, ← hUpdEE, ← hUpdDel, hwv]
          ring
        rw [eEq]
        exact IH _ (Finset.erase_ssubset huS) G (Function.update w v r)
          (cf_clawFree_mono G S _ hcf (Finset.erase_subset u S)) hposU'' z hz
      have hp23 : ∀ z : ℂ, 0 < z.im → ∀ r : ℝ, 0 < r →
          (fun z => (w u : ℂ) * z * cfZ G w (cfDel G S u) z) z +
          (r : ℂ) * ((fun z => z * cfZ G w (cfDel G S v) z) z) ≠ 0 := by
        intro z hz r hr
        change (w u : ℂ) * z * cfZ G w (cfDel G S u) z +
          (r : ℂ) * (z * cfZ G w (cfDel G S v) z) ≠ 0
        obtain ⟨hid7, hpos7⟩ := cf_contract_identity G S u v w (w u) r
          huS hv hadj hcf hpos (hpos u huS) hr z
        have hS'sub : cfS' G S u v ⊂ S := (cf_contract_ssubset G S u v huS).2.2.2
        have hcf' : cfClawFreeOn
            (cfContract G (cfPrivA G S u v) (cfPrivB G S u v)) (cfS' G S u v) :=
          cf_contract_clawFreeOn G S u v huS hv hadj hcf
        have hnzC := IH _ hS'sub _ _ hcf' hpos7 z hz
        have hwr : (w u + r : ℝ) ≠ 0 := ne_of_gt (add_pos (hpos u huS) hr)
        have eEq : (w u : ℂ) * z * cfZ G w (cfDel G S u) z +
            (r : ℂ) * (z * cfZ G w (cfDel G S v) z) =
            z * ((((w u + r : ℝ)) : ℂ) *
              cfZ (cfContract G (cfPrivA G S u v) (cfPrivB G S u v))
                (cfW w (cfPrivA G S u v) (cfPrivB G S u v) (w u) r)
                (cfS' G S u v) z) := by
          have e : (w u : ℂ) * z * cfZ G w (cfDel G S u) z +
              (r : ℂ) * (z * cfZ G w (cfDel G S v) z) =
              z * (((w u : ℂ) * cfZ G w (cfDel G S u) z) +
                ((r : ℂ) * cfZ G w (cfDel G S v) z)) := by ring
          rw [e, hid7]
        rw [eEq]
        exact mul_ne_zero (hz0 z hz) (mul_ne_zero
          (Complex.ofReal_ne_zero.mpr hwr) hnzC)
      have hN10 := cf_three_compat
        (fun z => cfZ G w ((S.erase v).erase u) z)
        (fun z => (w u : ℂ) * z * cfZ G w (cfDel G S u) z)
        (fun z => z * cfZ G w (cfDel G S v) z)
        hc1 hc2 hc3 hg1 hg2 hg3 hnz hp12 hp13 hp23 z hz
        1 1 (w v) one_pos one_pos (hpos v hv)
      have hdecomp : cfZ G w S z =
          (((1 : ℝ)) : ℂ) * cfZ G w ((S.erase v).erase u) z +
          (((1 : ℝ)) : ℂ) * ((w u : ℂ) * z * cfZ G w (cfDel G S u) z) +
          (((w v : ℝ)) : ℂ) * (z * cfZ G w (cfDel G S v) z) := by
        rw [hN1v, hN1u]
        simp only [Complex.ofReal_one, one_mul, mul_assoc]
      rw [hdecomp]
      exact hN10
    · have hN' : ∀ u ∈ S, ¬ G.Adj v u := by
        intro u hu hadj2
        exact hN ⟨u, hu, hadj2⟩
      have hDel : cfDel G S v = S.erase v := by
        ext x
        rw [cf_mem_del, Finset.mem_erase]
        constructor
        · rintro ⟨hxS, hxne, -⟩
          exact ⟨hxne, hxS⟩
        · rintro ⟨hxne, hxS⟩
          exact ⟨hxS, hxne, fun hadj2 => hN' x hxS hadj2⟩
      have hN1 := cf_vertex_recurrence G w S v hv z
      rw [hDel] at hN1
      have him : ((1 : ℂ) + (w v : ℂ) * z).im = w v * z.im := by
        rw [Complex.add_im]
        simp only [Complex.one_im, zero_add, Complex.im_ofReal_mul]
      have h1 : (1 : ℂ) + (w v : ℂ) * z ≠ 0 := by
        intro hcon
        rw [hcon] at him
        simp only [Complex.zero_im] at him
        have hpos2 := mul_pos (hpos v hv) hz
        linarith
      have hEsub : S.erase v ⊂ S := Finset.erase_ssubset hv
      have hnzE := IH _ hEsub G w
        (cf_clawFree_mono G S _ hcf (Finset.erase_subset v S))
        (fun x hx => hpos x (Finset.mem_of_mem_erase hx)) z hz
      have hfactor : cfZ G w S z =
          ((1 : ℂ) + (w v : ℂ) * z) * cfZ G w (S.erase v) z := by
        rw [hN1]; ring
      rw [hfactor]
      exact mul_ne_zero h1 hnzE

/-- Evaluation of the mapped `independencePoly` is `cfZ` with unit weights. -/
private lemma cf_eval_independencePoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : ℂ) :
    Polynomial.eval z (((independencePoly G).map (Int.castRingHom ℝ)).map
      Complex.ofRealHom) = cfZ G (fun _ => 1) Finset.univ z := by
  classical
  have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext n
    simp
  have hterm : ∀ (k : ℕ) (n : ℤ),
      Polynomial.eval z (((n • (Polynomial.X ^ k : Polynomial ℤ))).map
        (Int.castRingHom ℂ)) = (n : ℂ) * z ^ k := by
    intro k n
    rw [zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_intCast,
      Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_intCast, Polynomial.eval_pow,
      Polynomial.eval_X]
  have hprod : ∀ J : Finset V,
      ∏ x ∈ J, ((((fun _ => (1 : ℝ)) x) : ℝ) : ℂ) * z = z ^ J.card := by
    intro J
    simp only [Complex.ofReal_one, one_mul, Finset.prod_const]
  have hRHS : cfZ G (fun _ => 1) Finset.univ z =
      ∑ J ∈ (Finset.univ : Finset (Finset V)),
        (if cfIndep G J then z ^ J.card else 0) := by
    simp only [cfZ, Finset.powerset_univ]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    by_cases hJ : cfIndep G J
    · rw [ite_eq_left hJ, ite_eq_left hJ, hprod J]
    · rw [ite_eq_right hJ, ite_eq_right hJ]
  have hmem : ∀ J ∈ (Finset.univ : Finset (Finset V)),
      J.card ∈ Finset.range (Fintype.card V + 1) := by
    intro J _
    rw [Finset.mem_range]
    have hle := Finset.card_le_univ J
    omega
  have hfilter : ∀ k : ℕ, Finset.univ.filter
      (fun s : Finset V => s.card = k ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b) =
      Finset.univ.filter (fun s : Finset V => s.card = k ∧ cfIndep G s) := by
    intro k
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2⟩
  have hfib : ∀ (k : ℕ),
      (((Finset.univ.filter (fun s : Finset V => s.card = k ∧ cfIndep G s)).card : ℕ) : ℂ) *
        z ^ k =
      ∑ J ∈ Finset.univ.filter (fun J : Finset V => J.card = k),
        (if cfIndep G J then z ^ J.card else (0 : ℂ)) := by
    intro k
    have hJcard : ∀ J ∈ Finset.univ.filter (fun J : Finset V => J.card = k),
        (if cfIndep G J then z ^ J.card else (0 : ℂ)) =
        (if cfIndep G J then z ^ k else 0) := by
      intro J hJ
      rw [Finset.mem_filter] at hJ
      rw [hJ.2]
    have hsum : (∑ J ∈ Finset.univ.filter (fun J : Finset V => J.card = k),
          (if cfIndep G J then z ^ J.card else (0 : ℂ))) =
        ∑ J ∈ Finset.univ.filter (fun J : Finset V => J.card = k),
          (if cfIndep G J then z ^ k else 0) :=
      Finset.sum_congr rfl (fun J hJ => hJcard J hJ)
    rw [hsum, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const,
      nsmul_eq_mul]
  rw [hRHS, ← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset V)))
    (t := Finset.range (Fintype.card V + 1)) (g := Finset.card) hmem
    (fun J => if cfIndep G J then z ^ J.card else 0)]
  unfold independencePoly
  rw [Polynomial.map_map _ _ _, hcomp, Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hfilter k, hterm, Int.cast_natCast]
  exact hfib k

/-- A real polynomial with no zeros in the open upper half-plane splits. -/
private lemma cf_splits_of_no_roots_upperHalfPlane (p : Polynomial ℝ)
    (h : ∀ z : ℂ, 0 < z.im → Polynomial.eval z (p.map Complex.ofRealHom) ≠ 0) :
    p.Splits := by
  classical
  have hmap : p.map Complex.ofRealHom = p.map (algebraMap ℝ ℂ) := by
    have e : Complex.ofRealHom = algebraMap ℝ ℂ := by
      ext x
      simp
    rw [e]
  have hq0 : p.map Complex.ofRealHom ≠ 0 := by
    intro h0
    have hI := h Complex.I (Complex.I_im.symm ▸ one_pos)
    rw [h0, Polynomial.eval_zero] at hI
    exact hI rfl
  have hconj : ∀ α : ℂ, Polynomial.eval α (p.map Complex.ofRealHom) = 0 →
      Polynomial.eval (starRingEnd ℂ α) (p.map Complex.ofRealHom) = 0 := by
    intro α hα
    rw [hmap, Polynomial.eval_map_algebraMap] at hα ⊢
    rw [Polynomial.aeval_conj, hα, map_zero]
  have himc : ∀ α : ℂ, (starRingEnd ℂ α).im = -α.im :=
    fun α => RCLike.conj_im (K := ℂ) α
  have hreal : ∀ α ∈ (p.map Complex.ofRealHom).roots, α.im = 0 := by
    intro α hα
    have hroot : Polynomial.eval α (p.map Complex.ofRealHom) = 0 :=
      (Polynomial.mem_roots hq0).mp hα
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpos : 0 < (starRingEnd ℂ α).im := by rw [himc α]; linarith
      exact h _ hpos (hconj α hroot)
    · exact h α hgt hroot
  have hcard : (p.map Complex.ofRealHom).roots.card = p.natDegree := by
    have hsplitC : (p.map Complex.ofRealHom).Splits := IsAlgClosed.splits _
    have h1 := hsplitC.natDegree_eq_card_roots
    rw [Polynomial.natDegree_map] at h1
    exact h1.symm
  have himg : ∀ α ∈ (p.map Complex.ofRealHom).roots,
      α = ⇑Complex.ofRealHom α.re := by
    intro α hα
    have hre : α.im = 0 := hreal α hα
    change α = ((α.re : ℝ) : ℂ)
    apply Complex.ext
    · simp
    · simp [hre]
  have hinj : Function.Injective ⇑Complex.ofRealHom := Complex.ofReal_injective
  obtain ⟨m, hm⟩ : ∃ m : Multiset ℝ,
      m = (p.map Complex.ofRealHom).roots.map Complex.re := ⟨_, rfl⟩
  have hroots_eq : (p.map Complex.ofRealHom).roots = m.map ⇑Complex.ofRealHom := by
    rw [hm, Multiset.map_map]
    have e : ∀ α ∈ (p.map Complex.ofRealHom).roots,
        ((⇑Complex.ofRealHom ∘ Complex.re) α) = (fun _ => α) α :=
      fun α hα => (himg α hα).symm
    rw [Multiset.map_congr rfl e, Multiset.map_id']
  have hfac : ∀ r : ℝ, (Polynomial.X - Polynomial.C (⇑Complex.ofRealHom r) : Polynomial ℂ) =
      (Polynomial.X - Polynomial.C r).map Complex.ofRealHom := by
    intro r
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hprod_map : (((m.map ⇑Complex.ofRealHom).map
      fun a => Polynomial.X - Polynomial.C a).prod : Polynomial ℂ) =
      ((m.map fun r => Polynomial.X - Polynomial.C r).prod).map Complex.ofRealHom := by
    have e1 : ((m.map ⇑Complex.ofRealHom).map fun a => Polynomial.X - Polynomial.C a) =
        m.map ((fun a => Polynomial.X - Polynomial.C a) ∘ ⇑Complex.ofRealHom) :=
      Multiset.map_map _ _ _
    rw [e1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun r _ => ?_))
    exact hfac r
  have hC := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := p.map Complex.ofRealHom) (by rw [Polynomial.natDegree_map]; exact hcard)
  rw [hroots_eq, hprod_map] at hC
  have hlead : (p.map Complex.ofRealHom).leadingCoeff =
      Complex.ofRealHom p.leadingCoeff :=
    Polynomial.leadingCoeff_map _
  have hCmap : (Polynomial.C p.leadingCoeff).map Complex.ofRealHom =
      Polynomial.C (p.map Complex.ofRealHom).leadingCoeff := by
    rw [Polynomial.map_C, hlead]
  have hqeq : p.map Complex.ofRealHom =
      (Polynomial.C p.leadingCoeff *
        (m.map fun r => Polynomial.X - Polynomial.C r).prod).map
        Complex.ofRealHom := by
    rw [Polynomial.map_mul, hCmap]
    exact hC.symm
  have hp_eq : p = Polynomial.C p.leadingCoeff *
      (m.map fun r => Polynomial.X - Polynomial.C r).prod :=
    Polynomial.map_injective Complex.ofRealHom hinj hqeq
  exact Polynomial.splits_iff_exists_multiset.mpr ⟨m, hp_eq⟩

@[expose] public section

/-- **Chudnovsky–Seymour theorem.** Let $G$ be a claw-free simple graph on a finite vertex set
$V$, and let $I(G) = \sum_{k=0}^{|V|} i_k X^k \in \mathbb{Z}[X]$ be its independence polynomial,
where $i_k$ is the number of independent sets of $G$ with $k$ vertices. Then $I(G)$, viewed as a
polynomial with real coefficients, splits over $\mathbb{R}$: it is a constant times a product of
linear factors $X - r$ with $r \in \mathbb{R}$, so all its roots are real.

Proves `Wanted` entry `independence_poly_of_claw_free_splits`.

Source: Moussa Benoumhani, "On the Modes of the Independence Polynomial of
the Centipede," Journal of Integer Sequences 15 (2012), Article 12.5.1,
unnumbered Chudnovsky–Seymour theorem, lines 142–144,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Benoumhani/benoumhani8.tex
quoting M. Chudnovsky and P. Seymour, "The roots of the independence
polynomial of a clawfree graph," J. Combin. Theory Ser. B 97 (2007), 350–357
(biblio lines 499–501). -/
public theorem independence_poly_of_claw_free_splits :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      clawFree G → ((independencePoly G).map (Int.castRingHom ℝ)).Splits := by
  intro V _ _ G _ hcf
  apply cf_splits_of_no_roots_upperHalfPlane
  intro z hz
  rw [cf_eval_independencePoly]
  exact cf_main_nonvanishing _ _ _ (cf_clawFree_univ _ hcf)
    (fun _ _ => one_pos) z hz

/-- **Claw-free finite graphs have no induced claw.** Let $G$ be a simple graph on a finite
vertex set. Then $G$ is claw-free if and only if the claw $K_{1,3}$, the star graph on four
vertices whose center is adjacent to the other three, is not an induced subgraph of $G$, that is,
there is no injective map from its vertices to those of $G$ that preserves both adjacency and
nonadjacency. -/
public theorem clawFree_iff_not_isIndContained {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    clawFree G ↔ ¬ (SimpleGraph.starGraph (0 : Fin 4)).IsIndContained G := by
  constructor
  · intro hcf ⟨f⟩
    apply hcf
    have inj := f.injective
    have e01 : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 1 :=
      SimpleGraph.starGraph_adj.mpr ⟨by decide, Or.inl rfl⟩
    have e02 : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 2 :=
      SimpleGraph.starGraph_adj.mpr ⟨by decide, Or.inl rfl⟩
    have e03 : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 3 :=
      SimpleGraph.starGraph_adj.mpr ⟨by decide, Or.inl rfl⟩
    have n12 : ¬ (SimpleGraph.starGraph (0 : Fin 4)).Adj 1 2 := by
      rw [SimpleGraph.starGraph_adj]
      decide
    have n13 : ¬ (SimpleGraph.starGraph (0 : Fin 4)).Adj 1 3 := by
      rw [SimpleGraph.starGraph_adj]
      decide
    have n23 : ¬ (SimpleGraph.starGraph (0 : Fin 4)).Adj 2 3 := by
      rw [SimpleGraph.starGraph_adj]
      decide
    exact ⟨f 0, f 1, f 2, f 3,
      fun heq => (by decide : (0 : Fin 4) ≠ 1) (inj heq),
      fun heq => (by decide : (0 : Fin 4) ≠ 2) (inj heq),
      fun heq => (by decide : (0 : Fin 4) ≠ 3) (inj heq),
      fun heq => (by decide : (1 : Fin 4) ≠ 2) (inj heq),
      fun heq => (by decide : (1 : Fin 4) ≠ 3) (inj heq),
      fun heq => (by decide : (2 : Fin 4) ≠ 3) (inj heq),
      f.map_adj_iff.mpr e01, f.map_adj_iff.mpr e02, f.map_adj_iff.mpr e03,
      fun h => n12 (f.map_adj_iff.mp h),
      fun h => n13 (f.map_adj_iff.mp h),
      fun h => n23 (f.map_adj_iff.mp h)⟩
  · intro hnd
    unfold clawFree
    rintro ⟨c, l₁, l₂, l₃, hc1, hc2, hc3, h12, h13, h23,
      ha1, ha2, ha3, hn12, hn13, hn23⟩
    apply hnd
    refine ⟨⟨⟨![c, l₁, l₂, l₃], ?_⟩, ?_⟩⟩
    · intro a b hab
      fin_cases a <;> fin_cases b
      <;> first
        | rfl
        | exact (hc1 hab).elim
        | exact (Ne.symm hc1 hab).elim
        | exact (hc2 hab).elim
        | exact (Ne.symm hc2 hab).elim
        | exact (hc3 hab).elim
        | exact (Ne.symm hc3 hab).elim
        | exact (h12 hab).elim
        | exact (Ne.symm h12 hab).elim
        | exact (h13 hab).elim
        | exact (Ne.symm h13 hab).elim
        | exact (h23 hab).elim
        | exact (Ne.symm h23 hab).elim
    · intro a b
      fin_cases a <;> fin_cases b <;> simp only [SimpleGraph.starGraph_adj]
      <;> first
        | exact iff_of_true ha1 (by decide)
        | exact iff_of_true ha1.symm (by decide)
        | exact iff_of_true ha2 (by decide)
        | exact iff_of_true ha2.symm (by decide)
        | exact iff_of_true ha3 (by decide)
        | exact iff_of_true ha3.symm (by decide)
        | exact iff_of_false G.irrefl (by decide)
        | exact iff_of_false hn12 (by decide)
        | exact iff_of_false (fun h => hn12 h.symm) (by decide)
        | exact iff_of_false hn13 (by decide)
        | exact iff_of_false (fun h => hn13 h.symm) (by decide)
        | exact iff_of_false hn23 (by decide)
        | exact iff_of_false (fun h => hn23 h.symm) (by decide)

/-- **Coefficients of the independence polynomial.** Let $G$ be a simple graph on a finite vertex
set $V$, and let $I(G) = \sum_{k=0}^{|V|} i_k X^k \in \mathbb{Z}[X]$ be its independence
polynomial, where $i_k$ is the number of independent sets of $G$ with $k$ vertices. Then for every
natural number $k$, the coefficient of $X^k$ in $I(G)$ is the number of independent sets of $G$
with exactly $k$ vertices. -/
public theorem independencePoly_coeff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (independencePoly G).coeff k = ((G.indepSetFinset k).card : ℤ) := by
  classical
  have hindep : ∀ s : Finset V,
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b) ↔ G.IsIndepSet (s : Set V) := by
    intro s
    rw [SimpleGraph.isIndepSet_iff]
    constructor
    · intro h a ha b hb hne
      exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hne
    · intro h a ha b hb hne
      exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne
  have hcard : ∀ j : ℕ, (Finset.univ.filter
        (fun s : Finset V => s.card = j ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b)).card
        = (G.indepSetFinset j).card := by
    intro j
    congr 1
    ext s
    constructor
    · intro h
      obtain ⟨-, hcard, hforall⟩ := Finset.mem_filter.mp h
      rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff]
      exact ⟨(hindep s).mp hforall, hcard⟩
    · intro h
      rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff] at h
      obtain ⟨hI, hcard⟩ := h
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ s, hcard, (hindep s).mpr hI⟩
  unfold independencePoly
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ j : ℕ, ((((Finset.univ.filter
        (fun s : Finset V => s.card = j ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b)).card : ℤ))
        • (Polynomial.X ^ j : Polynomial ℤ)).coeff k
      = if k = j then ((G.indepSetFinset j).card : ℤ) else 0 := by
    intro j
    rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, hcard j]
    split_ifs <;> simp
  simp only [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
  by_cases h : k ≤ Fintype.card V
  · simp [h]
  · have hempty : G.indepSetFinset k = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff] at hs
      have hle := Finset.card_le_univ s
      omega
    simp [hempty, h]

/-- **Evaluating the independence polynomial.** Let $G$ be a simple graph on a finite vertex set
$V$, and let $I(G) = \sum_{k=0}^{|V|} i_k X^k \in \mathbb{Z}[X]$ be its independence polynomial,
where $i_k$ is the number of independent sets of $G$ with $k$ vertices. Then for every element
$x$ of a commutative ring $R$, the value of $I(G)$ at $x$ is $\sum_S x^{|S|}$, the sum running
over all independent sets $S \subseteq V$ of $G$, the empty set included. -/
public theorem aeval_independencePoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {R : Type*} [CommRing R] (x : R) :
    Polynomial.aeval x (independencePoly G)
      = ∑ s ∈ Finset.univ.filter (fun s : Finset V => G.IsIndepSet (s : Set V)),
        x ^ s.card := by
  classical
  have hindep : ∀ s : Finset V,
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b) ↔ G.IsIndepSet (s : Set V) := by
    intro s
    rw [SimpleGraph.isIndepSet_iff]
    constructor
    · intro h a ha b hb hne
      exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hne
    · intro h a ha b hb hne
      exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne
  have hmem : ∀ s ∈ Finset.univ.filter (fun s : Finset V => G.IsIndepSet (s : Set V)),
      s.card ∈ Finset.range (Fintype.card V + 1) := by
    intro s _
    rw [Finset.mem_range]
    have hle := Finset.card_le_univ s
    omega
  have hfibeq : ∀ j : ℕ, (Finset.univ.filter
        (fun s : Finset V => G.IsIndepSet (s : Set V))).filter (fun s => s.card = j)
      = Finset.univ.filter
        (fun s : Finset V => s.card = j ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b) := by
    intro j
    ext s
    constructor
    · intro h
      obtain ⟨hmemU, hcard⟩ := Finset.mem_filter.mp h
      obtain ⟨-, hI⟩ := Finset.mem_filter.mp hmemU
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ s, hcard, (hindep s).mp hI⟩
    · intro h
      obtain ⟨-, hcard, hforall⟩ := Finset.mem_filter.mp h
      rw [Finset.mem_filter]
      refine ⟨?_, hcard⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ s, (hindep s).mpr hforall⟩
  have hterm : ∀ j ∈ Finset.range (Fintype.card V + 1),
      Polynomial.aeval x ((((Finset.univ.filter
        (fun s : Finset V => s.card = j ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b)).card : ℤ))
        • (Polynomial.X ^ j : Polynomial ℤ))
      = ∑ s ∈ (Finset.univ.filter
        (fun s : Finset V => G.IsIndepSet (s : Set V))).filter (fun s => s.card = j),
        x ^ s.card := by
    intro j _
    have hconst : ∀ s ∈ (Finset.univ.filter
          (fun s : Finset V => G.IsIndepSet (s : Set V))).filter (fun s => s.card = j),
        x ^ s.card = x ^ j := by
      intro s hs
      have hcard : s.card = j := (Finset.mem_filter.mp hs).2
      rw [hcard]
    rw [map_smul, map_pow, Polynomial.aeval_X, zsmul_eq_mul, Int.cast_natCast, hfibeq j]
    have hconstB : ∀ s ∈ Finset.univ.filter
          (fun s : Finset V => s.card = j ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b),
        x ^ s.card = x ^ j := by
      intro s hs
      have hcard : s.card = j := (Finset.mem_filter.mp hs).2.1
      rw [hcard]
    rw [Finset.sum_congr rfl (fun s hs => hconstB s hs)]
    rw [Finset.sum_const, nsmul_eq_mul]
  unfold independencePoly
  rw [map_sum]
  exact ((Finset.sum_congr rfl (fun j hj => hterm j hj)).trans
    (Finset.sum_fiberwise_of_maps_to hmem _))

/-- **Independence polynomial of the edgeless graph.** Let $V$ be a finite set. For a simple
graph $G$ on $V$, let $I(G) = \sum_{k=0}^{|V|} i_k X^k \in \mathbb{Z}[X]$ be its independence
polynomial, where $i_k$ is the number of independent sets of $G$ with $k$ vertices. If $G$ is the
graph on $V$ with no edges, then $I(G) = (1 + X)^{|V|}$. -/
public theorem independencePoly_bot {V : Type*} [Fintype V] [DecidableEq V] :
    independencePoly (⊥ : SimpleGraph V) = (1 + Polynomial.X) ^ Fintype.card V := by
  classical
  rw [Polynomial.ext_iff]
  intro k
  have hindep : ∀ s : Finset V, (⊥ : SimpleGraph V).IsIndepSet (s : Set V) := by
    intro s
    rw [SimpleGraph.isIndepSet_iff]
    intro a _ b _ _
    simp only [SimpleGraph.bot_adj, not_false_eq_true]
  have hset : (⊥ : SimpleGraph V).indepSetFinset k = Finset.univ.powersetCard k := by
    ext s
    constructor
    · intro h
      rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff] at h
      obtain ⟨-, hcard⟩ := h
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ s, hcard⟩
    · intro h
      rw [Finset.mem_powersetCard] at h
      obtain ⟨-, hcard⟩ := h
      rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff]
      exact ⟨hindep s, hcard⟩
  rw [independencePoly_coeff, Polynomial.coeff_one_add_X_pow, hset,
    Finset.card_powersetCard, Finset.card_univ]

/-- **Independence polynomial of the complete graph.** Let $V$ be a finite set. For a simple
graph $G$ on $V$, let $I(G) = \sum_{k=0}^{|V|} i_k X^k \in \mathbb{Z}[X]$ be its independence
polynomial, where $i_k$ is the number of independent sets of $G$ with $k$ vertices. If $G$ is the
complete graph on $V$, then $I(G) = 1 + |V|\,X$. -/
public theorem independencePoly_top {V : Type*} [Fintype V] [DecidableEq V] :
    independencePoly (⊤ : SimpleGraph V)
      = 1 + Polynomial.C (Fintype.card V : ℤ) * Polynomial.X := by
  classical
  have hindep : ∀ s : Finset V,
      (⊤ : SimpleGraph V).IsIndepSet (s : Set V) ↔ s.card ≤ 1 := by
    intro s
    constructor
    · intro h
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hne
      have hmem1 : a ∈ (s : Set V) := Finset.mem_coe.mpr ha
      have hmem2 : b ∈ (s : Set V) := Finset.mem_coe.mpr hb
      have hpair : ¬ (⊤ : SimpleGraph V).Adj a b := h hmem1 hmem2 hne
      exact hpair ((SimpleGraph.top_adj a b).mpr hne)
    · intro h
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne
      have heq : a = b :=
        (Finset.card_le_one.mp h) a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb)
      exact absurd heq hne
  rw [Polynomial.ext_iff]
  intro k
  have hrhs : (1 + Polynomial.C (Fintype.card V : ℤ) * Polynomial.X).coeff k
      = if k = 0 then 1 else if k = 1 then (Fintype.card V : ℤ) else 0 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
      Polynomial.coeff_X]
    by_cases h0 : k = 0
    · subst h0
      simp
    · by_cases h1 : k = 1
      · subst h1
        simp [h0]
      · simp [h0, h1, Ne.symm h1]
  have hcount : ((⊤ : SimpleGraph V).indepSetFinset k).card
      = if k = 0 then 1 else if k = 1 then Fintype.card V else 0 := by
    by_cases h0 : k = 0
    · subst h0
      have hsing : (⊤ : SimpleGraph V).indepSetFinset 0 = {∅} := by
        ext s
        constructor
        · intro h
          rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff] at h
          obtain ⟨-, hcard⟩ := h
          rw [Finset.mem_singleton]
          exact Finset.card_eq_zero.mp hcard
        · intro h
          rw [Finset.mem_singleton] at h
          subst h
          rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff]
          exact ⟨(hindep ∅).mpr (by simp), Finset.card_empty⟩
      simp [hsing]
    · by_cases h1 : k = 1
      · subst h1
        have hpow : (⊤ : SimpleGraph V).indepSetFinset 1 = Finset.univ.powersetCard 1 := by
          ext s
          constructor
          · intro h
            rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff] at h
            obtain ⟨-, hcard⟩ := h
            rw [Finset.mem_powersetCard]
            exact ⟨Finset.subset_univ s, hcard⟩
          · intro h
            rw [Finset.mem_powersetCard] at h
            obtain ⟨-, hcard⟩ := h
            rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff]
            refine ⟨(hindep s).mpr ?_, hcard⟩
            rw [hcard]
        rw [hpow, Finset.card_powersetCard, Finset.card_univ, Nat.choose_one_right]
        simp
      · have hempty : (⊤ : SimpleGraph V).indepSetFinset k = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro s hs
          rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff] at hs
          obtain ⟨hI, hcard⟩ := hs
          have hle := (hindep s).mp hI
          omega
        rw [hempty, Finset.card_empty]
        simp [h0, h1]
  rw [independencePoly_coeff, hcount, hrhs]
  split_ifs <;> simp

end

end MetaMathlibExt

@[expose] public section

namespace SimpleGraph

/-- **Claw-free graph.** A simple graph $G$ on a vertex set $V$, not necessarily finite, is
claw-free if it has no induced claw $K_{1,3}$: there are no vertices
$c, \ell_1, \ell_2, \ell_3 \in V$ such that $\ell_1, \ell_2, \ell_3$ are pairwise distinct, each
is adjacent to $c$ and different from $c$, and no two of them are adjacent. -/
public def IsClawFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ∃ c l₁ l₂ l₃ : V, c ≠ l₁ ∧ c ≠ l₂ ∧ c ≠ l₃ ∧ l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    G.Adj c l₁ ∧ G.Adj c l₂ ∧ G.Adj c l₃ ∧ ¬ G.Adj l₁ l₂ ∧ ¬ G.Adj l₁ l₃ ∧ ¬ G.Adj l₂ l₃

/-- **Claw-free graphs have no induced claw.** Let $G$ be a simple graph on an arbitrary vertex
set. Then $G$ is claw-free if and only if the claw $K_{1,3}$, the star graph on four vertices
whose center is adjacent to the other three, is not an induced subgraph of $G$, that is, there is
no injective map from its vertices to those of $G$ that preserves both adjacency and
nonadjacency. -/
public theorem isClawFree_iff_not_isIndContained {V : Type*} (G : SimpleGraph V) :
    G.IsClawFree ↔ ¬ (starGraph (0 : Fin 4)).IsIndContained G := by
  constructor
  · intro hcf ⟨f⟩
    apply hcf
    have inj := f.injective
    have e01 : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 1 :=
      SimpleGraph.starGraph_adj.mpr ⟨by decide, Or.inl rfl⟩
    have e02 : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 2 :=
      SimpleGraph.starGraph_adj.mpr ⟨by decide, Or.inl rfl⟩
    have e03 : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 3 :=
      SimpleGraph.starGraph_adj.mpr ⟨by decide, Or.inl rfl⟩
    have n12 : ¬ (SimpleGraph.starGraph (0 : Fin 4)).Adj 1 2 := by
      rw [SimpleGraph.starGraph_adj]
      decide
    have n13 : ¬ (SimpleGraph.starGraph (0 : Fin 4)).Adj 1 3 := by
      rw [SimpleGraph.starGraph_adj]
      decide
    have n23 : ¬ (SimpleGraph.starGraph (0 : Fin 4)).Adj 2 3 := by
      rw [SimpleGraph.starGraph_adj]
      decide
    exact ⟨f 0, f 1, f 2, f 3,
      fun heq => (by decide : (0 : Fin 4) ≠ 1) (inj heq),
      fun heq => (by decide : (0 : Fin 4) ≠ 2) (inj heq),
      fun heq => (by decide : (0 : Fin 4) ≠ 3) (inj heq),
      fun heq => (by decide : (1 : Fin 4) ≠ 2) (inj heq),
      fun heq => (by decide : (1 : Fin 4) ≠ 3) (inj heq),
      fun heq => (by decide : (2 : Fin 4) ≠ 3) (inj heq),
      f.map_adj_iff.mpr e01, f.map_adj_iff.mpr e02, f.map_adj_iff.mpr e03,
      fun h => n12 (f.map_adj_iff.mp h),
      fun h => n13 (f.map_adj_iff.mp h),
      fun h => n23 (f.map_adj_iff.mp h)⟩
  · intro hnd
    unfold IsClawFree
    rintro ⟨c, l₁, l₂, l₃, hc1, hc2, hc3, h12, h13, h23,
      ha1, ha2, ha3, hn12, hn13, hn23⟩
    apply hnd
    refine ⟨⟨⟨![c, l₁, l₂, l₃], ?_⟩, ?_⟩⟩
    · intro a b hab
      fin_cases a <;> fin_cases b
      <;> first
        | rfl
        | exact (hc1 hab).elim
        | exact (Ne.symm hc1 hab).elim
        | exact (hc2 hab).elim
        | exact (Ne.symm hc2 hab).elim
        | exact (hc3 hab).elim
        | exact (Ne.symm hc3 hab).elim
        | exact (h12 hab).elim
        | exact (Ne.symm h12 hab).elim
        | exact (h13 hab).elim
        | exact (Ne.symm h13 hab).elim
        | exact (h23 hab).elim
        | exact (Ne.symm h23 hab).elim
    · intro a b
      fin_cases a <;> fin_cases b <;> simp only [SimpleGraph.starGraph_adj]
      <;> first
        | exact iff_of_true ha1 (by decide)
        | exact iff_of_true ha1.symm (by decide)
        | exact iff_of_true ha2 (by decide)
        | exact iff_of_true ha2.symm (by decide)
        | exact iff_of_true ha3 (by decide)
        | exact iff_of_true ha3.symm (by decide)
        | exact iff_of_false G.irrefl (by decide)
        | exact iff_of_false hn12 (by decide)
        | exact iff_of_false (fun h => hn12 h.symm) (by decide)
        | exact iff_of_false hn13 (by decide)
        | exact iff_of_false (fun h => hn13 h.symm) (by decide)
        | exact iff_of_false hn23 (by decide)
        | exact iff_of_false (fun h => hn23 h.symm) (by decide)

end SimpleGraph

namespace MetaMathlibExt

/-- **The two definitions of claw-free agree.** A simple graph on a finite vertex set is a
claw-free finite graph if and only if it is a claw-free graph in the sense defined for graphs on
arbitrary vertex sets. -/
public theorem clawFree_iff_isClawFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    clawFree G ↔ G.IsClawFree :=
  Iff.rfl

end MetaMathlibExt

end
