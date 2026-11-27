/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.FiveColorTheorem
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Regression tests for the five-color theorem -/

namespace MetaMathlibExt

open SimpleGraph

example {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.IsPlanar) :
    Nonempty (G.Coloring (Fin 5)) :=
  five_color_theorem G hG

-- The empty vertex type uses the empty disjunct of straight-line planarity.
example (G : SimpleGraph PEmpty) : Nonempty (G.Coloring (Fin 5)) :=
  five_color_theorem G (Or.inl fun h ↦ h.elim PEmpty.elim)

private def oneEdge : SimpleGraph (Fin 3) := fromEdgeSet {s(0, 1)}

-- One genuine edge and one isolated vertex: no connectedness premise is needed.
example : oneEdge.Adj 0 1 ∧ ¬ oneEdge.Connected ∧ Nonempty (oneEdge.Coloring (Fin 5)) := by
  refine ⟨(fromEdgeSet_adj _).mpr ⟨rfl, by decide⟩, ?_, ?_⟩
  · intro h
    apply not_reachable_of_neighborSet_left_eq_empty (G := oneEdge)
      (u := 2) (v := 0) (by decide) _ (h.preconnected 2 0)
    ext w
    fin_cases w <;> simp [neighborSet, oneEdge, fromEdgeSet_adj]
  · apply five_color_theorem
    let f : Fin 3 → ℝ × ℝ := fun i ↦ ((i.val : ℝ), 0)
    have hf : Function.Injective f := by
      intro i j h
      have hx : (i.val : ℝ) = (j.val : ℝ) := congrArg Prod.fst h
      exact Fin.ext (by exact_mod_cast hx)
    refine Or.inr ⟨f, hf, ?_, ?_⟩
    · intro a b h
      exact hf.ne h.ne
    · intro a b c d ha hc hne
      exfalso
      apply hne
      have he := ((fromEdgeSet_adj _).mp ha).1.trans ((fromEdgeSet_adj _).mp hc).1.symm
      rcases (Sym2.eq_iff.mp he) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Set.pair_comm _ _

private def k4Point (i : Fin 4) : ℝ × ℝ := ![(0, 0), (3, 0), (0, 3), (1, 1)] i

-- The triangle with one interior vertex is a straight-line drawing of K₄.
private theorem k4_planar : (⊤ : SimpleGraph (Fin 4)).IsPlanar := by
  have hinj : Function.Injective k4Point := by
    intro a b he
    fin_cases a <;> fin_cases b <;> norm_num [k4Point] at he
    all_goals rfl
  refine Or.inr ⟨k4Point, hinj, ?_, ?_⟩
  · intro a b h
    exact hinj.ne h.ne
  · intro a b c d ha hc hne p hp
    change a ≠ b at ha
    change c ≠ d at hc
    obtain ⟨⟨u, hu₀, hu₁, hux, huy⟩, ⟨w, hw₀, hw₁, hwx, hwy⟩⟩ := hp
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases a <;> fin_cases b <;> norm_num at ha <;>
      fin_cases c <;> fin_cases d <;> norm_num at hc
    all_goals try exact (hne rfl).elim
    all_goals try exact (hne (Set.pair_comm _ _)).elim
    all_goals norm_num [k4Point] at hux huy hwx hwy ⊢
    all_goals
      first
      | exfalso; linarith
      | constructor <;>
          first | (left; apply Prod.ext <;> linarith) | (right; apply Prod.ext <;> linarith)

-- A nonvacuous example: this planar graph has no three-coloring.
example : Nonempty ((⊤ : SimpleGraph (Fin 4)).Coloring (Fin 5)) ∧
    ¬ Nonempty ((⊤ : SimpleGraph (Fin 4)).Coloring (Fin 3)) := by
  refine ⟨five_color_theorem _ k4_planar, ?_⟩
  rintro ⟨C⟩
  have hinj : Function.Injective C := fun a b he ↦ by
    by_contra hn
    exact C.valid (show (⊤ : SimpleGraph (Fin 4)).Adj a b from hn) he
  have h := Fintype.card_le_of_injective C hinj
  norm_num at h

end MetaMathlibExt
