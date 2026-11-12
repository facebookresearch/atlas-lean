/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Ising.Gibbs

open scoped BigOperators
open Finset

namespace StatMech.Walls

open StatMech.Ising





variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]




noncomputable def kwdCutEdges (s : ConfigSpace V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => bond s e = -1)

omit [Fintype V] [DecidableEq V] in



theorem kwd_bond_eq_one_or_neg_one (s : ConfigSpace V) (e : Sym2 V) :
    bond s e = 1 ∨ bond s e = -1 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]



omit [DecidableEq V] in








theorem kwd_sum_bond_eq_card_sub_two_cut (s : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond s e)
      = (G.edgeFinset.card : ℝ) - 2 * (kwdCutEdges G s).card := by
  unfold kwdCutEdges
  rw [← Finset.sum_filter_add_sum_filter_not G.edgeFinset (fun e => bond s e = -1)]
  
  have h1 : ∑ e ∈ G.edgeFinset.filter (fun e => bond s e = -1), bond s e
      = - (G.edgeFinset.filter (fun e => bond s e = -1)).card := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2)]; simp
  
  have h2 : ∑ e ∈ G.edgeFinset.filter (fun e => ¬ bond s e = -1), bond s e
      = (G.edgeFinset.filter (fun e => ¬ bond s e = -1)).card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_]; · simp
    intro e he
    rcases kwd_bond_eq_one_or_neg_one s e with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp he).2
  rw [h1, h2]
  have hcard : (G.edgeFinset.filter (fun e => bond s e = -1)).card
      + (G.edgeFinset.filter (fun e => ¬ bond s e = -1)).card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  push_cast [← hcard]
  ring












theorem kwd_isingZ_low_temp_expansion (β : ℝ) :
    isingZ G β 0
      = Real.exp (β * G.edgeFinset.card)
        * ∑ s : ConfigSpace V, Real.exp (-2 * β) ^ (kwdCutEdges G s).card := by
  unfold isingZ isingWeight hamiltonian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [zero_mul, sub_zero]
  rw [kwd_sum_bond_eq_card_sub_two_cut G s, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring







omit [DecidableEq V] in




theorem kwd_isingWeight_eq_contour_weight (β : ℝ) (s : ConfigSpace V) :
    isingWeight G β 0 s
      = Real.exp (β * G.edgeFinset.card) * Real.exp (-2 * β) ^ (kwdCutEdges G s).card := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [kwd_sum_bond_eq_card_sub_two_cut G s, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring

omit [Fintype V] [DecidableEq V] in

theorem kwd_bond_flip (s : ConfigSpace V) (e : Sym2 V) :
    bond (fun v => ! s v) e = bond s e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk, bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

omit [DecidableEq V] in




theorem kwd_cutEdges_flip (s : ConfigSpace V) :
    kwdCutEdges G (fun v => ! s v) = kwdCutEdges G s := by
  unfold kwdCutEdges
  apply Finset.filter_congr
  intro e _
  rw [kwd_bond_flip]

end StatMech.Walls
