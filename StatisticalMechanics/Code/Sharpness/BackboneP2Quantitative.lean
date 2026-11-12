/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Mathlib
import Code.Sharpness.BackbonePropsFull
import Code.Ising.HdomNativeWeight

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem shb_isBackboneOf_of_select_eq_some (n : Current V) (x y : V)
    (omega : G.Path x y) (hsel : shb_backboneSelect G n x y = some omega) :
    shb_IsBackboneOf G n x y omega := by
  unfold shb_backboneSelect at hsel
  split at hsel
  · rename_i hne
    have hEq : (shb_backboneSet G n x y).min' hne = omega :=
      Option.some.inj hsel
    rw [← shb_mem_backboneSet]
    rw [← hEq]
    exact Finset.min'_mem _ _
  · contradiction



theorem shb_sources_removePath_eq_empty_of_select (n : Current V) {x y : V}
    (omega : G.Path x y) (hxy : Not (x = y)) (hsrc : sources G n = {x, y})
    (hsel : shb_backboneSelect G n x y = some omega) :
    sources G (removeWalk n omega.1) = ∅ := by
  let hbackbone : shb_IsBackboneOf G n x y omega :=
    shb_isBackboneOf_of_select_eq_some G n x y omega hsel
  let p : IsBackbonePath G n x y :=
    shb_backboneOf_imp_isBackbonePath G n x y omega hbackbone
  have hp : sources G (removeWalk n p.1) = ∅ :=
    sources_removeWalk_eq_empty G p hxy hsrc
  have hedges : p.1.edges = omega.1.edges := by
    dsimp [p, shb_backboneOf_imp_isBackbonePath]
    exact Walk.edges_transfer _ _
  have hremove : removeWalk n p.1 = removeWalk n omega.1 := by
    funext e
    simp only [removeWalk_apply, hedges]
  rwa [hremove] at hp



theorem shb_removeWalk_add_edgeSet_of_odd {H : SimpleGraph V} {n : Current V} {x y : V}
    (w : H.Walk x y) (hw : w.IsPath) (hodd : ∀ e ∈ w.edges, Odd (n e)) :
    (fun e => removeWalk n w e + (if e ∈ w.edges.toFinset then 1 else 0)) = n := by
  funext e
  by_cases he : e ∈ w.edges
  · rw [removeWalk_apply, if_pos (List.mem_toFinset.mpr he)]
    rw [hw.isTrail.count_edges_eq_one he]
    exact Nat.sub_add_cancel ((hodd e he).pos)
  · rw [removeWalk_apply, if_neg (by simpa using he)]
    rw [List.count_eq_zero_of_not_mem he]
    simp



theorem shb_removePath_add_edgeSet {n : Current V} {x y : V} (omega : G.Path x y)
    (hbackbone : shb_IsBackboneOf G n x y omega) :
    (fun e => removeWalk n omega.1 e + (if e ∈ omega.1.edges.toFinset then 1 else 0)) = n :=
  shb_removeWalk_add_edgeSet_of_odd omega.1 omega.2 hbackbone


theorem shb_weight_removeWalk_factor_of_odd (beta : Real) (J : Sym2 V -> Real)
    {H : SimpleGraph V} {n : Current V} {x y : V} (w : H.Walk x y)
    (hw : w.IsPath) (hodd : ∀ e ∈ w.edges, Odd (n e)) :
    weight G beta J n =
      weight G beta J (removeWalk n w) *
        ∏ e ∈ G.edgeFinset,
          (if e ∈ w.edges.toFinset
            then (beta * J e) / (removeWalk n w e + 1)
            else 1) := by
  calc
    weight G beta J n =
        weight G beta J
          (fun e => removeWalk n w e + (if e ∈ w.edges.toFinset then 1 else 0)) := by
      congr 1
      exact (shb_removeWalk_add_edgeSet_of_odd w hw hodd).symm
    _ = weight G beta J (removeWalk n w) *
          ∏ e ∈ G.edgeFinset,
            (if e ∈ w.edges.toFinset
              then (beta * J e) / (removeWalk n w e + 1)
              else 1) :=
      StatMech.Ising.hnw_addBackbone_weight G beta J
        (removeWalk n w) w.edges.toFinset




theorem shb_weight_removePath_factor (beta : Real) (J : Sym2 V -> Real)
    {n : Current V} {x y : V} (omega : G.Path x y)
    (hbackbone : shb_IsBackboneOf G n x y omega) :
    weight G beta J n =
      weight G beta J (removeWalk n omega.1) *
        ∏ e ∈ G.edgeFinset,
          (if e ∈ omega.1.edges.toFinset
            then (beta * J e) / (removeWalk n omega.1 e + 1)
            else 1) := by
  exact shb_weight_removeWalk_factor_of_odd G beta J omega.1 omega.2 hbackbone




theorem shb_P2_current_factor (beta : Real) (J : Sym2 V -> Real)
    {n : Current V} {x y : V} (p : IsBackbonePath G n x y) (hxy : Not (x = y))
    (hsrc : sources G n = {x, y}) :
    sources G (removeWalk n p.1) = ∅ ∧
      weight G beta J n =
        weight G beta J (removeWalk n p.1) *
          ∏ e ∈ G.edgeFinset,
            (if e ∈ p.1.edges.toFinset
              then (beta * J e) / (removeWalk n p.1 e + 1)
              else 1) := by
  exact ⟨sources_removeWalk_eq_empty G p hxy hsrc,
    shb_weight_removeWalk_factor_of_odd G beta J p.1 p.2
      (fun e he => isBackbonePath_edge_odd G p he)⟩




theorem shb_backboneNum_eq_removeWalk_sum (beta : Real) (J : Sym2 V -> Real)
    {x y : V} (omega : G.Path x y) :
    shb_backboneNum G beta J x y omega =
      ∑' m : G.edgeFinset -> Nat,
        if sources G (ofEdgeFun G m) = {x, y} ∧
            shb_backboneSelect G (ofEdgeFun G m) x y = some omega then
          weight G beta J (removeWalk (ofEdgeFun G m) omega.1) *
            ∏ e ∈ G.edgeFinset,
              (if e ∈ omega.1.edges.toFinset
                then (beta * J e) / (removeWalk (ofEdgeFun G m) omega.1 e + 1)
                else 1)
        else 0 := by
  unfold shb_backboneNum
  refine tsum_congr (fun m => ?_)
  by_cases h : sources G (ofEdgeFun G m) = {x, y} ∧
      shb_backboneSelect G (ofEdgeFun G m) x y = some omega
  · rw [if_pos h, if_pos h]
    exact shb_weight_removePath_factor G beta J omega
      (shb_isBackboneOf_of_select_eq_some G (ofEdgeFun G m) x y omega h.2)
  · rw [if_neg h, if_neg h]







theorem shb_rho_eq_removeWalk_sum_div (beta : Real) (J : Sym2 V -> Real)
    {x y : V} (omega : G.Path x y) :
    shb_rho G beta J x y omega =
      (∑' m : G.edgeFinset -> Nat,
        if sources G (ofEdgeFun G m) = {x, y} ∧
            shb_backboneSelect G (ofEdgeFun G m) x y = some omega then
          weight G beta J (removeWalk (ofEdgeFun G m) omega.1) *
            ∏ e ∈ G.edgeFinset,
              (if e ∈ omega.1.edges.toFinset
                then (beta * J e) / (removeWalk (ofEdgeFun G m) omega.1 e + 1)
                else 1)
        else 0) / currentSum G beta J ∅ := by
  unfold shb_rho
  rw [shb_backboneNum_eq_removeWalk_sum G beta J omega]

end Sharpness

end StatMech
