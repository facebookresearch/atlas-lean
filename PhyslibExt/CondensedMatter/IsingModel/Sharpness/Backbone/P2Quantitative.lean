/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BackboneDecomposition
public import PhyslibExt.CondensedMatter.IsingModel.HdomNativeWeight

/-!
# Removing a selected backbone from a current

Quantitative facts behind the backbone chain rule: removing a selected backbone path from a
current with sources `{x, y}` leaves a sourceless current, and the current weight factors as the
weight of the remaining current times an explicit product over the edges of the path.

## i. Overview

If the support-ordered selector returns a path `ω` for a current `n`, then `ω` is a backbone of
`n` (`shb_isBackboneOf_of_select_eq_some`) and removing it leaves a sourceless current
(`shb_sources_removePath_eq_empty_of_select`). Along a path with odd multiplicities, adding back one
unit per edge recovers `n`, so `w(n) = w(n − ω) ∏_{e ∈ ω} βJ_e / (n_e − 1 + 1)`
(`shb_weight_removeWalk_factor_of_odd`, `shb_P2_current_factor`). Summing over currents gives
expressions of the backbone numerator and of `shb_rho` as sums over the remaining currents.

Headline fidelity: `shb_P2_current_factor`, `shb_backboneNum_eq_removeWalk_sum` and
`shb_rho_eq_removeWalk_sum_div` are unconditional. They rewrite the backbone weight but do not
prove the backbone chain rule (P2), which needs a resummation over the remaining currents.

## ii. Key results

- `shb_sources_removePath_eq_empty_of_select` : removing the selected backbone leaves no sources
- `shb_P2_current_factor` : the current weight factors along a backbone path
- `shb_rho_eq_removeWalk_sum_div` : `shb_rho` as a sum over remaining currents

## iii. Table of contents

- A. Removing a selected backbone
- B. Weight factorization along a backbone
- C. The backbone numerator and `ρ` as sums over remaining currents

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982)
  1–48
- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Removing a selected backbone -/

/-- A path returned by the backbone selector is a backbone of the current. -/
lemma shb_isBackboneOf_of_select_eq_some (n : Current V) (x y : V)
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

/-- Removing the selected backbone from a current with sources `{x, y}` leaves no sources. -/
lemma shb_sources_removePath_eq_empty_of_select (n : Current V) {x y : V}
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

/-! ## B. Weight factorization along a backbone -/

omit [Fintype V] in
/-- Along a path with odd multiplicities, removing the path and adding back one unit per edge
recovers the current. -/
lemma shb_removeWalk_add_edgeSet_of_odd {H : SimpleGraph V} {n : Current V} {x y : V}
    (w : H.Walk x y) (hw : w.IsPath) (hodd : ∀ e ∈ w.edges, Odd (n e)) :
    (fun e => removeWalk n w e + (if e ∈ w.edges.toFinset then 1 else 0)) = n := by
  funext e
  by_cases he : e ∈ w.edges
  · rw [removeWalk_apply, ite_eq_left (List.mem_toFinset.mpr he)]
    rw [hw.isTrail.count_edges_eq_one he]
    exact Nat.sub_add_cancel ((hodd e he).pos)
  · rw [removeWalk_apply, ite_eq_right (by simpa using he)]
    rw [List.count_eq_zero_of_not_mem he]
    simp

omit [Fintype V] [DecidableRel G.Adj] in
lemma shb_removePath_add_edgeSet {n : Current V} {x y : V} (omega : G.Path x y)
    (hbackbone : shb_IsBackboneOf G n x y omega) :
    (fun e => removeWalk n omega.1 e + (if e ∈ omega.1.edges.toFinset then 1 else 0)) = n :=
  shb_removeWalk_add_edgeSet_of_odd omega.1 omega.2 hbackbone

/-- Along a path with odd multiplicities, the weight factors as the weight of the remaining current
times a product over the edges of the path. -/
lemma shb_weight_removeWalk_factor_of_odd (beta : Real) (J : Sym2 V -> Real)
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

/-- The weight factorization along a backbone path. -/
lemma shb_weight_removePath_factor (beta : Real) (J : Sym2 V -> Real)
    {n : Current V} {x y : V} (omega : G.Path x y)
    (hbackbone : shb_IsBackboneOf G n x y omega) :
    weight G beta J n =
      weight G beta J (removeWalk n omega.1) *
        ∏ e ∈ G.edgeFinset,
          (if e ∈ omega.1.edges.toFinset
            then (beta * J e) / (removeWalk n omega.1 e + 1)
            else 1) := by
  exact shb_weight_removeWalk_factor_of_odd G beta J omega.1 omega.2 hbackbone

/-- For a backbone path of a current with sources `{x, y}`, the remaining current is sourceless and
the weight factors along the path. -/
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

/-! ## C. The backbone numerator and `ρ` as sums over remaining currents -/

/-- The backbone numerator as a sum over currents selecting `ω` of the factorized weights. -/
lemma shb_backboneNum_eq_removeWalk_sum (beta : Real) (J : Sym2 V -> Real)
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
  · rw [ite_eq_left h, ite_eq_left h]
    exact shb_weight_removePath_factor G beta J omega
      (shb_isBackboneOf_of_select_eq_some G (ofEdgeFun G m) x y omega h.2)
  · rw [ite_eq_right h, ite_eq_right h]

/-- `shb_rho` as the factorized sum divided by the sourceless partition function. -/
lemma shb_rho_eq_removeWalk_sum_div (beta : Real) (J : Sym2 V -> Real)
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
