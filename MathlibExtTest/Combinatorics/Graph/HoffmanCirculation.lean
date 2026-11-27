/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.HoffmanCirculation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Graph.HoffmanCirculation

open MathlibExt.Combinatorics.Graph.ArcNetwork

-- One arc false → true: positive flow is negative demand at false, positive at true.
private def src (_ : Unit) := false
private def dst (_ : Unit) := true
private def demand (v : Bool) : ℝ := if v then 2 else -2

example : IsBoundedFlow src dst (fun _ => 1) (fun _ => 2) demand (fun _ => 2) := by
  refine ⟨fun _ => by norm_num, fun _ => le_rfl, funext fun v => ?_⟩
  cases v <;> norm_num [incidence_mulVec, Finset.sum_filter, src, dst, demand]

-- The opposite net inflow cannot be supplied: {false} has no entering capacity.
example : ¬ ∃ f, IsBoundedFlow src dst (fun _ => 1) (fun _ => 2) (-demand) f := by
  rintro ⟨f, hf⟩
  have h := hf.cut_le {false}
  norm_num [demand, enteringArcs, leavingArcs, Finset.sum_filter, src, dst] at h

-- A positive lower bound on the only entering arc prevents a circulation.
example : ¬ ∃ f, IsBoundedFlow src dst (fun _ => 1) (fun _ => 2) 0 f := by
  rw [hoffman_circulation_iff src dst _ _ (fun _ => by norm_num)]
  intro h
  have hh := h {true}
  norm_num [enteringArcs, leavingArcs, Finset.sum_filter, src, dst] at hh

-- Two parallel arcs, an antiparallel arc, and a zero-capacity loop.
private def t : Fin 4 → Fin 2 := ![0, 0, 1, 1]
private def h : Fin 4 → Fin 2 := ![1, 1, 0, 1]
private def lo : Fin 4 → ℤ := ![-2, -1, 0, 0]
private def hi : Fin 4 → ℤ := ![-1, 1, 1, 0]
private def b : Fin 2 → ℤ := ![1, -1]
private noncomputable def halves : Fin 4 → ℝ := ![-3/2, 1/2, 0, 0]

example : enteringArcs t h {1} = {0, 1} ∧ leavingArcs t h {1} = {2} := by decide

private theorem fractional_flow : IsBoundedFlow t h (fun e => (lo e : ℝ))
    (fun e => (hi e : ℝ)) (fun v => (b v : ℝ)) halves := by
  refine ⟨fun e => ?_, fun e => ?_, funext fun v => ?_⟩
  · fin_cases e <;> norm_num [lo, halves]
  · fin_cases e <;> norm_num [hi, halves]
  · fin_cases v <;>
      norm_num [Matrix.mulVec, dotProduct, incidenceMatrix, Fin.sum_univ_four, halves, t, h, b]

-- The integer witness need not (and here cannot) be the supplied real flow.
example : (¬ ∃ z : ℤ, (z : ℝ) = halves 1) ∧
    ∃ g : Fin 4 → ℤ, IsBoundedFlow t h (fun e => (lo e : ℝ)) (fun e => (hi e : ℝ))
      (fun v => (b v : ℝ)) (fun e => (g e : ℝ)) := by
  refine ⟨?_, exists_int_boundedFlow t h lo hi b ⟨halves, fractional_flow⟩⟩
  rintro ⟨z, hz⟩
  have h0 : (0 : ℝ) < z := by rw [hz]; norm_num [halves]
  have h1 : (z : ℝ) < 1 := by rw [hz]; norm_num [halves]
  have : (0 : ℤ) < z := by exact_mod_cast h0
  have : z < 1 := by exact_mod_cast h1
  omega

-- An isolated vertex and a forced negative flow on a loop. No arc enters or
-- leaves any vertex set, irrespective of the sign of the loop's bounds.
example : ∃ g : Unit → ℤ, IsBoundedFlow src src (fun _ => ((-3 : ℤ) : ℝ))
    (fun _ => ((-3 : ℤ) : ℝ)) 0 (fun e => (g e : ℝ)) := by
  apply exists_int_circulation src src (fun _ => -3) (fun _ => -3)
  apply (hoffman_circulation_iff _ _ _ _ le_rfl).2
  intro X
  simp [enteringArcs, leavingArcs]

-- No vertices or arcs are required for the existence direction.
example : ∃ f, IsBoundedFlow (id : Fin 0 → Fin 0) id 0 0 0 f := by
  apply (exists_boundedFlow_iff _ _ _ _ _ le_rfl (by simp)).2
  simp

end MathlibExtTest.Combinatorics.Graph.HoffmanCirculation
