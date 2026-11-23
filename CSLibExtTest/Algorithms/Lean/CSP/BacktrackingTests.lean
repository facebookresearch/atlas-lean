/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.Backtracking
public import Mathlib.Data.Fin.VecNotation

/-!
# Backtracking with forward checking tests

Kernel-checked fixtures (`decide`) on graph colouring, with the least-variable order
(`SearchOrder.ofLinearOrder`) and minimum remaining values (`SearchOrder.mrv`):

* the triangle with three colours returns the colouring `0, 1, 2`;
* `K₄` with three colours returns `none`, hence has no 3-colouring (`backtrackFC_eq_none_iff`);
* the triangle with two colours returns `none` although it is arc consistent;
* an empty domain returns `none`; a problem without variables returns the empty assignment;
* a self-loop arc acts as a unary constraint; a constraint on one orientation only is respected;
* MRV picks a variable with a singleton domain before the least variable, so it is a different
  order (nonvacuity), and still returns a solution.

Closed checks instantiate soundness and completeness for an arbitrary search order.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CSPBacktracking

open Cslib.Algorithms.Lean.ArcConsistency

/-- Graph colouring: both orientations of every edge, adjacent variables differ. -/
def colouring {n : ℕ} (edges : List (Fin n × Fin n)) (k : ℕ) : BinaryCSP (Fin n) (Fin k) :=
  ⟨edges.flatMap fun e => [e, (e.2, e.1)], fun _ _ a b => a ≠ b⟩

/-- The triangle. -/
def triangle : List (Fin 3 × Fin 3) := [(0, 1), (1, 2), (0, 2)]

/-- The complete graph `K₄`. -/
def k4 : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-! ## Positive check: the triangle is 3-colourable -/

example : backtrackFC (colouring triangle 3) SearchOrder.ofLinearOrder (fun _ => Finset.univ) =
    some ![0, 1, 2] := by decide

example : backtrackFC (colouring triangle 3) SearchOrder.mrv (fun _ => Finset.univ) =
    some ![0, 1, 2] := by decide

example : IsSolution (colouring triangle 3) (fun _ => Finset.univ) ![0, 1, 2] :=
  backtrackFC_sound _ SearchOrder.ofLinearOrder (by decide)

/-! ## Negative check: `K₄` is not 3-colourable -/

example : backtrackFC (colouring k4 3) SearchOrder.ofLinearOrder (fun _ => Finset.univ) = none := by
  decide

example : backtrackFC (colouring k4 3) SearchOrder.mrv (fun _ => Finset.univ) = none := by
  decide

/-- `K₄` has no 3-colouring, read off the search's `none`. -/
example (σ : Fin 4 → Fin 3) : ¬IsSolution (colouring k4 3) (fun _ => Finset.univ) σ :=
  (backtrackFC_eq_none_iff _ SearchOrder.ofLinearOrder _).1 (by decide) σ

/-- `K₄` with four colours is colourable. -/
example : (backtrackFC (colouring k4 4) SearchOrder.ofLinearOrder (fun _ => Finset.univ)).isSome :=
  by decide

/-! ## Boundary checks -/

/-- The triangle with two colours: arc consistent, yet no solution. -/
example : backtrackFC (colouring triangle 2) SearchOrder.ofLinearOrder (fun _ => Finset.univ) =
    none := by decide

/-- An empty domain: no solution. -/
example : backtrackFC (colouring triangle 3) SearchOrder.ofLinearOrder
    (fun v => if v = 1 then ∅ else Finset.univ) = none := by decide

/-- No variables: the empty assignment. -/
example : (backtrackFC (⟨[], fun _ _ _ _ => true⟩ : BinaryCSP (Fin 0) (Fin 2))
    SearchOrder.ofLinearOrder (fun _ => Finset.univ)).isSome := by decide

/-- A self-loop `x ≠ x` is unsatisfiable; a self-loop `x = x` is satisfiable. -/
example : backtrackFC (⟨[(0, 0)], fun _ _ a b => a ≠ b⟩ : BinaryCSP (Fin 1) (Fin 2))
    SearchOrder.ofLinearOrder (fun _ => Finset.univ) = none := by decide

example : backtrackFC (⟨[(0, 0)], fun _ _ a b => a = b⟩ : BinaryCSP (Fin 1) (Fin 2))
    SearchOrder.ofLinearOrder (fun _ => Finset.univ) = some ![0] := by decide

/-- `x < y` given on one orientation only. -/
example : backtrackFC (⟨[(0, 1)], fun _ _ a b => a < b⟩ : BinaryCSP (Fin 2) (Fin 3))
    SearchOrder.ofLinearOrder (fun _ => Finset.univ) = some ![0, 1] := by decide

example : backtrackFC (⟨[(0, 1)], fun _ _ a b => a < b⟩ : BinaryCSP (Fin 2) (Fin 3))
    SearchOrder.ofLinearOrder (fun v => if v = 1 then {0} else Finset.univ) = none := by decide

/-- Forward checking leaves a variable with no arc to the assigned variable unchanged. -/
example : forwardCheck (⟨[(0, 1)], fun _ _ a b => a < b⟩ : BinaryCSP (Fin 3) (Fin 3))
    (fun _ => Finset.univ) 0 0 2 = Finset.univ := by decide

example : incidentArcs (⟨[(0, 1)], fun _ _ a b => a < b⟩ : BinaryCSP (Fin 3) (Fin 3)) 0 2 = [] := by
  decide

/-! ## Nonvacuity: MRV is a different order -/

/-- Triangle domains where variable `2` has a single value. -/
def forcedDom : Fin 3 → Finset (Fin 3) := fun v => if v = 2 then {0} else Finset.univ

example : (SearchOrder.ofLinearOrder : SearchOrder (Fin 3) (Fin 3)).pick forcedDom Finset.univ
    Finset.univ_nonempty = 0 := by decide

example : (SearchOrder.mrv : SearchOrder (Fin 3) (Fin 3)).pick forcedDom Finset.univ
    Finset.univ_nonempty = 2 := by decide

example : backtrackFC (colouring triangle 3) SearchOrder.mrv forcedDom = some ![1, 2, 0] := by
  decide

example : backtrackFC (colouring triangle 3) SearchOrder.ofLinearOrder forcedDom =
    some ![1, 2, 0] := by decide

/-! ## Closed checks: every search order -/

example (O : SearchOrder (Fin 3) (Fin 3)) :
    (backtrackFC (colouring triangle 3) O (fun _ => Finset.univ)).isSome :=
  backtrackFC_complete _ O (σ := ![0, 1, 2]) ⟨fun _ => Finset.mem_univ _, by decide⟩

example (O : SearchOrder (Fin 4) (Fin 3)) :
    backtrackFC (colouring k4 3) O (fun _ => Finset.univ) = none :=
  (backtrackFC_eq_none_iff _ O _).2 fun σ =>
    (backtrackFC_eq_none_iff _ SearchOrder.ofLinearOrder _).1 (by decide) σ

example {X D : Type*} [DecidableEq X] [Fintype X] (P : BinaryCSP X D) (O : SearchOrder X D)
    (dom : X → Finset D) (σ : X → D) (h : backtrackFC P O dom = some σ) : IsSolution P dom σ :=
  backtrackFC_sound P O h

#print axioms backtrackFC_sound
#print axioms backtrackFC_complete
#print axioms backtrackFC_isSome_iff
#print axioms backtrackFC_eq_none_iff
#print axioms SearchOrder.mrv_pick_card_le

end Cslib.Algorithms.Lean.CSPBacktracking
