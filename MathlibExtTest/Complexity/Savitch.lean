/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Savitch
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-- Boundary check: on a two-point configuration space with one
edge, reachability in at most `2 ^ 0 = 1` step holds along the
edge, and the Savitch predicate accepts. -/
example : reachIn (fun x y : Fin 2 => x = 0 ∧ y = 1) 0 0 1 = true := by
  decide

/-- Soundness form at `k = 0`: acceptance gives a path of length
at most one. -/
example (h : reachIn (fun x y : Fin 2 => x = 0 ∧ y = 1) 0 0 1 = true) :
    ∃ n ≤ 2 ^ 0, GPath (fun x y : Fin 2 => x = 0 ∧ y = 1) 0 1 n :=
  reachIn_sound 0 0 1 h
