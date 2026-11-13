/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.SortingNetworks
import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-- Boundary check: the one-comparator network on two elements
sorts every Boolean input (by decide), so by the 0-1 principle
it sorts every natural input. -/
example (x : Fin 2 → ℕ) : SortedArr (Network.exec [(0, 1)] x) :=
  zero_one_principle [(0, 1)] (fun x a b hab => by
    fin_cases a <;> fin_cases b <;>
      simp_all [Network.exec, comparator] <;> cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all) x
