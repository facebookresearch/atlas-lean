/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic
/-!
# CoxeterGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 18
-/

@[expose] public section

-- Combinatorics 18: Coxeter graph
def fin4ToZMod7 : Fin 4 → ZMod 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3


def coxeterGraph : SimpleGraph (Fin 4 × ZMod 7) :=
  SimpleGraph.fromRel fun a b =>
    (a.1 = b.1 ∧ a.1 ≠ 0 ∧ a.2 - b.2 = fin4ToZMod7 a.1)
    ∨
    (a.1 = 0 ∧ b.1 ≠ 0 ∧ a.2 = b.2)

instance : DecidableRel coxeterGraph.Adj := fun a b => by
  unfold coxeterGraph
  infer_instance


instance : coxeterGraph.LocallyFinite := fun v =>
  Subtype.fintype (fun w => coxeterGraph.Adj v w)

-- Sanity check: the Coxeter graph is cubic (3-regular).

example : coxeterGraph.IsRegularOfDegree 3 := by
  change ∀ v : Fin 4 × ZMod 7, coxeterGraph.degree v = 3
  decide

end
