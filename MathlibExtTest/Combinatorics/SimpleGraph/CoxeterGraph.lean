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

public import MathlibExt.Combinatorics.SimpleGraph.CoxeterGraph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.CoxeterGraph

open MetaMathlibExt

-- Combinatorics 18: Coxeter graph

instance : DecidableRel coxeterGraph.Adj := fun a b => by
  unfold coxeterGraph
  infer_instance

instance : coxeterGraph.LocallyFinite := fun v =>
  Subtype.fintype (fun w => coxeterGraph.Adj v w)

-- Sanity check: the Coxeter graph is cubic (3-regular).

example : coxeterGraph.IsRegularOfDegree 3 := by
  change ∀ v : Fin 4 × ZMod 7, coxeterGraph.degree v = 3
  decide

end MathlibExtTest.Combinatorics.SimpleGraph.CoxeterGraph

end
