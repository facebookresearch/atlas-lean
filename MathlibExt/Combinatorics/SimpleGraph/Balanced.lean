/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

/-!
# Balanced graphs

A shared predicate for `D`-balanced (`D`-almost-regular) graphs.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- A graph is `D`-balanced if its maximum degree is at most `D` times its
minimum degree. -/
def IsBalanced (G : SimpleGraph V) (D : ℝ) [DecidableRel G.Adj] : Prop :=
  G.maxDegree ≤ D * G.minDegree

end SimpleGraph
