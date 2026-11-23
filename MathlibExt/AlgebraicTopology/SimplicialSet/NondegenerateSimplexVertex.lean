/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Vertices of nondegenerate simplices

This file provides the canonical low-level evaluation of a nondegenerate
simplicial simplex at one ordered vertex position.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Opposite
open scoped Simplicial

universe u

namespace SSet

/-- The vertex of a simplicial set occurring at position `i` of a
nondegenerate simplex. -/
noncomputable def simplexVertex (K : SSet.{u}) (s : K.N) :
    Fin (s.dim + 1) → K _⦋0⦌ := fun i =>
  (SSet.yonedaEquiv.symm s.simplex).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm i)

end SSet

end
