/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt

/-- **Five color theorem.** Every straight-line planar simple graph $G$ on a finite vertex set
has a proper vertex coloring with five colors.

Source: https://en.wikipedia.org/wiki/Five_color_theorem (statement five-color-s1). -/
theorem_wanted five_color_theorem {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsPlanar) :
    Nonempty (G.Coloring (Fin 5))

end MetaMathlibExt
