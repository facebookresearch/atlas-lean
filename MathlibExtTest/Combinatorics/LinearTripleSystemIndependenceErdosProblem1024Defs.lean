/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Defs

namespace MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted

/-- The empty family is a linear triple system. -/
example : IsLinearTripleSystem (∅ : Finset (Finset (Fin 3))) := by
  unfold IsLinearTripleSystem
  decide

/-- The Fano plane is a linear triple system on seven points. -/
example : IsLinearTripleSystem ({{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6},
    {2, 3, 6}, {2, 4, 5}} : Finset (Finset (Fin 7))) := by
  unfold IsLinearTripleSystem
  decide

/-- Two triples sharing two points do not form a linear triple system. -/
example : ¬ IsLinearTripleSystem ({{0, 1, 2}, {0, 1, 3}} : Finset (Finset (Fin 4))) := by
  unfold IsLinearTripleSystem
  decide

/-- A member with two elements is not a triple. -/
example : ¬ IsLinearTripleSystem ({{0, 1}} : Finset (Finset (Fin 3))) := by
  unfold IsLinearTripleSystem
  decide

end MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
