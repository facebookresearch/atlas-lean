/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Convenient.StdSimplexHornLocus

/-!
# Clients of the geometric horn locus

The standard zero-simplex is delta-generated. The nonempty edge horn at
vertex zero contains the actual image of the facet omitting vertex one.
-/

open Convexity

example : DeltaGeneratedSpace (StdSimplex ℝ (Fin 1)) := inferInstance

example (simplex : StdSimplex ℝ (Fin 1)) :
    (↑(hornRetractMap (0 : Fin 2) (by decide)
      (StdSimplex.map (Fin.succAbove (1 : Fin 2)) simplex)) : StdSimplex ℝ (Fin 2)) =
        StdSimplex.map (Fin.succAbove (1 : Fin 2)) simplex := by
  apply hornRetractMap_fix
  rw [hornLocus_eq_biUnion_faceRanges]
  exact Set.mem_iUnion.mpr ⟨⟨1, by decide⟩, ⟨simplex, rfl⟩⟩
