/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Convenient.DeltaGeneratedProduct

/-!
# Delta-generated product clients

Instance search covers the product of the two- and three-dimensional Euclidean
models. The general product theorem requires local compactness of the left
factor; the negative probe is about applying that theorem, not about whether
other products are Delta-generated.
-/

open Topology

example : IsGeneratedBy (fun n : ℕ => Fin n → ℝ)
    ((Fin 2 → ℝ) × (Fin 3 → ℝ)) := inferInstance

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DeltaGeneratedSpace X] [DeltaGeneratedSpace Y] :
    LocallyCompactSpace X → DeltaGeneratedSpace (X × Y) := by
  fail_if_success
    have : DeltaGeneratedSpace (X × Y) :=
      DeltaGeneratedSpace.prod_of_locallyCompact_left (X := X) (Y := Y)
  intro hX
  let : LocallyCompactSpace X := hX
  exact DeltaGeneratedSpace.prod_of_locallyCompact_left (X := X) (Y := Y)
