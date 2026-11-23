/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import Mathlib.Topology.UniformSpace.OfCompactT2

/-!
# Topological entropy on compact R1 spaces

A compact R1 space carries a canonical uniformity `uniformSpaceOfCompactR1` inducing its
topology. The topological entropy of a self-map is the Bowen-Dinaburg cover entropy of
`Set.univ` for this uniformity. Every uniform structure inducing the topology has uniformity
equal to the neighbourhood filter of the diagonal, so the value does not depend on the choice.
-/

@[expose] public section

namespace Dynamics

variable {X : Type*}

/-- Topological entropy of a self-map of a compact R1 space, as the cover entropy of
  `Set.univ` for the canonical uniformity `uniformSpaceOfCompactR1`. -/
noncomputable def topologicalEntropy [TopologicalSpace X] [CompactSpace X] [R1Space X]
    (T : X → X) : EReal :=
  @Dynamics.coverEntropy X uniformSpaceOfCompactR1 T Set.univ

/-- Cover entropy on `Set.univ` agrees with `topologicalEntropy` for any uniform structure
  inducing the topology. -/
theorem coverEntropy_eq_topologicalEntropy [t : TopologicalSpace X] [CompactSpace X]
    [R1Space X] (u : UniformSpace X) (hu : u.toTopologicalSpace = t) (T : X → X) :
    @Dynamics.coverEntropy X u T Set.univ = topologicalEntropy T := by
  subst hu
  have h1 : @uniformity X u = nhdsSet (Set.diagonal X) :=
    (nhdsSet_diagonal_eq_uniformity).symm
  have h2 : nhdsSet (Set.diagonal X) = @uniformity X uniformSpaceOfCompactR1 :=
    @nhdsSet_diagonal_eq_uniformity X uniformSpaceOfCompactR1 _
  have hU : u = (uniformSpaceOfCompactR1 : UniformSpace X) :=
    UniformSpace.ext (h1.trans h2)
  exact congrArg (fun w : UniformSpace X => @Dynamics.coverEntropy X w T Set.univ) hU

end Dynamics
