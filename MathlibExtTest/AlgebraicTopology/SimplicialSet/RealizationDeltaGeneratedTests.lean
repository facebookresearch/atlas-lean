/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationDeltaGenerated

/-!
# Legacy generatedness tests for geometric realization

The neutral presentation is tested separately. This owner pins only the
legacy generated-topology instance, including the singular circle and the
two-simplex with collapsed boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationDeltaGeneratedTests

noncomputable def collapseBoundary :
    (SSet.boundary 2 : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary 2 : SSet.{u})

noncomputable def collapsedBoundaryTwoSphere : SSet.{u} :=
  pushout (SSet.boundary 2).ι collapseBoundary

example (T : SSet.{u}) : DeltaGeneratedSpace (SSet.toTop.obj T) :=
  inferInstance

example (T : SSet.{1}) : DeltaGeneratedSpace (SSet.toTop.obj T) :=
  inferInstance

example (T : SSet.{0}) : DeltaGeneratedSpace (SSet.toTop.obj T) :=
  inferInstance

#synth DeltaGeneratedSpace (SSet.toTop.obj SSet.S1)
#synth DeltaGeneratedSpace (SSet.toTop.obj collapsedBoundaryTwoSphere.{u})
#synth DeltaGeneratedSpace (SSet.toTop.obj collapsedBoundaryTwoSphere.{1})
#synth DeltaGeneratedSpace (SSet.toTop.obj collapsedBoundaryTwoSphere.{0})

#check SSet.instDeltaGeneratedSpaceCarrierObjTopCatToTop_mathlibExt

#guard_msgs (error, substring := true) in
#synth CompactSpace (SSet.toTop.obj SSet.S1)

#guard_msgs (error, substring := true) in
#synth T1Space (SSet.toTop.obj SSet.S1)

#print axioms SSet.instDeltaGeneratedSpaceCarrierObjTopCatToTop_mathlibExt

end RealizationDeltaGeneratedTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
