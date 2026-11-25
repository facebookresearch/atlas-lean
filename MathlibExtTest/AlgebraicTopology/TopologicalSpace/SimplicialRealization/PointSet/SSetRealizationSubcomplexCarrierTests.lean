/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationSubcomplexCarrier

/-!
# Subcomplex-carrier coherence regression for the vertex-zero subcomplex of `Δ[1]`

Concrete client of `SSet.Subcomplex.sigmaToTop_mapCarrier`: ambient `sigmaToTop`
of the mapped carrier equals the realized inclusion applied to subcomplex `sigmaToTop`.
Locks public orientation, same-dimension coercions, and map-composition direction.
-/

@[expose] public section

set_option autoImplicit false

open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SubcomplexCarrierTests

/-- Vertex-zero `0`-simplex of `Δ[1]`. -/
def v0 : (Δ[1] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)

/-- Vertex-zero subcomplex of `Δ[1]`. -/
def A0 : (Δ[1] : SSet.{0}).Subcomplex :=
  SSet.Subcomplex.ofSimplex v0

/-- Nondegenerate carrier of the vertex-zero subcomplex. -/
def s0 : (A0 : SSet.{0}).N :=
  SSet.N.mk (X := (A0 : SSet.{0})) ⟨v0, SSet.Subcomplex.mem_ofSimplex_obj v0⟩ (by
    rw [SSet.nonDegenerate_zero]
    exact Set.mem_univ _)

/-- Unique positive point of the topological `0`-simplex. -/
noncomputable def pt0 : Convexity.StdSimplex ℝ (Fin (0 + 1)) :=
  Convexity.StdSimplex.single (0 : Fin (0 + 1))

/-- Carrier coherence for the vertex-zero subcomplex of `Δ[1]`. -/
theorem subcomplexCarrier_coherence_vertexZero_Δ1 :
    SSet.sigmaToTop (Δ[1] : SSet.{0}) ⟨SSet.Subcomplex.mapCarrier A0 s0, pt0⟩ =
      SSet.toTop.map A0.ι (SSet.sigmaToTop (A0 : SSet.{0}) ⟨s0, pt0⟩) :=
  SSet.Subcomplex.sigmaToTop_mapCarrier A0 s0 pt0

#print axioms subcomplexCarrier_coherence_vertexZero_Δ1

end MathlibExtTest.AlgebraicTopology.ModelCategory.SubcomplexCarrierTests
