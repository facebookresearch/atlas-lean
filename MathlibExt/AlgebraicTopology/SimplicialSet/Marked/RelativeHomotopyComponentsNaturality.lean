/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeHomotopyComponents

/-!
# Full original map naturality of the relative component comparison

Original source restriction and target postcomposition commute with the
native zero units and relative currying. The representative formulas give
naturality of the genuine homotopy-class/component equivalence on every
whole original marked map and all its original base equations.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- Original source restriction reads the same entire maximal relative mapping vertex. -/
theorem relativeMappingVertexEquiv_pre {Z : Marked.{u}} {X X' Y : Over Z}
    (f : X' ⟶ X) (g : X ⟶ Y) :
    relativeMappingVertexEquiv Z X' Y (f ≫ g) =
      (((overMappingFunctor .maximal Z Y).map f.op).app (op ⦋0⦌))
        (relativeMappingVertexEquiv Z X Y g) := by
  let GX := overParameterFunctor Z X
  let GX' := overParameterFunctor Z X'
  let U := relativePointProductIso Z X
  let U' := relativePointProductIso Z X'
  let τ := overParameterMap f
  let E : (GX.obj (Δ[0] : SSet.{u}) ⟶ Y) ≃ (Δ[0] ⟶ relativeMappingComplex .maximal X.hom Y.hom) :=
    overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y
  let E' : (GX'.obj (Δ[0] : SSet.{u}) ⟶ Y) ≃ (Δ[0] ⟶ relativeMappingComplex .maximal X'.hom Y.hom) :=
    overParameterHomEquiv Z X' (Δ[0] : SSet.{u}) Y
  have hU : τ.app (Δ[0] : SSet.{u}) ≫ U.hom = U'.hom ≫ f :=
    (overScalarTensorZeroNatIso Z).hom.naturality f
  have hG : U'.hom ≫ (f ≫ g) = τ.app (Δ[0] : SSet.{u}) ≫ (U.hom ≫ g) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ g) hU.symm).trans (Category.assoc _ _ _))
  let M := (overMappingFunctor .maximal Z Y).map f.op
  have hE : E' (U'.hom ≫ (f ≫ g)) = E (U.hom ≫ g) ≫ M :=
    (congrArg E' hG).trans (overParameterHomEquiv_source f (Δ[0] : SSet.{u}) Y (U.hom ≫ g))
  exact (congrArg yonedaEquiv hE).trans (yonedaEquiv_comp _ M)

/-- The actual original target postcomposition retains the entire native relative mapping vertex. -/
theorem relativeMappingVertexEquiv_post {Z : Marked.{u}} {X Y Y' : Over Z}
    (f : X ⟶ Y) (g : Y ⟶ Y') :
    relativeMappingVertexEquiv Z X Y' (f ≫ g) =
      (((overTargetMappingFunctor .maximal Z X).map g).app (op ⦋0⦌))
        (relativeMappingVertexEquiv Z X Y f) := by
  let GX := overParameterFunctor Z X
  let U := relativePointProductIso Z X
  let E : (GX.obj (Δ[0] : SSet.{u}) ⟶ Y') ≃ (Δ[0] ⟶ relativeMappingComplex .maximal X.hom Y'.hom) :=
    overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y'
  let M := (overTargetMappingFunctor .maximal Z X).map g
  have hE : E (U.hom ≫ (f ≫ g)) =
      overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y (U.hom ≫ f) ≫ M :=
    (congrArg E (Category.assoc U.hom f g).symm).trans
      (overParameterHomEquiv_post Z X (Δ[0] : SSet.{u}) (U.hom ≫ f) g)
  exact (congrArg yonedaEquiv hE).trans (yonedaEquiv_comp _ M)

/-- The genuine homotopy-class/component equivalence is natural under every original marked source map. -/
theorem relativeHomotopyClassEquivPi0_pre {Z : Marked.{u}} {X X' Y : Over Z}
    (f : X' ⟶ X) (c : (relativeIntervalCylinder Z).HomotopyClass X Y) :
    relativeHomotopyClassEquivPi0 Z X' Y ((relativeIntervalCylinder Z).homotopyClassPrecomp f Y c) =
      SSet.mapπ₀ ((overMappingFunctor .maximal Z Y).map f.op) (relativeHomotopyClassEquivPi0 Z X Y c) := by
  obtain ⟨g, rfl⟩ := (relativeIntervalCylinder Z).homotopyQuotientFunctor.map_surjective c
  rw [Precylinder.homotopyClassPrecomp_map, relativeHomotopyClassEquivPi0_map,
    relativeHomotopyClassEquivPi0_map]
  let M : relativeMappingComplex .maximal X.hom Y.hom ⟶ relativeMappingComplex .maximal X'.hom Y.hom :=
    (overMappingFunctor .maximal Z Y).map f.op
  exact (congrArg SSet.π₀.mk (relativeMappingVertexEquiv_pre f g)).trans
    (SSet.mapπ₀_mk M (relativeMappingVertexEquiv Z X Y g)).symm

end SSet.Marked
