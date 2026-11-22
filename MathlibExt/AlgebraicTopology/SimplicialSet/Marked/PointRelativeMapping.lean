/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFibrancy
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Original marked mapping spaces over the point

The actual maximal mapping complex into the original marked point is
terminal. Its fixed-base pullback first projection is therefore the
original absolute mapping-complex isomorphism. The original intrinsic
Cartesian or cocartesian point targets give Kan absolute mapping spaces,
retaining the same whole prism and source restriction.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- Original maximal marked mapping into the point is terminal by its genuine tensor adjunction. -/
def maximalMappingToPointIsTerminal (X : Marked.{u}) :
    IsTerminal (mappingComplex .maximal X (max (Δ[0] : SSet.{u}))) := by
  let G : Marked.{u} ⥤ SSet.{u} := maxMappingFunctor X
  let _ : PreservesLimitsOfSize.{0, 0} G := (maxTensorAdjunction X).rightAdjoint_preservesLimits
  let _ : PreservesLimit (Functor.empty Marked.{u}) G :=
    (inferInstance : PreservesLimitsOfShape (Discrete PEmpty) G).preservesLimit
  exact (parameterZeroIsTerminal .maximal).isTerminalObj G (max (Δ[0] : SSet.{u}))

/-- The actual fixed-base mapping first projection over the original point is an isomorphism on whole prisms. -/
def relativeMappingPointFstIso {X Y : Marked.{u}}
    (r : X ⟶ max (Δ[0] : SSet.{u})) (p : Y ⟶ max (Δ[0] : SSet.{u})) :
    relativeMappingComplex .maximal r p ≅ mappingComplex .maximal X Y := by
  let a := mappingComplexPost .maximal X p
  let b := mappingBasePoint .maximal r
  let hB : IsIso b := isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ (maximalMappingToPointIsTerminal X) b
  let f : relativeMappingComplex .maximal r p ⟶ mappingComplex .maximal X Y := pullback.fst a b
  let hF : IsIso f := (IsPullback.of_hasPullback a b).isIso_fst_of_isIso (inst := hB)
  exact @asIso _ _ _ _ f hF

/-- The native point first projections conjugate exactly the original whole source restriction. -/
def overPointMappingRestrictionIso {X X' Y : Over (max (Δ[0] : SSet.{u}))} (f : X ⟶ X') :
    Arrow.mk ((overMappingFunctor .maximal (max (Δ[0] : SSet.{u})) Y).map f.op) ≅
      Arrow.mk (mappingComplexPre .maximal f.left Y.left) :=
  Arrow.isoMk (relativeMappingPointFstIso X'.hom Y.hom) (relativeMappingPointFstIso X.hom Y.hom)
    (relativeMappingPre_fst .maximal f.left X'.hom X.hom Y.hom (Over.w f)).symm

/-- Every original marked source has Kan absolute mapping space into an actual intrinsic Cartesian point target. -/
theorem maximalMapping_cartesianPoint_kan (X : Marked.{u}) (Y : CartesianOver (Δ[0] : SSet.{u})) :
    KanComplex (mappingComplex .maximal X Y.obj.left) := by
  let r : X ⟶ max (Δ[0] : SSet.{u}) := (parameterZeroIsTerminal .maximal).from X
  let _ : KanComplex (relativeMappingComplex .maximal r Y.obj.hom) :=
    overMappingFunctor_cartesian_kan (Over.mk r) Y
  let e := relativeMappingPointFstIso r Y.obj.hom
  let _ : Fibration e.inv := (modelCategoryQuillen.fibration_iff _).mpr (modelCategoryQuillen.J.rlp_of_isIso _)
  exact isFibrant_of_fibration e.inv

/-- The same whole absolute mapping complex is Kan for every original cocartesian point target. -/
theorem maximalMapping_cocartesianPoint_kan (X : Marked.{u}) (Y : CocartesianOver (Δ[0] : SSet.{u})) :
    KanComplex (mappingComplex .maximal X Y.obj.left) := by
  let r : X ⟶ max (Δ[0] : SSet.{u}) := (parameterZeroIsTerminal .maximal).from X
  let _ : KanComplex (relativeMappingComplex .maximal r Y.obj.hom) :=
    overMappingFunctor_cocartesian_kan (Over.mk r) Y
  let e := relativeMappingPointFstIso r Y.obj.hom
  let _ : Fibration e.inv := (modelCategoryQuillen.fibration_iff _).mpr (modelCategoryQuillen.J.rlp_of_isIso _)
  exact isFibrant_of_fibration e.inv

end SSet.Marked
