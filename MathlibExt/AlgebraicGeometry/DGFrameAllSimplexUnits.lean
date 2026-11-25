/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits

/-!
# Original common-degeneracy induction units in every moduli simplex

Every vertex of every simplex restricts the SAME actual enriched
induction unit along the original unique degeneracy [n] to [0].
The source is the full original simplexBimodule and its entire
projective enveloping-module replacement. All T-action, coefficient,
face, degeneracy and homogeneous module data remain present before
the ordinary fundamental-groupoid construction.

Source: Toën--Vaquié arXiv:math/0503269v5, Sections 3.1 and 3.5.
Native source and license notices remain in the imported modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DGFrameAllSimplexUnits

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {T : DGCat k}
    (F : DGFrame k (oppositeCategory T)) {N : ShuffleAlgebraFunctor k}
    (A : SAlg k) (n : SimplexCategory)

/-- The actual i-th original cosimplicial vertex map. -/
def simplexEndpoint (i : Fin (n.len + 1)) : F.diagram.obj ⦋0⦌ ⟶ F.diagram.obj n :=
  F.diagram.map (SimplexCategory.const ⦋0⦌ n i)

/-- The same original degeneracy retracts every vertex of the whole simplex. -/
def simplexRetraction : F.diagram.obj n ⟶ F.diagram.obj ⦋0⦌ :=
  F.diagram.map (SimplexCategory.const n ⦋0⦌ 0)

/-- Every original endpoint has exactly the same native retraction. -/
theorem simplexEndpoint_retraction (i : Fin (n.len + 1)) :
    simplexEndpoint F n i ≫ simplexRetraction F n = 𝟙 (F.diagram.obj ⦋0⦌) := by
  have h : SimplexCategory.const ⦋0⦌ n i ≫ SimplexCategory.const n ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    simp only [SimplexCategory.const_comp, SimplexCategory.const_apply, SimplexCategory.const_eq_id]
  rw [simplexEndpoint, simplexRetraction, ← Functor.map_comp, h]
  exact F.diagram.map_id _

/-- All envelope functors retain the literal source maps and the actual coefficient identity. -/
structure SimplexEnvelopeRetraction where
  endpoint : ∀ i : Fin (n.len + 1),
    TensorMapModel (A := oppositeCategory (F.diagram.obj ⦋0⦌))
      (B := oppositeCategory (F.diagram.obj n))
      (C := coefficientCategory N A) (D := coefficientCategory N A)
      (EnrichedFunctor.op (V := Cochains k) (simplexEndpoint F n i)) (𝟙 (coefficientCategory N A))
  retraction : TensorMapModel (A := oppositeCategory (F.diagram.obj n))
    (B := oppositeCategory (F.diagram.obj ⦋0⦌))
    (C := coefficientCategory N A) (D := coefficientCategory N A)
    (EnrichedFunctor.op (V := Cochains k) (simplexRetraction F n)) (𝟙 (coefficientCategory N A))
  commutes : ∀ i, (endpoint i).functor ≫ retraction.functor =
    𝟙 (enveloping (F.diagram.obj ⦋0⦌) (coefficientCategory N A))

variable (B : SimplexEnvelopeRetraction F (N := N) A n)
    (R : RestrictionModel B.retraction.functor) (E : ExtensionModel B.retraction.functor R)
    (S : ∀ i, RestrictionModel (B.endpoint i).functor)
    (I : ∀ i, RestrictionCompositeIdentity (B.endpoint i).functor B.retraction.functor
      (B.commutes i) (S i) R)
    (M : DGDerivedModules k (enveloping (F.diagram.obj n) (coefficientCategory N A)))

/-- The common target is the original actual induction of the entire simplex module. -/
def simplexInduction : RightModule k (enveloping (F.diagram.obj ⦋0⦌) (coefficientCategory N A)) :=
  (E.functor.obj M).obj

/-- All vertex maps restrict the same full enriched induction unit, followed by the original restriction identity. -/
def simplexInductionUnit (i : Fin (n.len + 1)) :
    (S i).functor.obj M.obj ⟶ simplexInduction F A n B R E M := by
  let a := (S i).functor.dgMap 0 (E.unit M)
  have ha : dgDifferential k 0 a = 0 := by
    rw [← (S i).functor.dgMap_dgDifferential, E.unit_closed, map_zero]
  exact (DGFunctor.homEquivDGCycles k _ _).symm ⟨a, (mem_dgCycles k).mpr ha⟩ ≫
    ((I i).iso (E.functor.obj M).obj).hom

end MathlibExt.AlgebraicGeometry.DGFrameAllSimplexUnits
