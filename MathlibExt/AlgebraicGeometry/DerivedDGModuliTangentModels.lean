/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedDGModuli
public import MathlibExt.AlgebraicGeometry.DerivedCotangentModels

/-!
# Independent tangent objects of actual DG moduli points

The moduli point is the literal augmented image of a resolution-Hom
vertex at the constant ground algebra. Its cotangent representation
uses the actual simplicial square-zero deformation fibres, normalized
kernel modules and naturality in those coefficient modules.

The tangent candidate is the actual coefficient-linear dual of that
representing module, computed against the native coefficient-unit
representable. Its construction contains no endomorphism or shifted
RHom identification. The separate comparison target uses the actual
projectively cofibrant enveloping module of the same moduli vertex.

Reference: Toën--Vaquié, arXiv:math/0503269v5, Main Theorem0.2
and Corollary3.17; HAG II, Part 2, §2.2.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedDGModuliTangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The literal constant simplicial ground algebra. -/
def baseAlgebra (k : Type u) [CommRing k] : SAlg k :=
  ordinaryAlgebras.obj (CommAlgCat.of k k)

/-- A DG moduli vertex determines its actual point in the augmented derived stack. -/
def moduliPoint {T : DGCat k} {R : DGFrame k (oppositeCategory T)}
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {P : StrictPerfectSystem N S} {Q : AlgebraReplacementFunctor k}
    (M : ModuliStackModel R P Q)
    (E : ((moduliFunctor R P).obj (baseAlgebra k)) _⦋0⦌) :
    (Δ[0] : SSet.{u + 1}) ⟶ M.stack.functor.obj (baseAlgebra k) :=
  SSet.const ((M.augmentation.app (baseAlgebra k)).app (op ⦋0⦌) E)

/-- The actual coefficient-unit right module is the native Yoneda representable. -/
def coefficientUnit (N : ShuffleAlgebraFunctor k) (A : SAlg k) :
    RightModule k (coefficientCategory N A) :=
  (dgYoneda k (C := coefficientCategory N A)).obj PUnit.unit

/-- The tangent candidate is the derived dual of the actual deformation-representing module. -/
def tangentComplex {N : ShuffleAlgebraFunctor k}
    {X : DerivedPrestack.{u, u + 1} k} {A : SAlg k}
    {x : (Δ[0] : SSet.{u + 1}) ⟶ X.functor.obj A}
    {P : KanPathModel (X.functor.obj A)} (L : CotangentRepresentation N X A x P) :
    Cochains k :=
  dgHomComplex k L.module.obj (coefficientUnit N A)

/-- Actual coefficient cochain quasi-isomorphisms, with every degree retained. -/
def cochainWeakEquivalences (k : Type u) [CommRing k] : MorphismProperty (Cochains k) :=
  fun _ _ f => QuasiIso f

/-- The native cochain localization supplies the derived k-module comparison carrier. -/
abbrev cochainQ (k : Type u) [CommRing k] := (cochainWeakEquivalences k).Q

end MathlibExt.AlgebraicGeometry.DerivedDGModuliTangentModels
