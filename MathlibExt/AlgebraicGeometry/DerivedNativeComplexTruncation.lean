/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# Literal derived-to-classical source comparison maps

The groupoid projection is the native homotopy-category/nerve unit,
followed by the actual free-groupoid comparison to FundamentalGroupoid.
The ordinary source comparison is this projection followed by the nerve
of the already vertex/edge-normalized native complexes functor.

For derived coefficients A, first use the literal algebra augmentation
A to const pi0(A) on every native DG mapping simplex. Its domain is the
full subcomplex whose augmented vertices satisfy the actual universally
glueable source condition. It then maps to the same native ordinary
X_(pi0 A) complexes fibre. No weak equivalence to this ordinary target
is claimed for arbitrary derived coefficients.

References: Toën--Vaquié math/0503269v5 §§2.3 and3.1; Stacks 0DLD/0DLE.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedNativeComplexTruncation

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
open MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k]

/-- The actual homotopy category maps to its native free fundamental groupoid. -/
def homotopyToFundamental (X : SSet.{u + 1}) : X.HomotopyCategory ⥤ SSet.FundamentalGroupoid X :=
  FreeGroupoid.of X.HomotopyCategory ⋙
    (SSet.Truncated.FundamentalGroupoid.equivalenceFreeGroupoid ((SSet.truncation 2).obj X)).inverse

/-- The native unit and free-groupoid map give the literal groupoid truncation projection. -/
def groupoidTruncation (X : SSet.{u + 1}) : X ⟶ nerve (SSet.FundamentalGroupoid X) :=
  CategoryTheory.nerveAdjunction.unit.app X ≫ nerveMap (homotopyToFundamental X)

/-- The actual ordinary comparison map to the source-native complexes groupoid nerve. -/
def nativeOrdinaryComplexComparison {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    {A : CommAlgCat.{u} k} {F : ScalarFrameEdgeMaps I P A}
    {C : OrdinaryCoefficientSource N A} {V : OrdinaryModuleSource C}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    {J : AffineEtaleModuleSource O (ordinaryRing A)} (G : ClassicalComplexComparison F V L J)
    (H : IdentityComplexesTransportSource L A J) :
    universallyGlueableSpace r P A V L J ⟶ nerve (NativeComplexesFibre L A J) :=
  groupoidTruncation (universallyGlueableSpace r P A V L J) ≫
    nerveMap (nativeIdentityModuliComparison G H)

/-- The derived locus tests the actual augmented ordinary vertex, not a new independent complex. -/
def derivedGlueableSpace {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : SAlg k)
    {C : OrdinaryCoefficientSource N (piZero A)} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing (piZero A))) : SSet.{u + 1} :=
  (((moduliFunctor R P).obj A).fullEnhancedSubcategory
    (fun E => IsUniversallyGlueableVertex r P (piZero A) V L J
      ((truncationMap R P A).app (op ⦋0⦌) E))).toSSet

/-- Every derived simplex maps by the original native pi-zero scalar augmentation. -/
def augmentedGlueableMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : SAlg k)
    {C : OrdinaryCoefficientSource N (piZero A)} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing (piZero A))) :
    derivedGlueableSpace r P A V L J ⟶ universallyGlueableSpace r P (piZero A) V L J :=
  SSet.Subcomplex.lift
    ((((moduliFunctor R P).obj A).fullEnhancedSubcategory
      (fun E => IsUniversallyGlueableVertex r P (piZero A) V L J
        ((truncationMap R P A).app (op ⦋0⦌) E))).ι ≫ truncationMap R P A) (by
    rw [SSet.range_le_fullEnhancedSubcategory_iff]
    intro E
    exact (SSet.mem_fullEnhancedSubcategory_obj_zero_iff _ E.val).mp E.property)

/-- Literal derived-to-ordinary source map: pi-zero scalar augmentation, groupoid unit, normalized source comparison. -/
def nativeDerivedComplexTruncation {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    (A : SAlg k) {F : ScalarFrameEdgeMaps I P (piZero A)}
    {C : OrdinaryCoefficientSource N (piZero A)} {V : OrdinaryModuleSource C}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    {J : AffineEtaleModuleSource O (ordinaryRing (piZero A))}
    (G : ClassicalComplexComparison F V L J) (H : IdentityComplexesTransportSource L (piZero A) J) :
    derivedGlueableSpace r P A V L J ⟶ nerve (NativeComplexesFibre L (piZero A) J) :=
  augmentedGlueableMap r P A V L J ≫ nativeOrdinaryComplexComparison G H

end MathlibExt.AlgebraicGeometry.DerivedNativeComplexTruncation
