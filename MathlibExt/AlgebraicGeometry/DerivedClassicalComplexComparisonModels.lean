/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
public import MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange

/-!
# The source-normalized classical comparison on universally glueable complexes

A frame interval is an actual closed degree-zero arrow between the two
images of the chosen frame object. Its augmentation is the identity of
the source scalar category. Each moduli edge acts on this literal arrow;
the native perfect realization gives its actual module map. The ordinary
and small étale realizations retain that same arrow on every degree.

The comparison constructor is constrained on every vertex and every edge.
Its target is the actual perfect/no-negative-fibre-Ext small étale groupoid.
Equivalence of this constructed functor is a separate proof request.
The scalar maps on the glueable subcomplex are literal restrictions of
the native moduliFunctor maps, not independent ordinary stack arrows.

References: Toën--Vaquié, math/0503269v5 §3.1 pp36--37 and p8;
Stacks 0DLD/0DLE, in the affine identity situation. General T-actions
remain in vertexBimodule; only the source scalar category is compared
to the plain classical complexes fibre here.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
  _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k]

attribute [local instance] HasDerivedCategory.standard

/-- The two source objects are the literal cosimplicial endpoint maps. -/
def frameEndpoint {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (i : Fin 2) : R.diagram.obj ⦋1⦌ :=
  (R.diagram.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).obj r.point

/-- The source interval arrow is normalized by its augmentation to the actual scalar unit. -/
structure ScalarFrameInterval {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) where
  arrow : DGHom k 0 (frameEndpoint r 0) (frameEndpoint r 1)
  closed : dgDifferential k 0 arrow = 0
  augmentation : HEq ((R.augmentation.app ⦋1⦌).dgMap 0 arrow)
    (dgId k (C := oppositeCategory (scalarCategory k)) (op PUnit.unit))

/-- The literal image of that interval in the actual coefficient-perfect module category. -/
def frameEdgeModuleImage {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S)
    (A : CommAlgCat.{u} k) (e : ((underivedModuliFunctor R P).obj A) _⦋1⦌) :=
  ((P.realization (ordinaryAlgebras.obj A)).comp (Cochains k)
    (perfectToRaw (coefficientCategory N (ordinaryAlgebras.obj A)))).dgMap 0
      (e.dgMap 0 I.arrow)

/-- Transport only the actual endpoint equalities of an edge, retaining its source arrow. -/
structure ScalarFrameEdgeMaps {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} (I : ScalarFrameInterval r) (P : StrictPerfectSystem N S)
    (A : CommAlgCat.{u} k) where
  map : ∀ {x y : ((underivedModuliFunctor R P).obj A) _⦋0⦌}, SSet.Edge x y →
    DGHom k 0 (vertexModule r P A x) (vertexModule r P A y)
  closed : ∀ {x y : ((underivedModuliFunctor R P).obj A) _⦋0⦌} (e : SSet.Edge x y),
    dgDifferential k 0 (map e) = 0
  normalized : ∀ {x y : ((underivedModuliFunctor R P).obj A) _⦋0⦌} (e : SSet.Edge x y),
    HEq (map e) (frameEdgeModuleImage I P A e.edge)

/-- The actual closed module natural transformation carried by a moduli edge. -/
def nativeEdgeModuleMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    {A : CommAlgCat.{u} k} (F : ScalarFrameEdgeMaps I P A)
    {x y : ((underivedModuliFunctor R P).obj A) _⦋0⦌} (e : SSet.Edge x y) :
    vertexModule r P A x ⟶ vertexModule r P A y :=
  closedModuleMap (F.map e) (F.closed e)

/-- The source small étale edge arrow is that same ordinary cochain map, followed by Q. -/
def nativeEdgeEtaleMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    {A : CommAlgCat.{u} k} (F : ScalarFrameEdgeMaps I P A)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (J : AffineEtaleModuleSource O (ordinaryRing A))
    {x y : ((underivedModuliFunctor R P).obj A) _⦋0⦌} (e : SSet.Edge x y) :
    vertexEtaleDerived r P A V J x ⟶ vertexEtaleDerived r P A V J y :=
  DerivedCategory.Q.map ((J.functor.mapHomologicalComplex (.up ℤ)).map
    (V.functor.map (nativeEdgeModuleMap F e)))

/-- The comparison constructor fixes every vertex and every generating groupoid arrow. -/
structure ClassicalComplexComparison {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    {A : CommAlgCat.{u} k} (F : ScalarFrameEdgeMaps I P A)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) where
  functor : universallyGlueableGroupoid r P A V L J ⥤ ComplexesFibre L J
  vertex_eq : ∀ x : (universallyGlueableSpace r P A V L J) _⦋0⦌,
    (functor.obj (SSet.FundamentalGroupoid.mk x)).of.obj =
      vertexEtaleDerived r P A V J x.val
  edge_eq : ∀ {x y : (universallyGlueableSpace r P A V L J) _⦋0⦌} (e : SSet.Edge x y),
    HEq ((functor.map (SSet.FundamentalGroupoid.homMk e)).iso.hom.hom)
      (nativeEdgeEtaleMap F V J
        (e.map (((underivedModuliFunctor R P).obj A).fullEnhancedSubcategory
          (IsUniversallyGlueableVertex r P A V L J)).ι))

/-- A coherent family of prescribed ordinary coefficient and sheaf realizations. -/
structure OrdinaryComplexSourceSystem {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S)
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O) where
  coefficient : ∀ A : CommAlgCat.{u} k, OrdinaryCoefficientSource N A
  module : ∀ A : CommAlgCat.{u} k, OrdinaryModuleSource (coefficient A)
  etale : ∀ A : CommAlgCat.{u} k, AffineEtaleModuleSource O (ordinaryRing A)
  preserves : ∀ {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌),
    IsUniversallyGlueableVertex r P A (module A) L (etale A) E →
      IsUniversallyGlueableVertex r P B (module B) L (etale B)
        (((underivedModuliFunctor R P).map f).app (op ⦋0⦌) E)

/-- Scalar change is the actual native moduli map restricted to the glueable full subcomplex. -/
def glueableScalarMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {P : StrictPerfectSystem N S}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    (Z : OrdinaryComplexSourceSystem r P O L) {A B : CommAlgCat.{u} k} (f : A ⟶ B) :
    universallyGlueableSpace r P A (Z.module A) L (Z.etale A) ⟶
      universallyGlueableSpace r P B (Z.module B) L (Z.etale B) :=
  SSet.Subcomplex.lift
    ((((underivedModuliFunctor R P).obj A).fullEnhancedSubcategory
      (IsUniversallyGlueableVertex r P A (Z.module A) L (Z.etale A))).ι ≫
        (underivedModuliFunctor R P).map f) (by
    rw [SSet.range_le_fullEnhancedSubcategory_iff]
    intro x
    exact Z.preserves f x.val
      ((SSet.mem_fullEnhancedSubcategory_obj_zero_iff _ x.val).mp x.property))

/-- The groupoid map is induced by that literal scalar map. -/
def glueableScalarGroupoidMap {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {P : StrictPerfectSystem N S}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    (Z : OrdinaryComplexSourceSystem r P O L) {A B : CommAlgCat.{u} k} (f : A ⟶ B) :
    universallyGlueableGroupoid r P A (Z.module A) L (Z.etale A) ⥤
      universallyGlueableGroupoid r P B (Z.module B) L (Z.etale B) :=
  SSet.mapFundamentalGroupoid (glueableScalarMap Z f)

/-- The literal scalar maps inherit unit and composition from the native moduli functor. -/
def glueableModuliFunctor {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {P : StrictPerfectSystem N S}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    (Z : OrdinaryComplexSourceSystem r P O L) : CommAlgCat.{u} k ⥤ SSet.{u + 1} where
  obj A := universallyGlueableSpace r P A (Z.module A) L (Z.etale A)
  map f := glueableScalarMap Z f
  map_id A := by
    ext n x
    apply Subtype.ext
    exact congrArg (fun a => (a.app n) x.val)
      ((underivedModuliFunctor R P).map_id A)
  map_comp f g := by
    ext n x
    apply Subtype.ext
    exact congrArg (fun a => (a.app n) x.val)
      ((underivedModuliFunctor R P).map_comp f g)

end MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
