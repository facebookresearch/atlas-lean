/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Native small étale geometric DG Hom and pullback source models

The coefficient action on source module morphisms is fixed by the actual
scheme Γ map of each chart over Spec A. The DG category is the native
cochain category of those actual module sheaves; its Hom is the full
linear Hom complex in every integer degree.

Derived test pullback uses one augmented DG diagram of source cochains,
the native module inverse image on every homogeneous cochain, and a
quasi-isomorphism to the target K-injective diagram. The native total
left derived counit must be an isomorphism on the source diagram.
This fixes actual derived pullback of all test objects and all test
maps, without an unrelated tangent, complex or DG functor input.

References: Toën--Vaquié math/0503269v5 §3.5 pp59–60;
Stacks 03G8, 06YY and 0DLE. Construction and source model proofs are
separate Wanted requests; no moduli equivalence is included here.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open CochainComplex.HomComplex

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The actual scalar action comes from the chart's structural scheme map and native ΓSpec isomorphism. -/
def chartScalarMap {X : SourceSpace.{u}} (A : CommRingCat.{u})
    (π : X.sheaf ⟶ represented.obj (Spec A)) (U : EtaleChart X) :
    A →+* ((structurePresheaf X).obj (op U)) :=
  ((Scheme.Γ.map (chartStructuralMap π U).op).hom).comp (Scheme.ΓSpecIso A).inv.hom

/-- The source linearity is normalized on every source sheaf morphism and every actual chart section. -/
structure ScalarLinearitySource {X : SourceSpace.{u}} [SiteSource X]
    (A : CommRingCat.{u}) (π : X.sheaf ⟶ represented.obj (Spec A)) where
  linear : Linear (LargeScalar A) (Modules X)
  normalized : letI := linear
    ∀ (M N : Modules X) (a : M ⟶ N) (r : LargeScalar A) (U : EtaleChart X)
      (s : M.val.obj (op U)),
      ((r • a).val.app (op U)).hom s = (chartScalarMap A π U r.down) • (a.val.app (op U)).hom s

/-- The DG carrier is literally the native cochain category of source small étale modules. -/
def geometricDG {X : SourceSpace.{u}} [SiteSource X] {A : CommRingCat.{u}}
    {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π) :
    DGCat (LargeScalar A) :=
  letI := S.linear
  DGCat.of (LargeScalar A) (CochainComplex (Modules X) ℤ)

/-- A source K-injective model fixes an actual native derived object. -/
structure KInjectiveSource {X : SourceSpace.{u}} [SiteSource X] (E : Derived X) where
  complex : CochainComplex (Modules X) ℤ
  injective : complex.IsKInjective
  realization : DerivedCategory.Q.obj complex ≅ E

/-- The actual full geometric A-linear RHom cochain complex. -/
def geometricRHom {X : SourceSpace.{u}} [SiteSource X] {A : CommRingCat.{u}}
    {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π)
    {E F : Derived X} (P : KInjectiveSource E) (Q : KInjectiveSource F) :
    Cochains (LargeScalar A) :=
  dgHomComplex (LargeScalar A) (C := geometricDG S) P.complex Q.complex

/-- A native closed DG cochain gives the actual cochain morphism in the source module category. -/
def closedCochainMap {X : SourceSpace.{u}} [SiteSource X] {A : CommRingCat.{u}}
    {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π)
    {K K' : geometricDG S} (z : DGHom (LargeScalar A) 0 K K')
    (hz : z ∈ dgCycles (LargeScalar A) K K') :
    (show CochainComplex (Modules X) ℤ from K) ⟶
      (show CochainComplex (Modules X) ℤ from K') := by
  letI := S.linear
  apply Cocycle.homOf
  apply Cocycle.mk (z : Cochain K K' 0) 1 (by omega)
  have h := (mem_dgCycles (LargeScalar A)).mp hz
  change ((CochainComplex.linearHomComplex (LargeScalar A) K K').d 0 1).hom z = 0 at h
  exact (CochainComplex.linearHomComplex_d_hom_apply (LargeScalar A) K K' 0 1
    (z : Cochain K K' 0)).symm.trans h

/-- Raw DG inverse image is fixed on every source cochain object and every homogeneous cochain. -/
structure RawPullbackDGSource [SourceTheory.{u}] (P : PullbackSystem.{u})
    {X Y : SourceSpace.{u}} (f : X ⟶ Y) (A : CommRingCat.{u})
    (πY : Y.sheaf ⟶ represented.obj (Spec A)) (πX : X.sheaf ⟶ represented.obj (Spec A))
    (SY : ScalarLinearitySource A πY) (SX : ScalarLinearitySource A πX) where
  over : sheafMap f ≫ πY = πX
  functor : EnrichedFunctor (Cochains (LargeScalar A)) (geometricDG SY) (geometricDG SX)
  object_eq : ∀ K : geometricDG SY,
    functor.obj K = ((P.module f).functor.mapHomologicalComplex (.up ℤ)).obj K
  hom_eq : ∀ (K K' : geometricDG SY) (n : ℤ) (a : DGHom (LargeScalar A) n K K'),
    HEq (functor.dgMap n a) ((a : Cochain K K' n).map (P.module f).functor)

/-- One whole source DG diagram and two augmentations normalize actual derived pullback of all tests and maps. -/
structure TestPullbackDGSource [SourceTheory.{u}] {P : PullbackSystem.{u}}
    {X Y : SourceSpace.{u}} {f : X ⟶ Y} {A : CommRingCat.{u}}
    {πY : Y.sheaf ⟶ represented.obj (Spec A)} {πX : X.sheaf ⟶ represented.obj (Spec A)}
    {SY : ScalarLinearitySource A πY} {SX : ScalarLinearitySource A πX}
    (F : RawPullbackDGSource P f A πY πX SY SX)
    (D : DGCat (LargeScalar A)) (G : EnrichedFunctor (Cochains (LargeScalar A)) D (geometricDG SY)) where
  replacement : EnrichedFunctor (Cochains (LargeScalar A)) D (geometricDG SY)
  sourceAugmentation : DGNatTrans replacement G
  source_quasiIso : ∀ d : D, QuasiIso
    (closedCochainMap SY (sourceAugmentation.dgApp d) (sourceAugmentation.dgApp_mem_dgCycles d))
  source_acyclic : ∀ d : D, IsIso ((pullCounit P f).app (replacement.obj d))
  target : EnrichedFunctor (Cochains (LargeScalar A)) D (geometricDG SX)
  target_injective : ∀ d : D, (target.obj d).IsKInjective
  targetAugmentation : DGNatTrans (replacement.comp (Cochains (LargeScalar A)) F.functor) target
  target_quasiIso : ∀ d : D, QuasiIso
    (closedCochainMap SX (targetAugmentation.dgApp d) (targetAugmentation.dgApp_mem_dgCycles d))

/-- The native derived comparison is constructed from the two actual augmentations and the native counit. -/
def testDerivedPullbackComparison [SourceTheory.{u}] {P : PullbackSystem.{u}}
    {X Y : SourceSpace.{u}} {f : X ⟶ Y} {A : CommRingCat.{u}}
    {πY : Y.sheaf ⟶ represented.obj (Spec A)} {πX : X.sheaf ⟶ represented.obj (Spec A)}
    {SY : ScalarLinearitySource A πY} {SX : ScalarLinearitySource A πX}
    {F : RawPullbackDGSource P f A πY πX SY SX}
    {D : DGCat (LargeScalar A)} {G : EnrichedFunctor (Cochains (LargeScalar A)) D (geometricDG SY)}
    (T : TestPullbackDGSource F D G) (d : D) :
    (pull P f).obj (DerivedCategory.Q.obj (G.obj d)) ≅ DerivedCategory.Q.obj (T.target.obj d) := by
  let a := closedCochainMap SY (T.sourceAugmentation.dgApp d)
    (T.sourceAugmentation.dgApp_mem_dgCycles d)
  let b := closedCochainMap SX (T.targetAugmentation.dgApp d)
    (T.targetAugmentation.dgApp_mem_dgCycles d)
  letI : QuasiIso a := T.source_quasiIso d
  letI : QuasiIso b := T.target_quasiIso d
  letI : IsIso ((pullCounit P f).app (T.replacement.obj d)) := T.source_acyclic d
  exact (pull P f).mapIso (asIso (DerivedCategory.Q.map a)).symm ≪≫
    asIso ((pullCounit P f).app (T.replacement.obj d)) ≪≫
    (eqToIso (congrArg (fun K : CochainComplex (Modules X) ℤ => DerivedCategory.Q.obj K)
      (F.object_eq (T.replacement.obj d)))).symm ≪≫
    asIso (DerivedCategory.Q.map b)

end MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
