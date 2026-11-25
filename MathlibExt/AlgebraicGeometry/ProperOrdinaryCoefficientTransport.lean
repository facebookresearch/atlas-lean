/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperOrdinaryGlueableRealization
public import MathlibExt.AlgebraicGeometry.SpaceCoefficientPullbackCoherence

/-!
# Full native coefficient transport of ordinary geometric module realization

The coefficient map is the original tensor of the frame identity and
N(const f). Its scalar extension is the full native enriched module
adjunction. A comparison of ENTIRE module diagrams normalizes the map
between both geometric roofs. Actual geometric inverse image is the
existing TestPullbackDGSource on that whole roof, with its two source
augmentations and original total-left-derived counit.

Thus no independent geometric pullback comparison is accepted. The
computed comparison retains every module object, homogeneous map,
coefficient action and original native source X_f. Unit/composition
coherence is supplied by the same source chart-unit/counit data.

Source: Toën--Vaquié arXiv:math/0503269v5 Sections 3.1/3.5;
Stacks 03G8/06YY/0DLD/0DLE. Native source notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperOrdinaryCoefficientTransport

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
open MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ProperOrdinaryModuleRealization
open MathlibExt.AlgebraicGeometry.ProperOrdinaryGlueableRealization
open MathlibExt.AlgebraicGeometry.SpaceCoefficientPullbackCoherence
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]
attribute [local instance] HasDerivedCategory.standard

/-- Lift the actual full DG functor, preserving every homogeneous source map and coefficient. -/
def liftSmallDGMap (L : CochainLiftModel k) {C C' : DGCat k} (F : C ⟶ C') :
    liftedDGCategory L C ⟶ liftedDGCategory L C' := by
  letI := L.monoidal
  letI := smallLiftEnrichment (k := k) C
  letI := smallLiftEnrichment (k := k) C'
  let G : EnrichedFunctor (Cochains k) (ULift.{u + 1} C) (ULift.{u + 1} C') :=
    { obj x := ULift.up (F.obj x.down)
      map x y := F.map x.down y.down
      map_id x := F.map_id x.down
      map_comp x y z := F.map_comp x.down y.down z.down }
  exact transportFunctor (C := ULift.{u + 1} C) (D := ULift.{u + 1} C')
    (V := Cochains k) (W := Cochains (LargeScalar k)) (largeCochainLift k) G

/-- The source is the original geometric cochain of the full QCoh object; all Hom components are unchanged. -/
def qcohToGeometric (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ B : CommRingCat.{u}, AffineEtaleModuleSource O B)
    (C : ChartRestrictionSystem O) {X : SourceSpace.{u}} {A : CommRingCat.{u}}
    {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π) :
    qcohDGCategory O L J C S ⟶ geometricDG S :=
  qcohIntoGeometric O L J C S

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (C : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)
    (SB : ScalarLinearitySource B.ring (affineProperProjection D B)) (UL : CochainLiftModel B.ring)
    (T : SmallPerfectTestModel O L J C SB UL) (F : DGFrame B.ring (oppositeCategory T.category))
    {N : ShuffleAlgebraFunctor B.ring} {S : AffineScalarSystem N}
    (Q : PullbackSystem.{u}) (FB : NativeFramePerfectTests O L J C D B SB UL T F)
    {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A')
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (G' : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A')
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (R' : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A' G')

/-- Transport is fixed on the full native module/scalar and geometric/counit diagrams. -/
structure OrdinaryCoefficientTransport where
  coefficient : TensorMapModel (A := oppositeCategory (F.diagram.obj (SimplexCategory.mk 0)))
    (B := oppositeCategory (F.diagram.obj (SimplexCategory.mk 0)))
    (C := coefficientCategory N (ordinaryAlgebras.obj A))
    (D := coefficientCategory N (ordinaryAlgebras.obj A'))
    (𝟙 (oppositeCategory (F.diagram.obj (SimplexCategory.mk 0))))
    (coefficientMap N (ordinaryAlgebras.map f))
  restriction : RestrictionModel (liftSmallDGMap UL coefficient.functor)
  extension : ExtensionModel (liftSmallDGMap UL coefficient.functor) restriction
  target : R.roof.source.category ⟶ R'.roof.source.category
  moduleComparison : DGNatTrans
    ((R.roof.modules.comp (Cochains (LargeScalar B.ring)) extension.functor).comp
      (Cochains (LargeScalar B.ring))
      (cofibrantModulesToRaw (A := B.ring) (largeOrdinaryEnvelope UL F N A')))
    ((target.comp (Cochains (LargeScalar B.ring)) R'.roof.modules).comp
      (Cochains (LargeScalar B.ring))
      (cofibrantModulesToRaw (A := B.ring) (largeOrdinaryEnvelope UL F N A')))
  moduleWeak : ∀ (e : R.roof.source.category) (x : (largeOrdinaryEnvelope UL F N A')ᵒᵖ),
    QuasiIso (moduleComponent ((DGFunctor.homEquivDGCycles (LargeScalar B.ring) _ _).symm
      ⟨moduleComparison.dgApp e, moduleComparison.dgApp_mem_dgCycles e⟩) x)
  geometric : RawPullbackDGSource Q (coefficientGeometricArrow D B f) B.ring
    (baseCoefficientProjection D B A) (baseCoefficientProjection D B A') G.scalar G'.scalar
  pullback : TestPullbackDGSource geometric R.roof.source.category
    (R.roof.geometric.comp (Cochains (LargeScalar B.ring)) (qcohToGeometric O L J C G.scalar))
  target_normalized : pullback.target =
    (target.comp (Cochains (LargeScalar B.ring)) R'.roof.geometric).comp
      (Cochains (LargeScalar B.ring)) (qcohToGeometric O L J C G'.scalar)

/-- The geometric coefficient comparison is computed from the TWO actual augmentations and native pullCounit. -/
def coefficientGeometricComparison
    (H : OrdinaryCoefficientTransport O L J C D B SB UL T F Q FB f G G' R R')
    (e : R.roof.source.category) :
    (pull Q (coefficientGeometricArrow D B f)).obj (DerivedCategory.Q.obj (R.roof.geometric.obj e).obj) ≅
      DerivedCategory.Q.obj (R'.roof.geometric.obj (H.target.obj e)).obj :=
  testDerivedPullbackComparison H.pullback e ≪≫
    eqToIso (congrArg DerivedCategory.Q.obj (congrArg (fun T => T.obj e) H.target_normalized))

/-- Coefficient transport keeps ALL source simplices; only the original moduli coefficient map is restricted. -/
def glueableCoefficientMap {PP : StrictPerfectSystem N S}
    (M : ModuliSimplexModuleSources F PP A) (M' : ModuliSimplexModuleSources F PP A')
    (preserves : ∀ e : ((underivedModuliFunctor F PP).obj A) _⦋0⦌,
      IsGlueableVertex O L J C D B SB UL T F PP Q FB A G R M e →
      IsGlueableVertex O L J C D B SB UL T F PP Q FB A' G' R' M'
        (((underivedModuliFunctor F PP).map f).app (op (SimplexCategory.mk 0)) e)) :
    glueableSpace O L J C D B SB UL T F PP Q FB A G R M ⟶
      glueableSpace O L J C D B SB UL T F PP Q FB A' G' R' M' := by
  let g := (underivedModuliFunctor F PP).map f
  refine { app := fun n => ↾fun e => ⟨g.app n e.val, ?_⟩, naturality := ?_ }
  · rw [SSet.mem_fullEnhancedSubcategory_obj_iff]
    intro v
    have he := (SSet.mem_fullEnhancedSubcategory_obj_iff
      (IsGlueableVertex O L J C D B SB UL T F PP Q FB A G R M) e.val).mp e.property
    have h := preserves (((underivedModuliFunctor F PP).obj A).map v.op e.val) (he v)
    have hn := congrArg (fun t => t e.val) (g.naturality v.op)
    change g.app (op (SimplexCategory.mk 0))
      (((underivedModuliFunctor F PP).obj A).map v.op e.val) =
      ((underivedModuliFunctor F PP).obj A').map v.op (g.app n e.val) at hn
    rwa [← hn]
  · intro n m a
    ext e
    apply Subtype.ext
    exact congrArg (fun t => t e.val) (g.naturality a)

/-- The native fundamental groupoid functor is applied AFTER that complete coefficient transport. -/
def glueableCoefficientGroupoidMap {PP : StrictPerfectSystem N S}
    (M : ModuliSimplexModuleSources F PP A) (M' : ModuliSimplexModuleSources F PP A')
    (preserves : ∀ e : ((underivedModuliFunctor F PP).obj A) _⦋0⦌,
      IsGlueableVertex O L J C D B SB UL T F PP Q FB A G R M e →
      IsGlueableVertex O L J C D B SB UL T F PP Q FB A' G' R' M'
        (((underivedModuliFunctor F PP).map f).app (op (SimplexCategory.mk 0)) e)) :
    glueableGroupoid O L J C D B SB UL T F PP Q FB A G R M ⥤
      glueableGroupoid O L J C D B SB UL T F PP Q FB A' G' R' M' :=
  SSet.mapFundamentalGroupoid (glueableCoefficientMap O L J C D B SB UL T F Q FB f G G' R R' M M' preserves)

end MathlibExt.AlgebraicGeometry.ProperOrdinaryCoefficientTransport
