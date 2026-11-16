/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperOrdinaryModuleRealization
public import MathlibExt.AlgebraicGeometry.DGFrameAllSimplexUnits
public import MathlibExt.AlgebraicTopology.FullEnhancedSubcategory

/-!
# Native common-unit realization and the actual ordinary glueable locus

All simplices retain their complete original enveloping-module
replacement and common-degeneracy induction unit. The actual full
module/geometric realization is applied to those units before forming
the source fundamental groupoid. Vertex restrictions use the original
uncurrying value equalities on every coefficient index.

The locus is exactly relative perfection plus no negative field
self-Ext of the same realized X_A complex. Its target is the native
SpaceComplexAffinePresentations.ComplexesFibre. Higher source simplices
are retained until the explicit fundamental-groupoid operation.

Source: Toën--Vaquié arXiv:math/0503269v5, Sections 3.1/3.5 and
Remark 3.30(2); Stacks 0DLD/0DLE. Native source notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperOrdinaryGlueableRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
open MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DGFrameCoefficientUnits
open MathlibExt.AlgebraicGeometry.DGFrameAllSimplexUnits
open MathlibExt.AlgebraicGeometry.ProperOrdinaryModuleRealization
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {T₀ : DGCat k}
    (F : DGFrame k (oppositeCategory T₀)) {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)

/-- The actual i-th vertex of the entire original moduli simplex. -/
def moduliSimplexVertex (n : SimplexCategory)
    (e : ((underivedModuliFunctor F P).obj A).obj (op n)) (i : Fin (n.len + 1)) :=
  ((underivedModuliFunctor F P).obj A).map (SimplexCategory.const ⦋0⦌ n i).op e

/-- Restriction applies the actual full DG restriction to the same closed module morphism. -/
def restrictNativeModuleMap {C C' : DGCat k} {f : C ⟶ C'} (R : RestrictionModel f)
    {V W : RightModule k C'} (a : V ⟶ W) : R.functor.obj V ⟶ R.functor.obj W := by
  let z := R.functor.dgMap 0 ((DGFunctor.homEquivDGCycles k V W) a).val
  have hz : dgDifferential k 0 z = 0 := by
    rw [← R.functor.dgMap_dgDifferential,
      (mem_dgCycles k).mp ((DGFunctor.homEquivDGCycles k V W) a).property, map_zero]
  exact (DGFunctor.homEquivDGCycles k _ _).symm ⟨z, (mem_dgCycles k).mpr hz⟩

/-- All native simplex modules and their original endpoint/degeneracy units are chosen together. -/
structure ModuliSimplexModuleSources where
  vertex : ∀ e : ((underivedModuliFunctor F P).obj A) _⦋0⦌,
    EnvelopingModuleModel (vertexBimodule F P (ordinaryAlgebras.obj A) e)
  simplex : ∀ (n : SimplexCategory) (e : ((underivedModuliFunctor F P).obj A).obj (op n)),
    SimplexModulePoint F P (ordinaryAlgebras.obj A) n e
  envelope : ∀ (n : SimplexCategory) (_e : ((underivedModuliFunctor F P).obj A).obj (op n)),
    SimplexEnvelopeRetraction F (N := N) (ordinaryAlgebras.obj A) n
  restriction : ∀ n e, RestrictionModel (envelope n e).retraction.functor
  extension : ∀ n e, ExtensionModel (envelope n e).retraction.functor (restriction n e)
  endpoint : ∀ n e i, RestrictionModel ((envelope n e).endpoint i).functor
  identity : ∀ n e i, RestrictionCompositeIdentity ((envelope n e).endpoint i).functor
    (envelope n e).retraction.functor ((envelope n e).commutes i) (endpoint n e i) (restriction n e)
  endpointIso : ∀ n e i,
    (endpoint n e i).functor.obj (simplex n e).uncurried.module ≅
      (vertex (moduliSimplexVertex F P A n e i)).module
  endpointValue : ∀ n e i (x : F.diagram.obj ⦋0⦌) (y : (coefficientCategory N (ordinaryAlgebras.obj A))ᵒᵖ),
    ((endpoint n e i).functor.obj (simplex n e).uncurried.module).toEnrichedFunctor.obj
        (moduleIndex (F.diagram.obj ⦋0⦌) (coefficientCategory N (ordinaryAlgebras.obj A)) x y) =
      (vertex (moduliSimplexVertex F P A n e i)).module.toEnrichedFunctor.obj
        (moduleIndex (F.diagram.obj ⦋0⦌) (coefficientCategory N (ordinaryAlgebras.obj A)) x y)
  endpointNormalized : ∀ n e i x y,
    moduleComponent (endpointIso n e i).hom
      (moduleIndex (F.diagram.obj ⦋0⦌) (coefficientCategory N (ordinaryAlgebras.obj A)) x y) =
      eqToHom (endpointValue n e i x y)
  endpointWeak : ∀ n e i (x : (ordinaryEnvelope F N A)ᵒᵖ),
    QuasiIso (moduleComponent
      (restrictNativeModuleMap (endpoint n e i) (simplex n e).replacement.augmentation ≫
        (endpointIso n e i).hom) x)
  unitWeak : ∀ n e i (x : (ordinaryEnvelope F N A)ᵒᵖ),
    QuasiIso (moduleComponent
      (simplexInductionUnit F (ordinaryAlgebras.obj A) n (envelope n e) (restriction n e)
        (extension n e) (endpoint n e) (identity n e)
        ⟨(simplex n e).replacement.module, (simplex n e).replacement.cofibrant⟩ i) x)

/-- The literal derived-to-ordinary coefficient map is the original piZeroAugmentation. -/
def ordinaryCoefficientSpecialization (B : SAlg k) : (moduliFunctor F P).obj B ⟶
    (underivedModuliFunctor F P).obj (piZero B) :=
  (moduliFunctor F P).map (piZeroAugmentation B)

/-- The ordinary coefficient zero-endpoint is the original source face, in every frame. -/
theorem moduliEdgeSource {x y : ((underivedModuliFunctor F P).obj A) _⦋0⦌}
    (e : SSet.Edge (X := (underivedModuliFunctor F P).obj A) x y) :
    moduliSimplexVertex F P A ⦋1⦌ e.edge 0 = x := by
  have h : SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
    ext i
    fin_cases i
    rfl
  rw [moduliSimplexVertex, h]
  exact e.src_eq

/-- The one-endpoint is the same original target face. -/
theorem moduliEdgeTarget {x y : ((underivedModuliFunctor F P).obj A) _⦋0⦌}
    (e : SSet.Edge (X := (underivedModuliFunctor F P).obj A) x y) :
    moduliSimplexVertex F P A ⦋1⦌ e.edge 1 = y := by
  have h : SimplexCategory.const ⦋0⦌ ⦋1⦌ (1 : Fin 2) = SimplexCategory.δ (0 : Fin 2) := by
    ext i
    fin_cases i
    rfl
  rw [moduliSimplexVertex, h]
  exact e.tgt_eq

/-- Objectwise module weak maps are inverted in the native WHOLE module localization. -/
theorem moduleMap_isIso (W : DGCat k) {V V' : RightModule k W}
    (f : V ⟶ V') (hf : ∀ x, QuasiIso (moduleComponent f x)) :
    IsIso ((moduleQ (fun x : Wᵒᵖ => canonicalEvaluation (k := k) x)).map f) :=
  (moduleWeakEquivalences (fun x : Wᵒᵖ => canonicalEvaluation (k := k) x)).Q_inverts f hf

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ B : CommRingCat.{u}, AffineEtaleModuleSource O B)
    (C : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)
    (SB : ScalarLinearitySource B.ring (affineProperProjection D B)) (UL : CochainLiftModel B.ring)
    (T : SmallPerfectTestModel O L J C SB UL)
    (FF : DGFrame B.ring (oppositeCategory T.category))
    {NN : ShuffleAlgebraFunctor B.ring} {SS : AffineScalarSystem NN} (PP : StrictPerfectSystem NN SS)
    (Q : PullbackSystem.{u}) (FB : NativeFramePerfectTests O L J C D B SB UL T FF)
    (AA : CommAlgCat.{u} B.ring)
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T FF (N := NN) Q FB AA)
    (R : OrdinaryModuleRealization O L J C D B SB UL T FF Q FB AA G)
    (M : ModuliSimplexModuleSources FF PP AA)

/-- The native realized vertex is the image of the entire original enveloping module. -/
def realizedVertex (e : ((underivedModuliFunctor FF PP).obj AA) _⦋0⦌) : Derived (coefficientSpace D B AA) :=
  R.functor.obj ((moduleQ (fun x : (ordinaryEnvelope FF NN AA)ᵒᵖ => canonicalEvaluation (k := B.ring) x)).obj
    (M.vertex e).module)

/-- Each actual simplex vertex is connected to the SAME realized induced module by the SAME native unit. -/
def realizedSimplexLeg (n : SimplexCategory) (e : ((underivedModuliFunctor FF PP).obj AA).obj (op n))
    (i : Fin (n.len + 1)) :
    realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M (moduliSimplexVertex FF PP AA n e i) ≅
    R.functor.obj ((moduleQ (fun x : (ordinaryEnvelope FF NN AA)ᵒᵖ => canonicalEvaluation (k := B.ring) x)).obj
      (simplexInduction FF (ordinaryAlgebras.obj AA) n (M.envelope n e) (M.restriction n e)
        (M.extension n e) ⟨(M.simplex n e).replacement.module, (M.simplex n e).replacement.cofibrant⟩)) := by
  let a := restrictNativeModuleMap (M.endpoint n e i) (M.simplex n e).replacement.augmentation ≫
    (M.endpointIso n e i).hom
  let b := simplexInductionUnit FF (ordinaryAlgebras.obj AA) n (M.envelope n e) (M.restriction n e)
    (M.extension n e) (M.endpoint n e) (M.identity n e)
    ⟨(M.simplex n e).replacement.module, (M.simplex n e).replacement.cofibrant⟩ i
  let q := moduleQ (fun x : (ordinaryEnvelope FF NN AA)ᵒᵖ => canonicalEvaluation (k := B.ring) x)
  letI := moduleMap_isIso (ordinaryEnvelope FF NN AA) a (M.endpointWeak n e i)
  letI := moduleMap_isIso (ordinaryEnvelope FF NN AA) b (M.unitWeak n e i)
  exact (asIso (R.functor.map (q.map a))).symm ≪≫ asIso (R.functor.map (q.map b))

/-- The ordinary locus is the native source relative-perfect/no-negative-fibre-Ext condition on this actual image. -/
def IsGlueableVertex (e : ((underivedModuliFunctor FF PP).obj AA) _⦋0⦌) : Prop :=
  SpaceComplexAffinePresentations.ComplexesProperty Q L J C D (coefficientFamily D B AA).test
    (realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M e)

/-- The complete source simplices are retained on that exact actual vertex locus. -/
def glueableSpace : SSet.{u + 1} :=
  (((underivedModuliFunctor FF PP).obj AA).fullEnhancedSubcategory
    (IsGlueableVertex O L J C D B SB UL T FF PP Q FB AA G R M)).toSSet

/-- Correct ordinary source: fundamental groupoid only AFTER imposing the actual universally glueable locus. -/
abbrev glueableGroupoid := SSet.FundamentalGroupoid (glueableSpace O L J C D B SB UL T FF PP Q FB AA G R M)

/-- The edge is the actual ratio of the SAME two realized original induction-unit legs. -/
def realizedEdgeIso {x y : ((underivedModuliFunctor FF PP).obj AA) _⦋0⦌}
    (e : SSet.Edge (X := (underivedModuliFunctor FF PP).obj AA) x y) :
    realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M x ≅
      realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M y :=
  eqToIso (congrArg (realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M)
    (moduliEdgeSource FF PP AA e)).symm ≪≫
  realizedSimplexLeg O L J C D B SB UL T FF PP Q FB AA G R M ⦋1⦌ e.edge 0 ≪≫
  (realizedSimplexLeg O L J C D B SB UL T FF PP Q FB AA G R M ⦋1⦌ e.edge 1).symm ≪≫
  eqToIso (congrArg (realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M)
    (moduliEdgeTarget FF PP AA e))

/-- The unresolved triangle proof concerns these computed module/unit images of the native two-simplex. -/
structure OrdinaryRealizationTriangles where
  triangle : ∀ {x₀ x₁ x₂ : ((underivedModuliFunctor FF PP).obj AA) _⦋0⦌}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂} {e₀₂ : SSet.Edge x₀ x₂},
    SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂ →
    realizedEdgeIso O L J C D B SB UL T FF PP Q FB AA G R M e₀₁ ≪≫
      realizedEdgeIso O L J C D B SB UL T FF PP Q FB AA G R M e₁₂ =
    realizedEdgeIso O L J C D B SB UL T FF PP Q FB AA G R M e₀₂

/-- A locus vertex is the SAME actual realized source complex with both native source conditions. -/
def complexesVertex (e : (glueableSpace O L J C D B SB UL T FF PP Q FB AA G R M) _⦋0⦌) :
    SpaceComplexAffinePresentations.ComplexesFibre Q L J C D (coefficientFamily D B AA).test := by
  refine ⟨⟨realizedVertex O L J C D B SB UL T FF PP Q FB AA G R M e.val, ?_⟩⟩
  change IsGlueableVertex O L J C D B SB UL T FF PP Q FB AA G R M e.val
  have h := ((SSet.fullEnhancedSubcategory.verticesEquiv
    (IsGlueableVertex O L J C D B SB UL T FF PP Q FB AA G R M)) e).property
  simpa only [SSet.fullEnhancedSubcategory.verticesEquiv_apply_coe] using h

/-- The actual realized derived isomorphism is lifted to the native source complexes fibre. -/
def complexesEdge {x y : (glueableSpace O L J C D B SB UL T FF PP Q FB AA G R M) _⦋0⦌}
    (e : SSet.Edge x y) :
    complexesVertex O L J C D B SB UL T FF PP Q FB AA G R M x ⟶
      complexesVertex O L J C D B SB UL T FF PP Q FB AA G R M y :=
  ⟨(SpaceComplexAffinePresentations.ComplexesProperty Q L J C D (coefficientFamily D B AA).test).isoMk
    (realizedEdgeIso O L J C D B SB UL T FF PP Q FB AA G R M
      (e.map (((underivedModuliFunctor FF PP).obj AA).fullEnhancedSubcategory
        (IsGlueableVertex O L J C D B SB UL T FF PP Q FB AA G R M)).ι))⟩

/-- Native fundamental-groupoid descent is applied only after full module realization and the exact glueable locus. -/
def complexesGroupoidComparison
    (H : OrdinaryRealizationTriangles O L J C D B SB UL T FF PP Q FB AA G R M) :
    glueableGroupoid O L J C D B SB UL T FF PP Q FB AA G R M ⥤
      SpaceComplexAffinePresentations.ComplexesFibre Q L J C D (coefficientFamily D B AA).test :=
  SSet.FundamentalGroupoid.desc
    (complexesVertex O L J C D B SB UL T FF PP Q FB AA G R M)
    (complexesEdge O L J C D B SB UL T FF PP Q FB AA G R M)
    (by
      intro x₀ x₁ x₂ e₀₁ e₁₂ e₀₂ t
      apply CoreHom.ext
      apply Iso.ext
      apply ObjectProperty.hom_ext
      change _ ≫ _ = _
      exact congrArg (fun e => e.hom) (H.triangle (t.map
        (((underivedModuliFunctor FF PP).obj AA).fullEnhancedSubcategory
          (IsGlueableVertex O L J C D B SB UL T FF PP Q FB AA G R M)).ι)))

end MathlibExt.AlgebraicGeometry.ProperOrdinaryGlueableRealization
