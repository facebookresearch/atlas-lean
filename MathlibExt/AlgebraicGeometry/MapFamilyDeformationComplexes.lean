/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MapModuliCharts
public import MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
public import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
public import MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
public import MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps
public import MathlibExt.AlgebraicGeometry.DerivedInternalHom

/-!
# Actual map-family deformation complexes and evaluation derivatives

Fixed-source deformation uses Rπ_*Lf*T_V, with T_V the actual dual
of Kähler one-forms. Unmarked varying-source maps use
Rπ_*RHom(L_{C/(V×T)},O_C)[1], with full affine/overlap normalization.
Fixed-marking evaluation deformations use the actual marking ideal.
Moving-marking/log-cotangent comparisons remain a separate dependency.
These are computed objects, not freely named deformation complexes.

The fixed-source parameter differential is pinned on the actual functions
pulled from both product factors. Its dual and derived Kodaira--Spencer
map use the same actual sheaf morphism, native pullback/dual comparisons
and native derived unit. Evaluation is the actual marking followed by
the universal map.

Generic cotangent/transitivity/internal-Hom and universal Hom-stack
constructions are completed AxiomMath/Stacks integration at
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0), especially
Cotangent/SchemeCotangentComplex.lean and Stacks/HomStack/Basic.lean.
This records their native comparisons; general moduli representability
and the free-curve comparison remain explicit provider boundaries.
Primary reference: Graber--Harris--Starr, arXiv math/0109220v1, §2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
open MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.DerivedInternalHom
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [CommRing k]

/-- The tangent sheaf is the actual internal dual of Kähler one-forms. -/
abbrev tangent (X : Over (Spec (.of k))) := dual (forms k X 1)

/-- Actual fixed-source curve over the map parameter scheme. -/
abbrev fixedCurve (C T : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (pullback.snd C.hom T.hom ≫ T.hom)

abbrev fixedProjection (C T : Over (Spec (.of k))) : (fixedCurve C T).left ⟶ T.left :=
  pullback.snd C.hom T.hom

abbrev fixedSourceProjection (C T : Over (Spec (.of k))) :
    (fixedCurve C T).left ⟶ C.left := pullback.fst C.hom T.hom

def fixedMapOver (C V T : Over (Spec (.of k))) (F : FixedMap C.hom V.hom T) :
    fixedCurve C T ⟶ V := Over.homMk F.map F.over

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- The actual fixed-source deformation object. -/
def fixedDeformation (C V T : Over (Spec (.of k))) (F : FixedMap C.hom V.hom T) :
    D T.left :=
  (derivedPushforward (fixedProjection C T)).obj
    ((derivedPullback F.map).obj
      ((DerivedCategory.singleFunctor V.left.Modules 0).obj (tangent V)))

/-- The varying-source object retains C→V×_S T and the full actual cotangent normalization. -/
def varyingDeformation {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : GeneralStableMapFamilies.Family q n g T b)
    (L : CotangentNormalization (GeneralStableMapFamilies.mapToRelativeTarget F))
    [((derivedTensor F.curve.X).obj (DerivedCategory.Q.obj L.complex)).IsLeftAdjoint] : D T :=
  ((derivedPushforward F.curve.π).obj
    (internalHom F.curve.X (DerivedCategory.Q.obj L.complex) (derivedUnit F.curve.X)))⟦(1 : ℤ)⟧

/-- Actual marked ideal: kernel of all literal marking structure-unit maps. -/
def markingIdeal {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : GeneralStableMapFamilies.Family q n g T b) : F.curve.X.Modules :=
  kernel (Pi.lift (fun i : Fin n => structureUnit (F.curve.marking i)))

/-- The actual fixed-marking evaluation obstruction object. It does not replace
the moving-marking deformation complex. -/
def markedEvaluationDeformation (V T : Over (Spec (.of k))) {n g : ℕ}
    (F : GeneralStableMapFamilies.Family V.hom n g T.left T.hom) : D T.left :=
  (derivedPushforward F.curve.π).obj
    (((derivedTensor F.curve.X).obj
      ((derivedPullback F.map).obj
        ((DerivedCategory.singleFunctor V.left.Modules 0).obj (tangent V)))).obj
      ((DerivedCategory.singleFunctor F.curve.X.Modules 0).obj (markingIdeal F)))

def evaluationOver {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    (F : GeneralStableMapFamilies.Family q n g T b)
    (v : V ⟶ Spec (.of k)) (t : T ⟶ Spec (.of k))
    (h : ∀ i : Fin n, GeneralStableMapFamilies.evaluation F i ≫ v = t)
    (i : Fin n) : Over.mk t ⟶ Over.mk v :=
  Over.homMk (GeneralStableMapFamilies.evaluation F i) (h i)

/-- Product parameter projection fixed on regular functions from both factors. -/
structure ProductParameterDifferential (C T : Over (Spec (.of k))) where
  map : forms k (fixedCurve C T) 1 ⟶
    (Scheme.Modules.pullback (fixedProjection C T)).obj (forms k T 1)
  source_constant : ∀ (U : C.left.Opens) (W : (fixedCurve C T).left.Opens)
    (h : W ≤ fixedSourceProjection C T ⁻¹ᵁ U) (a : Γ(C.left,U)),
    (map.app W) (differential (fixedCurve C T) W
      (((fixedSourceProjection C T).appLE U W h).hom a)) = 0
  parameter_identity : ∀ (U : T.left.Opens) (W : (fixedCurve C T).left.Opens)
    (h : W ≤ fixedProjection C T ⁻¹ᵁ U) (a : Γ(T.left,U)),
    (map.app W) (differential (fixedCurve C T) W
      (((fixedProjection C T).appLE U W h).hom a)) =
    localPullbackSection (fixedProjection C T) (forms k T 1) U W h (differential T U a)

/-- Universal-map differential with the fixed source factor held constant. -/
def parameterDerivative (C V T : Over (Spec (.of k))) (F : FixedMap C.hom V.hom T)
    (P : ProductParameterDifferential C T)
    (E : PullbackDifferential V (fixedMapOver C V T F)) :
    (Scheme.Modules.pullback F.map).obj (forms k V 1) ⟶
      (Scheme.Modules.pullback (fixedProjection C T)).obj (forms k T 1) := E.map ≫ P.map

/-- A comparison isomorphism $f^*(M^\vee) \cong (f^* M)^\vee$ for a morphism of schemes
$f : Y \to X$ and an $\mathcal{O}_X$-module $M$, where $M^\vee = \mathcal{H}om(M, \mathcal{O}_X)$,
compatible with evaluation: for opens $U \subseteq X$ and $W \subseteq f^{-1}(U)$ and sections
$\varphi$ of $M^\vee$ and $s$ of $M$ over $U$, the image of the pullback of $\varphi$ to $W$,
evaluated on the pullback of $s$ to $W$, is the pullback $f^\#(\varphi(s))$ to $W$. -/
structure DualPullback {X Y : Scheme.{0}} (f : Y ⟶ X) (M : X.Modules) where
  comparison : (Scheme.Modules.pullback f).obj (dual M) ≅
    dual ((Scheme.Modules.pullback f).obj M)
  normalized : ∀ (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (φ : Γ(dual M,U)) (s : Γ(M,U)),
    localHomValue Y ((Scheme.Modules.pullback f).obj M) (structureModule Y) W
      ((comparison.hom.app W) (localPullbackSection f (dual M) U W h φ))
      (localPullbackSection f M U W h s) =
    (f.appLE U W h).hom (localHomValue X M (structureModule X) U φ s)

/-- Actual Hom-precomposition, fixed on every local homomorphism and section. -/
structure DualPrecomposition {X : Scheme.{0}} {M N : X.Modules} (a : M ⟶ N) where
  map : dual N ⟶ dual M
  normalized : ∀ (U : X.Opens) (φ : Γ(dual N,U)) (s : Γ(M,U)),
    localHomValue X M (structureModule X) U ((map.app U) φ) s =
      localHomValue X N (structureModule X) U φ ((a.app U) s)

/-- Parameter tangent map computed by dualizing the actual relative derivative. -/
def parameterTangent (C V T : Over (Spec (.of k))) (F : FixedMap C.hom V.hom T)
    (P : ProductParameterDifferential C T)
    (E : PullbackDifferential V (fixedMapOver C V T F))
    (PC : DualPrecomposition (parameterDerivative C V T F P E))
    (DT : DualPullback (fixedProjection C T) (forms k T 1))
    (DV : DualPullback F.map (forms k V 1)) :
    (Scheme.Modules.pullback (fixedProjection C T)).obj (tangent T) ⟶
      (Scheme.Modules.pullback F.map).obj (tangent V) :=
  DT.comparison.hom ≫ PC.map ≫ DV.comparison.inv

/-- Native derived transpose of a displayed module map. -/
def derivedTranspose (C V T : Over (Spec (.of k))) (F : FixedMap C.hom V.hom T)
    (a : (Scheme.Modules.pullback (fixedProjection C T)).obj (tangent T) ⟶
      (Scheme.Modules.pullback F.map).obj (tangent V))
    (A : PullPushAdjunction (fixedProjection C T))
    (hT : IsIso ((derivedPullbackCounit (fixedProjection C T)).app
      ((CochainComplex.singleFunctor T.left.Modules 0).obj (tangent T))))
    (hV : IsIso ((derivedPullbackCounit F.map).app
      ((CochainComplex.singleFunctor V.left.Modules 0).obj (tangent V)))) :
    (DerivedCategory.singleFunctor T.left.Modules 0).obj (tangent T) ⟶ fixedDeformation C V T F :=
  A.adjunction.unit.app _ ≫
    (derivedPushforward (fixedProjection C T)).map
      ((singlePullbackIso (fixedProjection C T) (tangent T) 0 hT).hom ≫
        (DerivedCategory.singleFunctor (fixedCurve C T).left.Modules 0).map a ≫
        (singlePullbackIso F.map (tangent V) 0 hV).inv)

/-- Family Kodaira--Spencer morphism computed from the parameter differential's transpose. -/
def familyKodairaSpencer (C V T : Over (Spec (.of k))) (F : FixedMap C.hom V.hom T)
    (P : ProductParameterDifferential C T)
    (E : PullbackDifferential V (fixedMapOver C V T F))
    (PC : DualPrecomposition (parameterDerivative C V T F P E))
    (DT : DualPullback (fixedProjection C T) (forms k T 1))
    (DV : DualPullback F.map (forms k V 1))
    (A : PullPushAdjunction (fixedProjection C T))
    (hT : IsIso ((derivedPullbackCounit (fixedProjection C T)).app
      ((CochainComplex.singleFunctor T.left.Modules 0).obj (tangent T))))
    (hV : IsIso ((derivedPullbackCounit F.map).app
      ((CochainComplex.singleFunctor V.left.Modules 0).obj (tangent V)))) :=
  derivedTranspose C V T F (parameterTangent C V T F P E PC DT DV) A hT hV


/-- An étale chart of the actual fixed-source Hom model, with all derivative data fixed. -/
structure FixedHomDifferentialData (C V : Over (Spec (.of k)))
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas) where
  parameter : ProductParameterDifferential C a.U
  differential : PullbackDifferential V (fixedMapOver C V a.U (M.family a.U a.point))
  precomposition : DualPrecomposition
    (parameterDerivative C V a.U (M.family a.U a.point) parameter differential)
  dualParameter : DualPullback (fixedProjection C a.U) (forms k a.U 1)
  dualTarget : DualPullback (M.family a.U a.point).map (forms k V 1)
  adjunction : PullPushAdjunction (fixedProjection C a.U)
  flatParameter : IsIso ((derivedPullbackCounit (fixedProjection C a.U)).app
    ((CochainComplex.singleFunctor a.U.left.Modules 0).obj (tangent a.U)))
  targetBundle : IsIso ((derivedPullbackCounit (M.family a.U a.point).map).app
    ((CochainComplex.singleFunctor V.left.Modules 0).obj (tangent V)))

/-- The chart comparison arrow uses the computed parameter derivative of its universal map. -/
def FixedHomDifferentialData.kodairaSpencer {C V : Over (Spec (.of k))}
    {M : FixedModel C.hom V.hom} {a : M.stack.EtaleAtlas}
    (B : FixedHomDifferentialData C V M a) :=
  familyKodairaSpencer C V a.U (M.family a.U a.point) B.parameter B.differential
    B.precomposition B.dualParameter B.dualTarget B.adjunction B.flatParameter B.targetBundle

end MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
