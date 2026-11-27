/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootWeightEvaluations
public import MathlibExt.AlgebraicGeometry.CartesianStackModules

/-!
# Universal root weight lines on the actual cartesian stack-module category

Values on every affine root family are actual groupified DF root lines.
Their positive base-change comparison is computed from the native root
restriction functor, its actual fibre arrow, the DF inverse-image generator
and the native identity-etale pullback. Unit, multiplication, weight-arrow,
identity and composition diagrams fix the extension to all group weights.
The stack-module sections are normalized for both weight and base arrows.

This is the universal Lambda_v construction used by Borne--Vistoli,
https://arxiv.org/abs/1001.0466v2, Corollary 5.4 and Theorem 6.1.
The actual cartesian/QCoh category is the completed source adapter in
CartesianStackModules. Native tensor/pullback comparisons retain the
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache-2.0)
attribution in ModuleTensorPullbackSections. The root-specific universal
line construction is a separate Wanted endpoint.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.UniversalRootWeightLines
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackFibreModels _root_.AlgebraicGeometry.StackAffineModules
open _root_.AlgebraicGeometry.CartesianStackModules
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
open MathlibExt.AlgebraicGeometry.RootWeightEvaluations
open MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

variable {X : Scheme.{0}}
  [∀ (T Z : Scheme.{0}) (f : T ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (U : X.Etale) (R : Model I D j U.hom)

/-- The genuine root object represented by an actual affine stack point. -/
def rootObject (a : AffinePoint R.stack) := (R.fibre a.obj.base).functor.obj a.obj.fiber

/-- The actual root arrow obtained from the total fibre arrow and native reindexing. -/
def rootArrow {a b : AffinePoint R.stack} (h : a ⟶ b) :
    rootObject I D j U R a ⟶ (R.reindexing h.hom.base).functor.obj (rootObject I D j U R b) :=
  (R.fibre a.obj.base).functor.map h.hom.fiber ≫
    (R.mapComparison h.hom.base).hom.app b.obj.fiber

/-- The actual identity-etale pullback section for a scheme map. -/
def unitDiagonal {T V : Scheme.{0}} (f : V ⟶ T) :
    identityEtale V ⟶ (etaleBaseChange f).obj (identityEtale T) :=
  MorphismProperty.Over.homMk
    (pullback.lift f (𝟙 V) ((Category.comp_id f).trans (Category.id_comp f).symm)) (by
      change pullback.lift f (𝟙 V) _ ≫ pullback.snd (𝟙 T) f = 𝟙 V
      exact pullback.lift_snd _ _ _)

omit [∀ (T Z : Scheme.{0}) (f : T ⟶ Z), HasInverseImage f] in
theorem unitDiagonal_projection {T V : Scheme.{0}} (f : V ⟶ T) :
    (unitDiagonal f).left ≫ projection f (identityEtale T) = f := by
  change pullback.lift f (𝟙 V) _ ≫ pullback.fst (𝟙 T) f = f
  exact pullback.lift_fst _ _ _

/-- Native generator naturality along the actual parameter-scheme map. -/
def GeneratorNaturality : Prop :=
  ∀ (T V : Over U.left) (f : V ⟶ T) (b : B.obj.obj (op U)),
    (pulledMonoids ((Over.map U.hom).obj V) B).obj.map (unitDiagonal f.left).op
      ((monoidOverComparison B ((Over.map U.hom).map f)).hom.hom.app
        (op ((etaleBaseChange f.left).obj (identityEtale T.left)))
        (generator f.left (pulledMonoids ((Over.map U.hom).obj T) B)
          (identityEtale T.left) (localGenerators B U T b))) = localGenerators B U V b

/-- The actual positive line on a root family. -/
def familyPositiveLine {T : Over U.left}
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (v : B.obj.obj (op U)) : T.left.Modules :=
  (E.of.extended.chart (identityEtale T.left)).module (localGenerators B U T v)

/-- Native comparison between pullback along `f` and pullback along its
identity-etale diagonal followed by projection. -/
def diagonalPullbackIso {T V : Scheme.{0}} (f : V ⟶ T) (L : T.Modules) :
    (Scheme.Modules.pullback f).obj L ≅
      (Scheme.Modules.pullback (unitDiagonal f).left).obj
        ((Scheme.Modules.pullback (projection f (identityEtale T))).obj L) :=
  eqToIso (congrArg (fun q => (Scheme.Modules.pullback q).obj L)
    (unitDiagonal_projection f).symm) ≪≫
    (Scheme.Modules.pullbackComp (unitDiagonal f).left
      (projection f (identityEtale T))).symm.app L

/-- The inverse-image chart generator before the root-restriction comparison. -/
def inverseImageGenerator {T V : Over U.left} (f : V ⟶ T) (v : B.obj.obj (op U)) :=
  generator f.left (pulledMonoids ((Over.map U.hom).obj T) B)
    (identityEtale T.left) (localGenerators B U T v)

/-- Its actual image under the native comparison with the direct monoid pullback. -/
def reindexedGenerator {T V : Over U.left} (f : V ⟶ T) (v : B.obj.obj (op U)) :=
  (monoidOverComparison B ((Over.map U.hom).map f)).hom.hom.app
    (op ((etaleBaseChange f.left).obj (identityEtale T.left)))
      (inverseImageGenerator (B := B) U f v)

/-- The intermediate chart line of the actual DF inverse image. -/
def inverseImageLine {T V : Over U.left} (f : V ⟶ T)
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (v : B.obj.obj (op U)) :
    ((etaleBaseChange f.left).obj (identityEtale T.left)).left.Modules :=
  (((I V.left T.left f.left (pulledMonoids ((Over.map U.hom).obj T) B)).object
    E.of.extended).pulled.chart ((etaleBaseChange f.left).obj (identityEtale T.left))).module
      (inverseImageGenerator (B := B) U f v)

/-- The intermediate chart line of the actual reindexed root family. -/
def reindexedLine {T V : Over U.left} (f : V ⟶ T)
    (r : RootReindexing I D j ((Over.map U.hom).map f))
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (v : B.obj.obj (op U)) :
    ((etaleBaseChange f.left).obj (identityEtale T.left)).left.Modules :=
  ((r.functor.obj E).of.extended.chart
    ((etaleBaseChange f.left).obj (identityEtale T.left))).module
      (reindexedGenerator (B := B) U f v)

/-- The first native arrow stage: the actual DF inverse-image generator comparison. -/
def inverseImageLineIso {T V : Over U.left} (f : V ⟶ T)
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (v : B.obj.obj (op U)) :
    (Scheme.Modules.pullback (projection f.left (identityEtale T.left))).obj
      (familyPositiveLine I D j U E v) ≅ inverseImageLine I D j U f E v :=
  ((I V.left T.left f.left (pulledMonoids ((Over.map U.hom).obj T) B)).object
    E.of.extended).comparison (identityEtale T.left) (localGenerators B U T v)

/-- Evaluation of the prescribed root comparison over its actual log base.
Keeping the base arrow explicit avoids expanding iterated `Over.map` data
inside every coefficient module. -/
def nativeRootLineIso {T V : Over X} (q : V ⟶ T)
    (r : RootReindexing I D j q) (E : rootsAt I D j T) (Z : V.left.Etale)
    (g : ((monoidPullback q.left).obj (pulledMonoids T B)).obj.obj (op Z)) :
    (((I V.left T.left q.left (pulledMonoids T B)).object E.of.extended).pulled.chart Z).module g ≅
      ((r.functor.obj E).of.extended.chart Z).module
        ((monoidOverComparison B q).hom.hom.app (op Z) g) :=
  (r.rootComparison E).comparison Z g

-- Specializing native root coefficients performs a large dependent conversion.
set_option maxHeartbeats 2000000 in
/-- The second native arrow stage: the prescribed comparison of reindexed roots. -/
def reindexedLineIso {T V : Over U.left} (f : V ⟶ T)
    (r : RootReindexing I D j ((Over.map U.hom).map f))
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (v : B.obj.obj (op U)) :
    inverseImageLine I D j U f E v ≅ reindexedLine I D j U f r E v :=
  nativeRootLineIso I D j ((Over.map U.hom).map f) r E
    ((etaleBaseChange f.left).obj (identityEtale T.left))
    (inverseImageGenerator (B := B) U f v)

/-- Native DF restriction with its one generator-equality transport.
The root-family data are substituted only after this map is typechecked. -/
def nativeReindexLineIso {Y : Scheme.{0}} {M : DeligneFaltingsSheaves.MonoidSheaf Y}
    (F : Structure M) {V Z : Y.Etale} (e : V ⟶ Z)
    (c : M.obj.obj (op Z)) (d : M.obj.obj (op V)) (h : M.obj.map e.op c = d) :
    (Scheme.Modules.pullback e.left).obj ((F.chart Z).module c) ≅ (F.chart V).module d :=
  F.reindex e c ≪≫ eqToIso (congrArg (F.chart V).module h)

set_option maxHeartbeats 2000000 in
/-- The third native arrow stage: restriction along the identity-etale
diagonal, followed by the genuine local-generator equality. -/
def diagonalLineIso (N : GeneratorNaturality (B := B) U)
    {T V : Over U.left} (f : V ⟶ T)
    (r : RootReindexing I D j ((Over.map U.hom).map f))
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (v : B.obj.obj (op U)) :
    (Scheme.Modules.pullback (unitDiagonal f.left).left).obj
      (reindexedLine I D j U f r E v) ≅ familyPositiveLine I D j U (r.functor.obj E) v :=
  nativeReindexLineIso (r.functor.obj E).of.extended (unitDiagonal f.left)
    (reindexedGenerator (B := B) U f v) (localGenerators B U V v) (N T V f v)

/-- Evaluation of the actual root arrow on its actual positive generator. -/
def rootArrowLineIso {T V : Over U.left} (f : V ⟶ T)
    (r : RootReindexing I D j ((Over.map U.hom).map f))
    (E : rootsAt I D j ((Over.map U.hom).obj T))
    (H : rootsAt I D j ((Over.map U.hom).obj V))
    (k : H ⟶ r.functor.obj E) (v : B.obj.obj (op U)) :
    familyPositiveLine I D j U H v ≅ familyPositiveLine I D j U (r.functor.obj E) v :=
  k.iso.hom.hom.comparison (identityEtale V.left) (localGenerators B U V v)

/-- The native positive pullback square. Each arrow is the typed stage of
the genuine inverse-image/root-arrow/diagonal recipe above. -/
def PositiveRestrictionSquare (N : GeneratorNaturality (B := B) U)
    {T V : Over U.left} (f : V ⟶ T)
    (r : RootReindexing I D j ((Over.map U.hom).map f))
    (E : rootsAt I D j ((Over.map U.hom).obj T))
    (H : rootsAt I D j ((Over.map U.hom).obj V))
    (k : H ⟶ r.functor.obj E) (v : B.obj.obj (op U))
    (comparison : (Scheme.Modules.pullback f.left).obj
      (familyPositiveLine I D j U E v) ≅ familyPositiveLine I D j U H v) : Prop :=
  comparison.hom ≫ (rootArrowLineIso I D j U f r E H k v).hom =
    (diagonalPullbackIso f.left (familyPositiveLine I D j U E v)).hom ≫
    (Scheme.Modules.pullback (unitDiagonal f.left).left).map
      (inverseImageLineIso I D j U f E v).hom ≫
    (Scheme.Modules.pullback (unitDiagonal f.left).left).map
      (reindexedLineIso I D j U f r E v).hom ≫
    (diagonalLineIso I D j U N f r E v).hom

/-- Positive restriction data along an arrow $h : a \to b$ of affine points of the root stack $R$,
at a section $v$ of $B$ over $U$: an isomorphism from the pullback, along the base map $f$ of $h$,
of the positive line of the root object at $b$ (`familyPositiveLine`, the chart line of the local
generator of $v$) to the positive line of the root object at $a$ (`comparison`), whose composite
with the isomorphism of positive lines induced by the root arrow of $h$ (`rootArrowLineIso`) is the
composite of the identification $f^* \cong \Delta^* \mathrm{pr}^*$ for the identity-étale diagonal
$\Delta$, the inverse-image and reindexing comparisons of chart lines pulled back along $\Delta$,
and restriction along $\Delta$ using the generator naturality $N$ (`normalization`, the square
`PositiveRestrictionSquare`). -/
structure PositiveRestrictionData (N : GeneratorNaturality (B := B) U)
    {a b : AffinePoint R.stack} (h : a ⟶ b) (v : B.obj.obj (op U)) :
    Type 1 where
  comparison : (Scheme.Modules.pullback h.hom.base.left).obj
      (((rootObject I D j U R b).of.extended.chart (identityEtale b.obj.base.left)).module
        (localGenerators B U b.obj.base v)) ≅
    ((rootObject I D j U R a).of.extended.chart (identityEtale a.obj.base.left)).module
      (localGenerators B U a.obj.base v)
  normalization : PositiveRestrictionSquare I D j U N h.hom.base
    (R.reindexing h.hom.base) (rootObject I D j U R b) (rootObject I D j U R a)
    (rootArrow I D j U R h) v comparison

/-- The model's root-line comparisons are trivial on identity arrows: positive restriction
data on the identity arrow of an affine point has the identity pullback comparison. The
identity and composition laws of a `Model` constrain its reindexing functors, not these
evaluated line comparisons. -/
def IdentityLineCoherent : Prop :=
  ∀ (N : GeneratorNaturality (B := B) U) (a : AffinePoint R.stack) (v : B.obj.obj (op U))
    (P : PositiveRestrictionData I D j U R N (𝟙 a) v),
    P.comparison.hom = (Scheme.Modules.pullbackId a.obj.base.left).hom.app
      (((rootObject I D j U R a).of.extended.chart (identityEtale a.obj.base.left)).module
        (localGenerators B U a.obj.base v))

/-- The model's root-line comparisons compose: positive restriction data on two composable
arrows and on their composite have compatible comparisons. -/
def CompositionLineCoherent : Prop :=
  ∀ (N : GeneratorNaturality (B := B) U) {a b c : AffinePoint R.stack} (h : a ⟶ b) (k : b ⟶ c)
    (v : B.obj.obj (op U)) (P : PositiveRestrictionData I D j U R N h v)
    (Q : PositiveRestrictionData I D j U R N k v)
    (PQ : PositiveRestrictionData I D j U R N (h ≫ k) v),
    PQ.comparison.hom =
      (Scheme.Modules.pullbackComp h.hom.base.left k.hom.base.left).inv.app
        (((rootObject I D j U R c).of.extended.chart (identityEtale c.obj.base.left)).module
          (localGenerators B U c.obj.base v)) ≫
      (Scheme.Modules.pullback h.hom.base.left).map Q.comparison.hom ≫ P.comparison.hom

abbrev positiveWeight (b : B.obj.obj (op U)) : Weight (B.obj.obj (op U)) :=
  ⟨Algebra.GrothendieckGroup.of b⟩

abbrev oneWeight : Weight (B.obj.obj (op U)) := ⟨1⟩

def multiplyWeight (v w : Weight (B.obj.obj (op U))) : Weight (B.obj.obj (op U)) :=
  ⟨v.value * w.value⟩

def values (a : AffinePoint R.stack) (G : GroupifiedDF (rootObject I D j U R a).of.extended)
    (K : LineFunctorLaws (G.chart (identityEtale a.obj.base.left))) :=
  weightFunctorAt I D j U a.obj.base (rootObject I D j U R a) G K

def positiveIso (a : AffinePoint R.stack)
    (G : GroupifiedDF (rootObject I D j U R a).of.extended)
    (K : LineFunctorLaws (G.chart (identityEtale a.obj.base.left))) (v : B.obj.obj (op U)) :
    (values I D j U R a G K).obj (positiveWeight U v) ≅
      ((rootObject I D j U R a).of.extended.chart (identityEtale a.obj.base.left)).module
        (localGenerators B U a.obj.base v) :=
  eqToIso (congrArg (G.chart (identityEtale a.obj.base.left)).line
    (groupMap_of (localGenerators B U a.obj.base) v)) ≪≫
      (G.chart (identityEtale a.obj.base.left)).positive (localGenerators B U a.obj.base v)

def unitIso (a : AffinePoint R.stack)
    (G : GroupifiedDF (rootObject I D j U R a).of.extended)
    (K : LineFunctorLaws (G.chart (identityEtale a.obj.base.left))) :
    (values I D j U R a G K).obj (oneWeight (B := B) U) ≅
      MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.structureModule a.obj.base.left :=
  eqToIso (congrArg (G.chart (identityEtale a.obj.base.left)).line
    (map_one (groupMap (localGenerators B U a.obj.base)))) ≪≫
      (G.chart (identityEtale a.obj.base.left)).unit

def multiplicationIso (a : AffinePoint R.stack)
    (G : GroupifiedDF (rootObject I D j U R a).of.extended)
    (K : LineFunctorLaws (G.chart (identityEtale a.obj.base.left)))
    (v w : Weight (B.obj.obj (op U))) :
    moduleTensor a.obj.base.left ((values I D j U R a G K).obj v)
      ((values I D j U R a G K).obj w) ≅
        (values I D j U R a G K).obj (multiplyWeight U v w) :=
  (G.chart (identityEtale a.obj.base.left)).multiplication
    (groupMap (localGenerators B U a.obj.base) v.value)
    (groupMap (localGenerators B U a.obj.base) w.value) ≪≫
      eqToIso (congrArg (G.chart (identityEtale a.obj.base.left)).line
        (map_mul (groupMap (localGenerators B U a.obj.base)) v.value w.value).symm)

/-- Universal stack root weights, normalized on every actual affine root family and arrow. -/
structure StackWeights where
  groupified : ∀ a : AffinePoint R.stack, GroupifiedDF (rootObject I D j U R a).of.extended
  laws : ∀ a : AffinePoint R.stack, LineFunctorLaws ((groupified a).chart (identityEtale a.obj.base.left))
  generator_naturality : GeneratorNaturality (B := B) U
  line : Weight (B.obj.obj (op U)) ⥤ QCoh R.stack
  finitePresentation : ∀ (w : Weight (B.obj.obj (op U))) (a : (AffinePoint R.stack)ᵒᵖ),
    Module.FinitePresentation ((rings R.stack).obj a) ((line.obj w).obj.obj a)
  rankOne : ∀ w : Weight (B.obj.obj (op U)), HasConstantRank
    (show FPModule R.stack from
      { presheaf := (line.obj w).obj
        cartesian := (line.obj w).property
        finitePresentation := finitePresentation w }) 1
  sections : ∀ (w : Weight (B.obj.obj (op U))) (a : AffinePoint R.stack),
    (line.obj w).obj.obj (op a) ≃ₗ[Γ(a.obj.base.left, ⊤)]
      Γ((values I D j U R a (groupified a) (laws a)).obj w, ⊤)
  weight_naturality : ∀ {v w : Weight (B.obj.obj (op U))} (f : v ⟶ w)
      (a : AffinePoint R.stack) (s : (line.obj v).obj.obj (op a)),
    sections w a ((line.map f).hom.app (op a) s) =
      (((values I D j U R a (groupified a) (laws a)).map f).val.app
        (op (⊤ : a.obj.base.left.Opens))).hom (sections v a s)
  tensorPullback : ∀ {a b : AffinePoint R.stack} (h : a ⟶ b), PullbackTensorData h.hom.base.left
  baseComparison : ∀ (w : Weight (B.obj.obj (op U))) {a b : AffinePoint R.stack} (h : a ⟶ b),
    (Scheme.Modules.pullback h.hom.base.left).obj ((values I D j U R b (groupified b) (laws b)).obj w) ≅
      (values I D j U R a (groupified a) (laws a)).obj w
  positivePullback : ∀ {a b : AffinePoint R.stack} (h : a ⟶ b) (v : B.obj.obj (op U)),
    PositiveRestrictionData I D j U R generator_naturality h v
  positive_normalization : ∀ {a b : AffinePoint R.stack} (h : a ⟶ b) (v : B.obj.obj (op U)),
    (Scheme.Modules.pullback h.hom.base.left).map (positiveIso I D j U R b (groupified b) (laws b) v).hom ≫
      (positivePullback h v).comparison.hom =
    (baseComparison (positiveWeight U v) h).hom ≫ (positiveIso I D j U R a (groupified a) (laws a) v).hom
  unit_normalization : ∀ {a b : AffinePoint R.stack} (h : a ⟶ b),
    (Scheme.Modules.pullback h.hom.base.left).map (unitIso I D j U R b (groupified b) (laws b)).hom ≫
      SheafOfModules.pullbackObjUnitToUnit h.hom.base.left.toRingCatSheafHom =
    (baseComparison (oneWeight (B := B) U) h).hom ≫ (unitIso I D j U R a (groupified a) (laws a)).hom
  multiplication_normalization : ∀ {a b : AffinePoint R.stack} (h : a ⟶ b)
      (v w : Weight (B.obj.obj (op U))),
    (Scheme.Modules.pullback h.hom.base.left).map
      (multiplicationIso I D j U R b (groupified b) (laws b) v w).hom ≫
      (baseComparison (multiplyWeight U v w) h).hom =
    ((tensorPullback h).comparison ((values I D j U R b (groupified b) (laws b)).obj v)
      ((values I D j U R b (groupified b) (laws b)).obj w)).hom ≫
      tensorMap (baseComparison v h).hom (baseComparison w h).hom ≫
      (multiplicationIso I D j U R a (groupified a) (laws a) v w).hom
  arrow_normalization : ∀ {a b : AffinePoint R.stack} (h : a ⟶ b)
      {v w : Weight (B.obj.obj (op U))} (f : v ⟶ w),
    (Scheme.Modules.pullback h.hom.base.left).map ((values I D j U R b (groupified b) (laws b)).map f) ≫
      (baseComparison w h).hom =
    (baseComparison v h).hom ≫ (values I D j U R a (groupified a) (laws a)).map f
  base_identity : ∀ (a : AffinePoint R.stack) (w : Weight (B.obj.obj (op U))),
    (baseComparison w (𝟙 a)).hom =
      (Scheme.Modules.pullbackId a.obj.base.left).hom.app ((values I D j U R a (groupified a) (laws a)).obj w)
  base_composition : ∀ {a b c : AffinePoint R.stack} (h : a ⟶ b) (k : b ⟶ c)
      (w : Weight (B.obj.obj (op U))),
    (baseComparison w (h ≫ k)).hom =
    (Scheme.Modules.pullbackComp h.hom.base.left k.hom.base.left).inv.app
      ((values I D j U R c (groupified c) (laws c)).obj w) ≫
      (Scheme.Modules.pullback h.hom.base.left).map (baseComparison w k).hom ≫ (baseComparison w h).hom
  base_naturality : ∀ (w : Weight (B.obj.obj (op U))) {a b : AffinePoint R.stack} (h : a ⟶ b)
      (s : (line.obj w).obj.obj (op b)),
    sections w a ((line.obj w).obj.map h.op s) =
      ((baseComparison w h).hom.val.app (op (⊤ : a.obj.base.left.Opens))).hom
        (localPullback h.hom.base.left ((values I D j U R b (groupified b) (laws b)).obj w)
          ⊤ (sections w b s))

end MathlibExt.AlgebraicGeometry.UniversalRootWeightLines
