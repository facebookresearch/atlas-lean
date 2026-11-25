/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps

/-!
# The literal identity-situation affine fibre of the native complexes stack

For the proper, flat, finitely presented identity of Spec k, the native
base change is X_A = Spec k times_(Spec k) Spec A. Its projection to
Spec A is the actual native pullback projection isomorphism. A ring
map induces the unique map of these base changes through that projection.

Objects are actual small étale derived modules on X_A, represented by
the pullback of a bounded finite projective affine complex, with negative
self-Ext vanishing on every field fibre. Arrows in a fixed fibre are the
actual derived isomorphisms. The comparison from the Spec A presentation
uses the actual derived pullback of its projection.

This adapts exactly the identity-situation affine part of
AlgebraicGeometry.Space.ComplexesObject/ComplexesHom in
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Quot/ComplexesStack.lean, 0DLD/0DLE.
It does not replace the general proper algebraic-space source stack.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
open MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps

universe u

variable {k : Type u} [CommRing k]

/-- The source identity is proper, as required in Stacks 0DLE. -/
theorem identity_isProper (k : Type u) [CommRing k] : IsProper (𝟙 (Spec (CommRingCat.of k))) := by
  infer_instance

/-- The source identity is flat, as required in Stacks 0DLE. -/
theorem identity_isFlat (k : Type u) [CommRing k] : Flat (𝟙 (Spec (CommRingCat.of k))) := by
  infer_instance

/-- The source identity is finitely presented. -/
theorem identity_isLocallyOfFinitePresentation (k : Type u) [CommRing k] :
    LocallyOfFinitePresentation (𝟙 (Spec (CommRingCat.of k))) := by
  infer_instance

/-- For a commutative ring `k`, the identity of `Spec k` is of finite presentation: it is locally
of finite presentation, quasi-compact and quasi-separated. -/
theorem identity_finitePresentation (k : Type u) [CommRing k] :
    LocallyOfFinitePresentation (𝟙 (Spec (CommRingCat.of k))) ∧
      QuasiCompact (𝟙 (Spec (CommRingCat.of k))) ∧
      QuasiSeparated (𝟙 (Spec (CommRingCat.of k))) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The source's actual X_A, with the native fibre-product object. -/
def identityBaseChange (A : CommAlgCat.{u} k) : Scheme.{u} :=
  pullback (𝟙 (Spec (CommRingCat.of k))) (Spec.algebraMap k A)

/-- The source projection is the actual second pullback projection. -/
def identityProjection (A : CommAlgCat.{u} k) : identityBaseChange A ⟶ Spec (ordinaryRing A) :=
  pullback.snd (𝟙 (Spec (CommRingCat.of k))) (Spec.algebraMap k A)

instance (A : CommAlgCat.{u} k) : IsIso (identityProjection A) := by
  dsimp only [identityProjection, identityBaseChange]
  infer_instance

/-- The affine identification is the native projection isomorphism. -/
def identityProjectionIso (A : CommAlgCat.{u} k) : identityBaseChange A ≅ Spec (ordinaryRing A) :=
  asIso (identityProjection A)

/-- The actual induced map of base changes, uniquely specified through the native projections. -/
def identityBaseChangeMap {A B : CommAlgCat.{u} k} (f : A ⟶ B) :
    identityBaseChange B ⟶ identityBaseChange A :=
  identityProjection B ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
    (identityProjectionIso A).inv

/-- The source induced map lies over the actual coefficient scheme map. -/
theorem identityBaseChangeMap_projection {A B : CommAlgCat.{u} k} (f : A ⟶ B) :
    identityBaseChangeMap f ≫ identityProjection A =
      identityProjection B ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
  simp [identityBaseChangeMap, Category.assoc, identityProjectionIso]

/-- The actual source X_h pullback arrow uses only native composition comparisons and this projection square. -/
def identitySourcePullbackMap {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {C : EtalePushforwardCoherence L}
    {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (H₁ : EtaleCompositeDerivationSource C (identityBaseChangeMap f) (identityProjection A))
    (H₂ : EtaleCompositeDerivationSource C (identityProjection B)
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom)))
    {E : EtaleDerived O (Spec (ordinaryRing A))} {E' : EtaleDerived O (Spec (ordinaryRing B))}
    (a : (etaleDerivedPullback (L.derived (Spec.map (CommRingCat.ofHom f.hom.toRingHom)))).obj E ⟶ E') :
    (etaleDerivedPullback (L.derived (identityBaseChangeMap f))).obj
      ((etaleDerivedPullback (L.derived (identityProjection A))).obj E) ⟶
    (etaleDerivedPullback (L.derived (identityProjection B))).obj E' :=
  (etaleDerivedComp H₁).inv.app E ≫
    (eqToIso (congrArg
      (fun h : identityBaseChange B ⟶ Spec (ordinaryRing A) => etaleDerivedPullback (L.derived h))
      (identityBaseChangeMap_projection f))).hom.app E ≫
    (etaleDerivedComp H₂).hom.app E ≫
    (etaleDerivedPullback (L.derived (identityProjection B))).map a

/-- The source comparison isomorphism is the actual native composition of these same maps. -/
def identitySourcePullbackIso {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {C : EtalePushforwardCoherence L}
    {A B : CommAlgCat.{u} k} {f : A ⟶ B}
    {H₁ : EtaleCompositeDerivationSource C (identityBaseChangeMap f) (identityProjection A)}
    {H₂ : EtaleCompositeDerivationSource C (identityProjection B)
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom))}
    {E : EtaleDerived O (Spec (ordinaryRing A))} {E' : EtaleDerived O (Spec (ordinaryRing B))}
    (a : (etaleDerivedPullback (L.derived (Spec.map (CommRingCat.ofHom f.hom.toRingHom)))).obj E ≅ E') :
    (etaleDerivedPullback (L.derived (identityBaseChangeMap f))).obj
      ((etaleDerivedPullback (L.derived (identityProjection A))).obj E) ≅
    (etaleDerivedPullback (L.derived (identityProjection B))).obj E' :=
  (etaleDerivedComp H₁).symm.app E ≪≫
    (eqToIso (congrArg
      (fun h : identityBaseChange B ⟶ Spec (ordinaryRing A) => etaleDerivedPullback (L.derived h))
      (identityBaseChangeMap_projection f))).app E ≪≫
    (etaleDerivedComp H₂).app E ≪≫
    (etaleDerivedPullback (L.derived (identityProjection B))).mapIso a

/-- Source relative perfection, via the actual bounded projective affine presentation on X_A. -/
def NativeIsRelativelyPerfect {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (A : CommAlgCat.{u} k)
    (J : AffineEtaleModuleSource O (ordinaryRing A))
    (E : EtaleDerived O (identityBaseChange A)) : Prop :=
  ∃ P : StrictPerfectComplex (ordinaryRing A),
    Nonempty (E ≅ (etaleDerivedPullback (L.derived (identityProjection A))).obj
      (associatedEtaleDerived J P.complex))

/-- Stacks 0DLD(2) on the literal source fibres and actual maps X_y to X_A. -/
def NativeHasNoNegativeFibreExt {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (A : CommAlgCat.{u} k)
    (E : EtaleDerived O (identityBaseChange A)) : Prop :=
  ∀ (K : CommAlgCat.{u} k) [Field K] (f : A ⟶ K) (i : ℤ), i < 0 →
    Subsingleton ((etaleDerivedPullback (L.derived (identityBaseChangeMap f))).obj E ⟶
      ((etaleDerivedPullback (L.derived (identityBaseChangeMap f))).obj E)⟦i⟧)

/-- The source objects retain both actual conditions of ComplexesObject. -/
def NativeComplexesProperty {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (A : CommAlgCat.{u} k)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) :
    ObjectProperty (EtaleDerived O (identityBaseChange A)) :=
  fun E => NativeIsRelativelyPerfect L A J E ∧ NativeHasNoNegativeFibreExt L A E

/-- The actual groupoid fibre of native identity-situation objects. -/
abbrev NativeComplexesFibre {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (A : CommAlgCat.{u} k)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) :=
  Core ((NativeComplexesProperty L A J).FullSubcategory)

/-- Transport is a source comparison proof for this exact projection and these exact field maps. -/
structure IdentityComplexesTransportSource {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (A : CommAlgCat.{u} k)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) : Prop where
  preserves : ∀ E : EtaleDerived O (Spec (ordinaryRing A)), ComplexesProperty L J E →
    NativeComplexesProperty L A J
      ((etaleDerivedPullback (L.derived (identityProjection A))).obj E)

/-- Actual derived inverse image under the native projection, retaining every object and arrow. -/
def identityComplexesTransportUnderlying {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {A : CommAlgCat.{u} k}
    {J : AffineEtaleModuleSource O (ordinaryRing A)} (H : IdentityComplexesTransportSource L A J) :
    (ComplexesProperty L J).FullSubcategory ⥤ (NativeComplexesProperty L A J).FullSubcategory where
  obj E := ⟨(etaleDerivedPullback (L.derived (identityProjection A))).obj E.obj,
    H.preserves E.obj E.property⟩
  map a := ObjectProperty.homMk
    ((etaleDerivedPullback (L.derived (identityProjection A))).map a.hom)
  map_id E := by
    apply ObjectProperty.hom_ext
    exact (etaleDerivedPullback (L.derived (identityProjection A))).map_id E.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (etaleDerivedPullback (L.derived (identityProjection A))).map_comp a.hom b.hom

/-- The comparison lands in the literal native source groupoid by actual inverse image. -/
def identityComplexesTransport {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {L : EtalePullbackSystem O} {A : CommAlgCat.{u} k}
    {J : AffineEtaleModuleSource O (ordinaryRing A)} (H : IdentityComplexesTransportSource L A J) :
    ComplexesFibre L J ⥤ NativeComplexesFibre L A J :=
  (identityComplexesTransportUnderlying H).core

/-- The actual DG groupoid comparison lands in the literal native X_A source by this projection pullback. -/
def nativeIdentityModuliComparison {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    {r : ScalarFramePoint R} {I : ScalarFrameInterval r} {P : StrictPerfectSystem N S}
    {A : CommAlgCat.{u} k} {F : ScalarFrameEdgeMaps I P A}
    {C : OrdinaryCoefficientSource N A} {V : OrdinaryModuleSource C}
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} {L : EtalePullbackSystem O}
    {J : AffineEtaleModuleSource O (ordinaryRing A)} (G : ClassicalComplexComparison F V L J)
    (H : IdentityComplexesTransportSource L A J) :
    universallyGlueableGroupoid r P A V L J ⥤ NativeComplexesFibre L A J :=
  G.functor ⋙ identityComplexesTransport H

end MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack
