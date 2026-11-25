/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

/-
The source conditions and inverse-image comparison conventions follow
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Quot/ComplexesStack.lean and
Spaces/Perfect/RelativeSubcategory.lean. That source is Apache 2.0 and
has no individual author or copyright notice in these files. This is
an affine identity-situation adaptation to native Mathlib scheme sites;
the general Axiom algebraic-space implementation is not copied here.
-/

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Core

/-!
# The affine identity-situation source for the classical complexes stack

The structure ring on the small étale site is the literal global-section
presheaf on étale test schemes. Ringed inverse image uses the native
base-change functor and the global-section map of its first projection.
The derived inverse image is the native total left derived functor of
that module inverse image, with its localization comparison.

On an affine scheme, perfection means an isomorphism to the associated
small étale sheaf complex of a bounded finite projective module complex.
The classical locus additionally tests negative self-Ext after every
field-valued base change. The fibre is a groupoid of actual derived
isomorphisms. These are the conditions and arrows of Stacks 0DLD/0DLE
for the proper, flat, finitely presented identity of Spec k.

The sheaf and derived source constructions are explicit sourced outputs;
no groupoid comparison or moduli theorem is included in their inputs.
Reference: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Quot/ComplexesStack.lean, 0DLD/0DLE.
This is an adaptation of that source's affine identity situation, not
a port of its general algebraic-space category or algebraicity proof.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Global sections of the actual étale test scheme, with the actual ring maps. -/
def etaleStructurePresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ RingCat.{u} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ ⋙
    forget₂ CommRingCat RingCat

/-- The only ring-sheaf input is the sheaf axiom for that prescribed presheaf. -/
structure EtaleStructureSource (X : Scheme.{u}) : Prop where
  isSheaf : Presheaf.IsSheaf X.smallEtaleTopology (etaleStructurePresheaf X)

/-- The small étale structure ring has no freely supplied section presheaf. -/
def etaleStructureRing (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (X : Scheme.{u}) : Sheaf X.smallEtaleTopology RingCat.{u} :=
  ⟨etaleStructurePresheaf X, (O X).isSheaf⟩

/-- The actual small étale module category. -/
abbrev EtaleModules (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (X : Scheme.{u}) :=
  SheafOfModules.{u} (etaleStructureRing O X)

/-- Its actual quasi-isomorphism localization. -/
abbrev EtaleDerived (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (X : Scheme.{u}) :=
  DerivedCategory (EtaleModules O X)

/-- Base change of every actual étale test scheme, retaining its native arrows. -/
def etaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback (@Etale) ⊤ f

/-- The source ringed-site map is fixed by the actual first pullback projection. -/
structure EtaleRingedMapSource (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  [continuous : (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology]
  ringMap : etaleStructureRing O Y ⟶
    ((etaleBaseChange f).sheafPushforwardContinuous RingCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj (etaleStructureRing O X)
  ringMap_eq : ∀ U : Y.Etale, ringMap.hom.app (op U) =
    (forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map (op (pullback.fst U.hom f)))
  [rightAdjoint : (SheafOfModules.pushforward.{u} ringMap).IsRightAdjoint]
  [additive : (SheafOfModules.pullback.{u} ringMap).Additive]

/-- Literal native ringed inverse image; its source map is prescribed above. -/
def etaleModulePullback {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) :
    EtaleModules O Y ⥤ EtaleModules O X :=
  letI := D.continuous
  letI := D.rightAdjoint
  SheafOfModules.pullback D.ringMap

instance {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) :
    (etaleModulePullback D).Additive :=
  D.additive

/-- The ordinary inverse image followed by the actual quasi-isomorphism quotient. -/
def etalePullbackBeforeDeriving {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) :
    CochainComplex (EtaleModules O Y) ℤ ⥤ EtaleDerived O X :=
  (etaleModulePullback D).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The condition that the inverse image of étale modules along `f` given by the ringed-site data
`D`, applied degreewise to complexes and followed by the localization to the derived category, has a
left derived functor with respect to quasi-isomorphisms. -/
structure EtaleDerivedPullbackSource {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (D : EtaleRingedMapSource O f) : Prop where
  hasLeftDerived : (etalePullbackBeforeDeriving D).HasLeftDerivedFunctor
    (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ))

/-- Actual derived inverse image, computed as native total left derivation. -/
def etaleDerivedPullback {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {D : EtaleRingedMapSource O f}
    (L : EtaleDerivedPullbackSource D) : EtaleDerived O Y ⥤ EtaleDerived O X :=
  letI := L.hasLeftDerived
  (etalePullbackBeforeDeriving D).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ))

/-- The native total-left-derived comparison is retained, rather than a freely named counit. -/
def etaleDerivedPullbackCounit {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {D : EtaleRingedMapSource O f}
    (L : EtaleDerivedPullbackSource D) :
    DerivedCategory.Q ⋙ etaleDerivedPullback L ⟶ etalePullbackBeforeDeriving D :=
  letI := L.hasLeftDerived
  (etalePullbackBeforeDeriving D).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ))

instance {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {D : EtaleRingedMapSource O f}
    (L : EtaleDerivedPullbackSource D) :
    (etaleDerivedPullback L).IsLeftDerivedFunctor (etaleDerivedPullbackCounit L)
      (HomologicalComplex.quasiIso (EtaleModules O Y) (.up ℤ)) := by
  letI := L.hasLeftDerived
  dsimp only [etaleDerivedPullback, etaleDerivedPullbackCounit]
  infer_instance

/-- A bounded finite projective presentation of an affine perfect complex. -/
structure StrictPerfectComplex (A : CommRingCat.{u}) where
  complex : CochainComplex (ModuleCat.{u} A) ℤ
  lower : ℤ
  upper : ℤ
  outside : ∀ n : ℤ, n < lower ∨ upper < n → IsZero (complex.X n)
  finite : ∀ n : ℤ, Module.Finite A (complex.X n)
  projective : ∀ n : ℤ, Module.Projective A (complex.X n)

/-- Native tilde followed by native scheme-module pullback on every étale test. -/
def zarAtEtaleTest (A : CommRingCat.{u}) (U : (Spec A).Etale) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} ((etaleStructurePresheaf (Spec A)).obj (op U)) :=
  tilde.functor A ⋙ Scheme.Modules.pullback U.hom ⋙
    SheafOfModules.evaluation U.left.ringCatSheaf (op ⊤)

/-- Actual test restriction: the native pullback adjunction unit and pullback-composition mate. -/
def zarEtaleRestriction (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
    {U V : (Spec A).Etale} (a : U ⟶ V) :
    Γ((Scheme.Modules.pullback V.hom).obj ((tilde.functor A).obj M), ⊤) ⟶
      Γ((Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj M), ⊤) := by
  let N := (Scheme.Modules.pullback V.hom).obj ((tilde.functor A).obj M)
  let N' := (Scheme.Modules.pullback a.left).obj N
  let unit := (Scheme.Modules.pullbackPushforwardAdjunction a.left).unit.app N
  let topIso : Γ((Scheme.Modules.pushforward a.left).obj N', ⊤) ≅ Γ(N', ⊤) :=
    eqToIso (congrArg (fun W : U.left.Opens => N'.presheaf.obj (op W)) (by simp))
  let comparison := Scheme.Modules.pullbackComp a.left V.hom ≪≫
    Scheme.Modules.pullbackCongr (show a.left ≫ V.hom = U.hom from by cat_disch)
  exact unit.app ⊤ ≫ topIso.hom ≫ (comparison.hom.app ((tilde.functor A).obj M)).app ⊤

/-- The affine Zar-to-étale module source is normalized on every test and every map. -/
structure AffineEtaleModuleSource (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (A : CommRingCat.{u}) where
  functor : ModuleCat.{u} A ⥤ EtaleModules O (Spec A)
  [additive : functor.Additive]
  [finiteLimits : PreservesFiniteLimits functor]
  [finiteColimits : PreservesFiniteColimits functor]
  testIso : ∀ U : (Spec A).Etale,
    functor ⋙ SheafOfModules.evaluation (etaleStructureRing O (Spec A)) (op U) ≅
      zarAtEtaleTest A U
  testRestriction : ∀ (M : ModuleCat.{u} A) {U V : (Spec A).Etale} (a : U ⟶ V),
    (functor.obj M).val.presheaf.map a.op ≫
      (forget₂ (ModuleCat ((etaleStructurePresheaf (Spec A)).obj (op U))) AddCommGrpCat).map
        ((testIso U).hom.app M) =
      (forget₂ (ModuleCat ((etaleStructurePresheaf (Spec A)).obj (op V))) AddCommGrpCat).map
        ((testIso V).hom.app M) ≫ zarEtaleRestriction A M a

attribute [instance] AffineEtaleModuleSource.additive
  AffineEtaleModuleSource.finiteLimits AffineEtaleModuleSource.finiteColimits

/-- The associated small étale sheaf complex is termwise that prescribed source functor. -/
def associatedEtaleComplex {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {A : CommRingCat.{u}} (J : AffineEtaleModuleSource O A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) : CochainComplex (EtaleModules O (Spec A)) ℤ :=
  J.functor.mapHomologicalComplex (.up ℤ) |>.obj K

/-- The associated ordinary source object is the native quotient of that same sheaf complex. -/
def associatedEtaleDerived {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {A : CommRingCat.{u}} (J : AffineEtaleModuleSource O A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) : EtaleDerived O (Spec A) :=
  DerivedCategory.Q.obj (associatedEtaleComplex J K)

/-- The perfect affine source uses actual bounded projective presentations. -/
def IsAffinePerfect {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    {A : CommRingCat.{u}} (J : AffineEtaleModuleSource O A)
    (E : EtaleDerived O (Spec A)) : Prop :=
  ∃ P : StrictPerfectComplex A, Nonempty (E ≅ associatedEtaleDerived J P.complex)

/-- Source-normalized derived inverse image along each actual ordinary scheme map. -/
structure EtalePullbackSystem (O : ∀ X : Scheme.{u}, EtaleStructureSource X) where
  ringed : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), EtaleRingedMapSource O f
  derived : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), EtaleDerivedPullbackSource (ringed f)

/-- Stacks 0DLD(2): literal negative self-Ext after every field-valued derived pullback. -/
def HasNoNegativeFibreExt {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) (A : CommRingCat.{u})
    (E : EtaleDerived O (Spec A)) : Prop :=
  ∀ (K : Type u) [Field K] (f : A →+* K) (i : ℤ), i < 0 →
    Subsingleton ((etaleDerivedPullback (L.derived (Spec.map (CommRingCat.ofHom f)))).obj E ⟶
      ((etaleDerivedPullback (L.derived (Spec.map (CommRingCat.ofHom f)))).obj E)⟦i⟧)

/-- The affine fibre of the source's universally glueable perfect-complex locus. -/
def ComplexesProperty {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) {A : CommRingCat.{u}} (J : AffineEtaleModuleSource O A) :
    ObjectProperty (EtaleDerived O (Spec A)) :=
  fun E => IsAffinePerfect J E ∧ HasNoNegativeFibreExt L A E

/-- The classical fibre is the actual core, so its arrows are actual derived isomorphisms. -/
abbrev ComplexesFibre {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (L : EtalePullbackSystem O) {A : CommRingCat.{u}} (J : AffineEtaleModuleSource O A) :=
  Core ((ComplexesProperty L J).FullSubcategory)

end MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
