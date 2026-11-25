/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGenericSourceRefinementModels
public import MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Generic whole-diagram Li source assembly

The small local source diagram is normalized against the genuine Li
complexes and scaling maps on every qualified chart. It retains the
actual parent/source arrows and all coefficient actions. Its whole
module-presheaf diagram is lifted to universe 2 before a K-injective
replacement in that ENTIRE diagram category. Only then is the native
right-adjoint Kan extension applied.

The source comparison is ONE roof in the derived category of complete
coefficient diagrams: the source resolution and the native adjunction
counit. Objectwise isomorphisms cannot replace that roof. Derived scalar
extension on every affine parent arrow uses the literal balanced tensor
map with the actual presheaf restriction.

The normalized source diagram and its assembly are construction outputs.
Sources: Jun Li math/0110113v1 Sections 1--2; the native derived-category,
module-presheaf and Kan adjunction constructions in frozen Mathlib.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGenericSourceAssemblyModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry GeneralStackGeometry StackCycleGeometry StackAffineModules
open LiGenericSourceIndex
open MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
attribute [local instance] HasDerivedCategory.standard
open scoped TensorProduct ChangeOfRings

variable {k : Type} [Field k] (X : Stack (Spec (.of k)))
  (Frame : SourceChart X → Type 2)
  (gauge : ∀ C : SourceChart X, Frame C → LiGenericGaugeSourceModels.Source C)

abbrev IndexComplex := CochainComplex (LargeModules X Frame) ℤ
abbrev LiftComplex := CochainComplex (LargeLiftModules X Frame) ℤ
abbrev SmallLiftModules := PresheafOfModules.{0}
  ((includeLift X Frame).op ⋙ coefficientRings X Frame)
abbrev SmallLiftComplex := CochainComplex (SmallLiftModules X Frame) ℤ
abbrev ParentModules := PresheafOfModules.{2} (rings X ⋙ forget₂ CommRingCat RingCat)
abbrev ParentComplex := CochainComplex (ParentModules X) ℤ
abbrev SmallParentComplex := CochainComplex (ModulePresheaf X) ℤ

def smallFromParents : ModulePresheaf X ⥤ SmallLiftModules X Frame :=
  PresheafOfModules.pushforward₀ (includeLift X Frame ⋙ projection X Frame)
    (rings X ⋙ forget₂ CommRingCat RingCat)

def spreadParents : ParentModules X ⥤ LargeModules X Frame :=
  PresheafOfModules.pushforward₀ (projection X Frame)
    (rings X ⋙ forget₂ CommRingCat RingCat)

instance : (smallFromParents X Frame).Additive where
  map_add := by intros; rfl

instance : (spreadParents X Frame).Additive where
  map_add := by intros; rfl

def raiseParent (L : SmallParentComplex X) : ParentComplex X :=
  ((MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift.functor
    (rings X ⋙ forget₂ CommRingCat RingCat)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

instance : (restrictToLifts X Frame).Additive where
  map_add := by intros; rfl

instance : (parentRestriction X Frame).Additive where
  map_add := by intros; rfl

def raiseLocal (L : SmallLiftComplex X Frame) : LiftComplex X Frame :=
  ((MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift.functor
    ((includeLift X Frame).op ⋙ coefficientRings X Frame)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L

def evaluateNativeLocal (L : SmallLiftComplex X Frame) (C : SourceChart X) (h : Frame C) :
    CochainComplex (ModuleCat.{0} ((rings X).obj (op C.native))) ℤ :=
    (((PresheafOfModules.evaluation
      ((includeLift X Frame).op ⋙ coefficientRings X Frame)
      (op (show LiftIndex X Frame from .chart C h))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)

def evaluateLocal (L : SmallLiftComplex X Frame) (C : SourceChart X) (h : Frame C) :
    CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of C.ring)).inv.hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (evaluateNativeLocal X Frame L C h)

/-- The actual raw quotient of a fixed Li source and its native scaling differential. -/
def chartComplex (C : SourceChart X) (h : Frame C) :=
  LiGenericGaugeSourceModels.quotientComplex C (gauge C h)

def localArrow (C E : SourceChart X) (h : Frame C) (j : Frame E) (f : E.native ⟶ C.native) :
    (show LiftIndex X Frame from .chart E j) ⟶ (show LiftIndex X Frame from .chart C h) :=
  InducedCategory.homMk f

/-- The restriction is the actual presheaf arrow with its native Gamma-Spec scalar square. -/
def localRestriction (L : SmallLiftComplex X Frame) (C E : SourceChart X)
    (h : Frame C) (j : Frame E) (f : E.native ⟶ C.native) :
    evaluateLocal X Frame L C h ⟶
      (LiGenericSourceRefinementModels.restrictionComplex C E f).obj (evaluateLocal X Frame L E j) where
  f t := by
    let q := (localArrow X Frame C E h j f).op
    letI : Module C.ring ((evaluateNativeLocal X Frame L C h).X t) :=
      ((evaluateLocal X Frame L C h).X t).isModule
    letI : Module E.ring ((evaluateNativeLocal X Frame L E j).X t) :=
      ((evaluateLocal X Frame L E j).X t).isModule
    letI : Module ((rings X).obj (op C.native)) ((evaluateLocal X Frame L C h).X t) :=
      ((evaluateNativeLocal X Frame L C h).X t).isModule
    letI : Module ((rings X).obj (op E.native)) ((evaluateLocal X Frame L E j).X t) :=
      ((evaluateNativeLocal X Frame L E j).X t).isModule
    letI : Module C.ring ((evaluateLocal X Frame L E j).X t) :=
      (((LiGenericSourceRefinementModels.restrictionComplex C E f).obj
        (evaluateLocal X Frame L E j)).X t).isModule
    exact ModuleCat.ofHom (show (evaluateLocal X Frame L C h).X t →ₗ[C.ring]
      ((LiGenericSourceRefinementModels.restrictionComplex C E f).obj
        (evaluateLocal X Frame L E j)).X t from
      { toFun := fun x => (L.X t).map q x
        map_add' := fun x y => map_add ((L.X t).map q).hom x y
        map_smul' := by
          intro r x
          change (L.X t).map q
            ((show (rings X).obj (op C.native) from (Scheme.ΓSpecIso (.of C.ring)).inv.hom r) • x) =
            (show (rings X).obj (op E.native) from (Scheme.ΓSpecIso (.of E.ring)).inv.hom
              (LiGenericSourceRefinementModels.scalar C E f r)) • (L.X t).map q x
          rw [PresheafOfModules.map_smul]
          congr 1
          change f.hom.base.left.appTop.hom ((Scheme.ΓSpecIso (.of C.ring)).inv.hom r) =
            (Scheme.ΓSpecIso (.of E.ring)).inv.hom (LiGenericSourceRefinementModels.scalar C E f r)
          simp [LiGenericSourceRefinementModels.scalar]
          rfl })
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((L.d n m).naturality (localArrow X Frame C E h j f).op) x

/-- Local source and every actual overlap are part of ONE module-presheaf complex. -/
structure NativeSource where
  global : SmallParentComplex X
  complex : SmallLiftComplex X Frame
  localMap : ((smallFromParents X Frame).mapHomologicalComplex (ComplexShape.up ℤ)).obj global ⟶ complex
  [localQuasi : QuasiIso localMap]
  comparison : ∀ (C : SourceChart X) (h : Frame C),
    evaluateLocal X Frame complex C h ⟶ chartComplex X Frame gauge C h
  [quasi : ∀ C h, QuasiIso (comparison C h)]
  cover : ∀ p : AffinePoint X, IsNoetherian p.obj.base.left →
    LocallyOfFiniteType p.obj.base.hom →
      ∃ (C : SourceChart X) (h : Frame C) (f : C.native ⟶ p),
        Etale f.hom.base.left ∧ Function.Surjective f.hom.base.left
  refinement : ∀ (C E : SourceChart X) (h : Frame C) (j : Frame E)
    (f : E.native ⟶ C.native), Refinement X Frame C E f
  leftSource : ∀ (C E : SourceChart X) (h : Frame C) (j : Frame E) (f : E.native ⟶ C.native),
    LiGenericSourceRefinementModels.SourceRefinement
      (C := C) (E := (refinement C E h j f).chart) (f := (refinement C E h j f).left)
      (gauge C h) (gauge (refinement C E h j f).chart (refinement C E h j f).qualification)
  rightSource : ∀ (C E : SourceChart X) (h : Frame C) (j : Frame E) (f : E.native ⟶ C.native),
    LiGenericSourceRefinementModels.SourceRefinement
      (C := E) (E := (refinement C E h j f).chart) (f := (refinement C E h j f).right)
      (gauge E j) (gauge (refinement C E h j f).chart (refinement C E h j f).qualification)
  left : ∀ (C E : SourceChart X) (h : Frame C) (j : Frame E) (f : E.native ⟶ C.native),
    Homotopy
      (comparison C h ≫ LiGenericSourceRefinementModels.quotientMap (gauge C h)
        (gauge (refinement C E h j f).chart (refinement C E h j f).qualification) (leftSource C E h j f))
      (localRestriction X Frame complex C (refinement C E h j f).chart h
        (refinement C E h j f).qualification (refinement C E h j f).left ≫
        (LiGenericSourceRefinementModels.restrictionComplex C (refinement C E h j f).chart
          (refinement C E h j f).left).map
            (comparison (refinement C E h j f).chart (refinement C E h j f).qualification))
  right : ∀ (C E : SourceChart X) (h : Frame C) (j : Frame E) (f : E.native ⟶ C.native),
    Homotopy
      (comparison E j ≫ LiGenericSourceRefinementModels.quotientMap (gauge E j)
        (gauge (refinement C E h j f).chart (refinement C E h j f).qualification) (rightSource C E h j f))
      (localRestriction X Frame complex E (refinement C E h j f).chart j
        (refinement C E h j f).qualification (refinement C E h j f).right ≫
        (LiGenericSourceRefinementModels.restrictionComplex E (refinement C E h j f).chart
          (refinement C E h j f).right).map
            (comparison (refinement C E h j f).chart (refinement C E h j f).qualification))
attribute [instance] NativeSource.quasi NativeSource.localQuasi

/-- The native right Kan functor is characterized by the full restriction adjunction. -/
structure RightKan where
  functor : LargeLiftModules X Frame ⥤ LargeModules X Frame
  adjunction : restrictToLifts X Frame ⊣ functor
  [additive : functor.Additive]
attribute [instance] RightKan.additive

def RightKan.complex (K : RightKan X Frame) : LiftComplex X Frame ⥤ IndexComplex X Frame :=
  K.functor.mapHomologicalComplex (ComplexShape.up ℤ)

def restrictComplex : IndexComplex X Frame ⥤ LiftComplex X Frame :=
  (restrictToLifts X Frame).mapHomologicalComplex (ComplexShape.up ℤ)

/-- One native counit map on the complete coefficient/cochain diagram. -/
def RightKan.counit (K : RightKan X Frame) (I : LiftComplex X Frame) :
    (restrictComplex X Frame).obj (K.complex.obj I) ⟶ I where
  f j := K.adjunction.counit.app (I.X j)
  comm' i j _ := (K.adjunction.counit.naturality (I.d i j)).symm

def RightKan.unit (K : RightKan X Frame) (I : IndexComplex X Frame) :
    I ⟶ K.complex.obj ((restrictComplex X Frame).obj I) where
  f j := K.adjunction.unit.app (I.X j)
  comm' i j _ := (K.adjunction.unit.naturality (I.d i j)).symm

def spreadComplex (L : ParentComplex X) : IndexComplex X Frame :=
  ((spreadParents X Frame).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

def assemblyMap (N : NativeSource X Frame gauge) (K : RightKan X Frame)
    (I : LiftComplex X Frame) (q : raiseLocal X Frame N.complex ⟶ I) :
    spreadComplex X Frame (raiseParent X N.global) ⟶ K.complex.obj I :=
  RightKan.unit X Frame K (spreadComplex X Frame (raiseParent X N.global)) ≫
    K.complex.map
      (((MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift.functor
        ((includeLift X Frame).op ⋙ coefficientRings X Frame)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map N.localMap ≫ q)

def evaluateParent (L : ParentComplex X) (p : AffinePoint X) :
    CochainComplex (ModuleCat.{2} ((rings X).obj (op p))) ℤ :=
  ((PresheafOfModules.evaluation (rings X ⋙ forget₂ CommRingCat RingCat) (op p)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L

/-- Actual projective cofibrancy makes the displayed tensor the derived pullback. -/
def IsCofibrant {R : Type} [CommRing R] (L : CochainComplex (ModuleCat.{2} R) ℤ) : Prop :=
  ∀ (A B : CochainComplex (ModuleCat.{2} R) ℤ) (p : A ⟶ B),
    QuasiIso p → (∀ j, Function.Surjective ((p.f j).hom)) →
      ∀ f : L ⟶ B, ∃ g : L ⟶ A, g ≫ p = f

structure BaseChange (L : ParentComplex X) {p q : AffinePoint X} (f : p ⟶ q) where
  map : ((ModuleCat.extendScalars ((rings X).map f.op).hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (evaluateParent X L q) ⟶ evaluateParent X L p
  pure : ∀ j (r : (rings X).obj (op p)) (x : (evaluateParent X L q).X j),
    map.f j (r ⊗ₜ[(rings X).obj (op q), ((rings X).map f.op).hom] x) =
      r • (L.X j).map f.op x
  quasi : QuasiIso map

def parentComplex (K : RightKan X Frame) (I : LiftComplex X Frame) : ParentComplex X :=
  ((parentRestriction X Frame).mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.complex.obj I)

/-- The source, whole K-injective replacement and canonical Kan assembly are outputs. -/
structure Assembly where
  native : NativeSource X Frame gauge
  kan : RightKan X Frame
  replacement : LiftComplex X Frame
  resolution : raiseLocal X Frame native.complex ⟶ replacement
  [quasi : QuasiIso resolution]
  [injective : replacement.IsKInjective]
  [counit : QuasiIso (RightKan.counit X Frame kan replacement)]
  [globalQuasi : QuasiIso (assemblyMap X Frame gauge native kan replacement resolution)]
  parentModel : ParentComplex X
  parentResolution : parentModel ⟶ parentComplex X Frame kan replacement
  [parentQuasi : QuasiIso parentResolution]
  parentNormalization : raiseParent X native.global ⟶ parentModel
  [normalizationQuasi : QuasiIso parentNormalization]
  parent_square : parentNormalization ≫ parentResolution =
    ((parentRestriction X Frame).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (assemblyMap X Frame gauge native kan replacement resolution)
  cofibrant : ∀ p : AffinePoint X,
    IsCofibrant (evaluateParent X parentModel p)
  baseChange : ∀ {p q : AffinePoint X} (f : p ⟶ q),
    BaseChange X parentModel f
attribute [instance] Assembly.quasi Assembly.injective Assembly.counit Assembly.globalQuasi
  Assembly.parentQuasi Assembly.normalizationQuasi

def globalComplex (A : Assembly X Frame gauge) : IndexComplex X Frame :=
  A.kan.complex.obj A.replacement

def globalDerived (A : Assembly X Frame gauge) := DerivedCategory.Q.obj (globalComplex X Frame gauge A)

/-- ONE native roof identifies the whole local source, including every action and overlap. -/
def sourceIso (A : Assembly X Frame gauge) :
    DerivedCategory.Q.obj (raiseLocal X Frame A.native.complex) ≅
      DerivedCategory.Q.obj ((restrictComplex X Frame).obj (globalComplex X Frame gauge A)) :=
  asIso (DerivedCategory.Q.map A.resolution) ≪≫
    (asIso (DerivedCategory.Q.map (RightKan.counit X Frame A.kan A.replacement))).symm

end MathlibExt.AlgebraicGeometry.LiGenericSourceAssemblyModels
