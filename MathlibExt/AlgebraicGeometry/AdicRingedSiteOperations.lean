/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Native operations on continuous coefficient ringed sites

The rings, module categories, maps, adjoints and derived functors are
fixed constructions. `E_X` is the actual continuous-function ring sheaf.
Direct image uses its actual pullback-of-functions ring morphism, and
inverse image is Mathlib's chosen left adjoint of that direct image.
The unit maps are the native ring-unit morphism and its adjunction mate.

Exact inverse-image and derived-presentation comparisons remain explicit
provider inputs. In particular, derived scalar extension needs its actual
exactness or K-flat comparison. Nonflat derived tensor products,
constructible preservation, completion and six-functor comparisons are
separate interfaces. No unrelated functor or cohomology carrier is
selected and named as a geometric operation.

References: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma
4.2.12 and section 6.8, https://arxiv.org/abs/1309.1198.
The native chosen adjoints and unit maps are Mathlib's
`SheafOfModules.pullback`, `pullbackPushforwardAdjunction`,
`unitToPushforwardObjUnit` and `pullbackObjUnitToUnit`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open ContinuousAdicRingModules
open ProEtaleCohomologyFunctoriality

attribute [local instance] HasDerivedCategory.standard

variable (E : Type) [CommRing E] [TopologicalSpace E]
  [IsTopologicalRing E]

/-- The actual module category over the continuous coefficient ring. -/
abbrev ModuleSheaf (X : Scheme) := CoefficientModules E X

/-- The actual native coefficient-ring unit. -/
abbrev ringUnit (X : Scheme) : ModuleSheaf E X :=
  SheafOfModules.unit (coefficientRing E X)

/-- The actual bounded-below cochain category. -/
abbrev Cochains (X : Scheme) := CochainComplex.Plus (ModuleSheaf E X)

/-- The actual bounded-below derived category. -/
abbrev Derived (X : Scheme) := CoefficientDerived E X

/-- A sheaf as its actual degree-zero bounded-below cochain complex. -/
def singleCochain {X : Scheme} (M : ModuleSheaf E X) : Cochains E X :=
  ⟨(CochainComplex.singleFunctor (ModuleSheaf E X) 0).obj M,
    ⟨0, inferInstance⟩⟩

/-- The actual derived single-object construction. -/
def single {X : Scheme} (M : ModuleSheaf E X) : Derived E X :=
  DerivedCategory.Plus.Q.obj (singleCochain E M)

/-- The specified derived continuous coefficient unit. -/
def derivedUnit (X : Scheme) : Derived E X := single E (ringUnit E X)

/-- The native continuous-ring direct-image map, by precomposition with
the first projection of the actual scheme base change. -/
def coefficientPushforward {Y X : Scheme} (f : Y ⟶ X) :
    coefficientRing E X ⟶
      ((baseChange f).sheafPushforwardContinuous RingCat.{1}
        (ProEt.topology X) (ProEt.topology Y)).obj (coefficientRing E Y) :=
  ObjectProperty.homMk
    { app U := RingCat.ofHom
        { toFun a := a.comp (Limits.pullback.fst U.unop.hom f).base.hom
          map_zero' := rfl
          map_one' := rfl
          map_add' _ _ := rfl
          map_mul' _ _ := rfl }
      naturality U V g := by
        apply RingCat.hom_ext
        apply RingHom.ext
        intro a
        let a' : C(U.unop.left, ULift.{1} E) := a
        change (a'.comp g.unop.left.base.hom).comp
            (Limits.pullback.fst V.unop.hom f).base.hom =
          (a'.comp (Limits.pullback.fst U.unop.hom f).base.hom).comp
            (((baseChange f).map g.unop).left).base.hom
        apply ContinuousMap.ext
        intro x
        change a' ((Limits.pullback.fst V.unop.hom f ≫
            g.unop.left).base.hom x) =
          a' ((((baseChange f).map g.unop).left ≫
            Limits.pullback.fst U.unop.hom f).base.hom x)
        have h : ((baseChange f).map g.unop).left ≫
            Limits.pullback.fst U.unop.hom f =
          Limits.pullback.fst V.unop.hom f ≫ g.unop.left :=
          Limits.pullback.lift_fst _ _ _
        exact congrArg (fun h : Limits.pullback V.unop.hom f ⟶
          U.unop.left ↦ a' (h.base.hom x)) h.symm }

/-- Actual direct image of modules over `E_X`. -/
abbrev pushforward {Y X : Scheme} (f : Y ⟶ X) :
    ModuleSheaf E Y ⥤ ModuleSheaf E X :=
  SheafOfModules.pushforward.{1} (coefficientPushforward E f)

instance pushforward_additive {Y X : Scheme} (f : Y ⟶ X) :
    (pushforward E f).Additive where
  map_add := rfl

/-- The actual unit-to-direct-image morphism supplied by the ring map. -/
def unitPushforward {Y X : Scheme} (f : Y ⟶ X) :
    ringUnit E X ⟶ (pushforward E f).obj (ringUnit E Y) :=
  SheafOfModules.unitToPushforwardObjUnit (coefficientPushforward E f)

/-- Native inverse image: the chosen left adjoint of actual direct image. -/
abbrev pullback {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    ModuleSheaf E X ⥤ ModuleSheaf E Y :=
  SheafOfModules.pullback.{1} (coefficientPushforward E f)

/-- The actual chosen module inverse/direct-image adjunction. -/
def pullbackPushforwardAdjunction {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    pullback E f ⊣ pushforward E f :=
  SheafOfModules.pullbackPushforwardAdjunction (coefficientPushforward E f)

instance pullback_additive {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] : (pullback E f).Additive :=
  (pullbackPushforwardAdjunction E f).left_adjoint_additive

instance pullback_finiteColimits {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    PreservesFiniteColimits (pullback E f) := by
  let := (pullbackPushforwardAdjunction E f).isLeftAdjoint
  infer_instance

/-- The unit comparison is the adjunction mate of `unitPushforward`. -/
def unitPullback {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    (pullback E f).obj (ringUnit E X) ⟶ ringUnit E Y :=
  SheafOfModules.pullbackObjUnitToUnit (coefficientPushforward E f)

/-- Fixed native normalization of the unit comparison. -/
theorem unitPullback_mate {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    (pullbackPushforwardAdjunction E f).homEquiv _ _
      (unitPullback E f) = unitPushforward E f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (coefficientPushforward E f)

/-- Actual global sections, with the specified constant `E` scalar action. -/
def sections (X : Scheme) : ModuleSheaf E X ⥤ ModuleCat.{1} E :=
  underlying E X ⋙ AdicDerivedContracts.sections E X

instance sections_additive (X : Scheme) : (sections E X).Additive :=
  inferInstanceAs ((underlying E X ⋙
    AdicDerivedContracts.sections E X).Additive)

/-- Actual right derived global sections on arbitrary bounded-below
complexes of modules over the continuous coefficient ring. -/
def derivedSections (X : Scheme) [EnoughInjectives (ModuleSheaf E X)] :
    Derived E X ⥤ DerivedCategory.Plus (ModuleCat.{1} E) :=
  (sections E X).rightDerivedFunctorPlus

/-- Actual right derived direct image. -/
def derivedPushforward {Y X : Scheme} (f : Y ⟶ X)
    [EnoughInjectives (ModuleSheaf E Y)] :
    Derived E Y ⥤ Derived E X :=
  (pushforward E f).rightDerivedFunctorPlus

/-- Actual derived inverse image in the exact inverse-image scope.
Finite-limit preservation is an explicit adapter condition. -/
def derivedPullback {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (pullback E f)]
    [EnoughInjectives (ModuleSheaf E X)] :
    Derived E X ⥤ Derived E Y :=
  (pullback E f).rightDerivedFunctorPlus

/-- The actual cohomology module of a specified derived coefficient object. -/
def cohomologyObject (X : Scheme) [EnoughInjectives (ModuleSheaf E X)]
    (K : Derived E X) (n : ℤ) : ModuleCat.{1} E :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} E) n).obj
    ((derivedSections E X).obj K)

/-- Every cohomology map is the image of the actual derived-object map. -/
def cohomologyMap (X : Scheme) [EnoughInjectives (ModuleSheaf E X)]
    {K L : Derived E X} (f : K ⟶ L) (n : ℤ) :
    cohomologyObject E X K n ⟶ cohomologyObject E X L n :=
  (derivedSections E X ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} E) n).map f

/-- Exact inverse-image realization is a named source-adapter input.
The compared functor and unit are the native ones, not selected data. -/
class PullbackNormalization {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (pullback E f)]
    [EnoughInjectives (ModuleSheaf E X)] : Prop where
  unitIsIso : ∀ K : Cochains E X, IsIso
    ((pullback E f).rightDerivedFunctorPlusUnit.app K)

variable (F : Type) [CommRing F] [TopologicalSpace F]
  [IsTopologicalRing F]

/-- Coefficient change is the literal continuous-function ring map. -/
def coefficientMap (α : E →+* F) (continuousα : Continuous α) (X : Scheme) :
    coefficientRing E X ⟶ coefficientRing F X :=
  ObjectProperty.homMk
    { app U := RingCat.ofHom
        { toFun a := ⟨fun x ↦ ULift.up (α (a x).down),
            continuous_uliftUp.comp (continuousα.comp
              (continuous_uliftDown.comp a.continuous))⟩
          map_zero' := by
            apply ContinuousMap.ext
            intro x
            exact congrArg ULift.up (map_zero α)
          map_one' := by
            apply ContinuousMap.ext
            intro x
            exact congrArg ULift.up (map_one α)
          map_add' a b := by
            apply ContinuousMap.ext
            intro x
            exact congrArg ULift.up (map_add α (a x).down (b x).down)
          map_mul' a b := by
            apply ContinuousMap.ext
            intro x
            exact congrArg ULift.up (map_mul α (a x).down (b x).down) }
      naturality U V f := by
        apply RingCat.hom_ext
        apply RingHom.ext
        intro a
        apply ContinuousMap.ext
        intro x
        rfl }

/-- Native scalar restriction on the same actual pro-etale site. -/
abbrev coefficientRestriction (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme) : ModuleSheaf F X ⥤ ModuleSheaf E X :=
  SheafOfModules.pushforward.{1} (F := 𝟭 X.ProEt)
    (coefficientMap E F α continuousα X)

instance coefficientRestriction_additive (α : E →+* F)
    (continuousα : Continuous α) (X : Scheme) :
    (coefficientRestriction E F α continuousα X).Additive where
  map_add := rfl

/-- Native scalar extension: the chosen left adjoint, when it exists. -/
abbrev coefficientExtension (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme)
    [(coefficientRestriction E F α continuousα X).IsRightAdjoint] :
    ModuleSheaf E X ⥤ ModuleSheaf F X :=
  SheafOfModules.pullback.{1} (F := 𝟭 X.ProEt)
    (coefficientMap E F α continuousα X)

/-- The actual scalar extension/restriction adjunction. -/
def coefficientAdjunction (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme)
    [(coefficientRestriction E F α continuousα X).IsRightAdjoint] :
    coefficientExtension E F α continuousα X ⊣
      coefficientRestriction E F α continuousα X :=
  Adjunction.ofIsRightAdjoint (coefficientRestriction E F α continuousα X)

/-- The coefficient-unit map is fixed by the actual coefficient ring map. -/
def coefficientUnitMap (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme) : ringUnit E X ⟶
      (coefficientRestriction E F α continuousα X).obj (ringUnit F X) :=
  SheafOfModules.unitToPushforwardObjUnit
    (F := 𝟭 X.ProEt)
    (S := coefficientRing E X) (R := coefficientRing F X)
    (coefficientMap E F α continuousα X)

end MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations
