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
# Operations on sheaves of modules over the continuous coefficient ring

For a topological ring `E`, sheaves of modules over the ring sheaf `E_X = C(-, E)` on the small
pro-étale site of `X` (`ContinuousAdicRingModules`) have direct image along a morphism of
schemes, through the ring map `E_X → f_* E_Y` given by precomposition with the projection of the
base change, and inverse image, Mathlib's left adjoint of direct image (when it exists). The unit
maps are Mathlib's `SheafOfModules.unitToPushforwardObjUnit` and its mate
`SheafOfModules.pullbackObjUnitToUnit`. Global sections, their right derived functors, derived
direct and inverse images (the latter for inverse images preserving finite limits) and
coefficient change along a continuous ring map are defined as well.

When inverse image preserves finite limits, it is exact and its derived unit is an isomorphism
(`pullbackNormalization`). Derived tensor products, constructibility, completion and the
six-functor formalism are not treated here.

References: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma
4.2.12 and section 6.8, https://arxiv.org/abs/1309.1198.
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

/-- Sheaves of modules over the continuous coefficient ring `E_X`. -/
abbrev ModuleSheaf (X : Scheme) := CoefficientModules E X

/-- `E_X` as a module over itself. -/
abbrev ringUnit (X : Scheme) : ModuleSheaf E X :=
  SheafOfModules.unit (coefficientRing E X)

/-- Bounded-below cochain complexes of `E_X`-modules. -/
abbrev Cochains (X : Scheme) := CochainComplex.Plus (ModuleSheaf E X)

/-- The bounded-below derived category of `E_X`-modules. -/
abbrev Derived (X : Scheme) := CoefficientDerived E X

/-- A sheaf of modules as a complex concentrated in degree zero. -/
def singleCochain {X : Scheme} (M : ModuleSheaf E X) : Cochains E X :=
  ⟨(CochainComplex.singleFunctor (ModuleSheaf E X) 0).obj M,
    ⟨0, inferInstance⟩⟩

/-- A sheaf of modules as an object of the derived category, in degree zero. -/
def single {X : Scheme} (M : ModuleSheaf E X) : Derived E X :=
  DerivedCategory.Plus.Q.obj (singleCochain E M)

/-- `E_X` in degree zero. -/
def derivedUnit (X : Scheme) : Derived E X := single E (ringUnit E X)

/-- The ring map `E_X → f_* E_Y`: precomposition with the first projection of the base change. -/
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

/-- Direct image of `E_Y`-modules, as `E_X`-modules. -/
abbrev pushforward {Y X : Scheme} (f : Y ⟶ X) :
    ModuleSheaf E Y ⥤ ModuleSheaf E X :=
  SheafOfModules.pushforward.{1} (coefficientPushforward E f)

instance pushforward_additive {Y X : Scheme} (f : Y ⟶ X) :
    (pushforward E f).Additive where
  map_add := rfl

/-- The map `E_X → f_* E_Y` of `E_X`-modules induced by the ring map. -/
def unitPushforward {Y X : Scheme} (f : Y ⟶ X) :
    ringUnit E X ⟶ (pushforward E f).obj (ringUnit E Y) :=
  SheafOfModules.unitToPushforwardObjUnit (coefficientPushforward E f)

/-- Inverse image: the left adjoint of direct image. -/
abbrev pullback {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    ModuleSheaf E X ⥤ ModuleSheaf E Y :=
  SheafOfModules.pullback.{1} (coefficientPushforward E f)

/-- The adjunction between inverse and direct image. -/
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

/-- `unitPullback` is the adjoint of `unitPushforward`. -/
theorem unitPullback_mate {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint] :
    (pullbackPushforwardAdjunction E f).homEquiv _ _
      (unitPullback E f) = unitPushforward E f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (coefficientPushforward E f)

/-- Global sections, as `E`-modules through the constant functions. -/
def sections (X : Scheme) : ModuleSheaf E X ⥤ ModuleCat.{1} E :=
  underlying E X ⋙ AdicDerivedContracts.sections E X

instance sections_additive (X : Scheme) : (sections E X).Additive :=
  inferInstanceAs ((underlying E X ⋙
    AdicDerivedContracts.sections E X).Additive)

/-- Derived global sections of bounded-below complexes of `E_X`-modules. -/
def derivedSections (X : Scheme) [EnoughInjectives (ModuleSheaf E X)] :
    Derived E X ⥤ DerivedCategory.Plus (ModuleCat.{1} E) :=
  (sections E X).rightDerivedFunctorPlus

/-- Derived direct image. -/
def derivedPushforward {Y X : Scheme} (f : Y ⟶ X)
    [EnoughInjectives (ModuleSheaf E Y)] :
    Derived E Y ⥤ Derived E X :=
  (pushforward E f).rightDerivedFunctorPlus

/-- Derived inverse image, for an inverse image preserving finite limits (hence exact). -/
def derivedPullback {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (pullback E f)]
    [EnoughInjectives (ModuleSheaf E X)] :
    Derived E X ⥤ Derived E Y :=
  (pullback E f).rightDerivedFunctorPlus

/-- The `n`-th cohomology of a complex: homology of its derived global sections. -/
def cohomologyObject (X : Scheme) [EnoughInjectives (ModuleSheaf E X)]
    (K : Derived E X) (n : ℤ) : ModuleCat.{1} E :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} E) n).obj
    ((derivedSections E X).obj K)

/-- The map on cohomology induced by a map in the derived category. -/
def cohomologyMap (X : Scheme) [EnoughInjectives (ModuleSheaf E X)]
    {K L : Derived E X} (f : K ⟶ L) (n : ℤ) :
    cohomologyObject E X K n ⟶ cohomologyObject E X L n :=
  (derivedSections E X ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} E) n).map f

/-- The derived unit of inverse image along `f` is an isomorphism on every complex: the derived
inverse image is computed degreewise. It holds whenever inverse image preserves finite limits
(`pullbackNormalization`). -/
class PullbackNormalization {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (pullback E f)]
    [EnoughInjectives (ModuleSheaf E X)] : Prop where
  unitIsIso : ∀ K : Cochains E X, IsIso
    ((pullback E f).rightDerivedFunctorPlusUnit.app K)

attribute [instance] PullbackNormalization.unitIsIso

/-- An exact inverse image preserves quasi-isomorphisms, so its derived unit is an isomorphism. -/
instance pullbackNormalization {Y X : Scheme} (f : Y ⟶ X)
    [(pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (pullback E f)]
    [EnoughInjectives (ModuleSheaf E X)] : PullbackNormalization E f where
  unitIsIso K := by
    have hF : (CochainComplex.Plus.quasiIso (ModuleSheaf E X)).IsInvertedBy
        ((pullback E f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
      intro K L φ hφ
      rw [CochainComplex.Plus.quasiIso_iff] at hφ
      refine Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) _ ?_
      rw [CochainComplex.Plus.quasiIso_iff]
      change QuasiIso (((pullback E f).mapHomologicalComplex _).map φ.hom)
      infer_instance
    have := Functor.isIso_of_isRightDerivedFunctor_of_inverts _
      (pullback E f).rightDerivedFunctorPlusUnit hF
    infer_instance

variable (F : Type) [CommRing F] [TopologicalSpace F]
  [IsTopologicalRing F]

/-- The ring map `C(-, E) → C(-, F)` induced by a continuous ring map `E → F`. -/
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

/-- Restriction of scalars along `coefficientMap`. -/
abbrev coefficientRestriction (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme) : ModuleSheaf F X ⥤ ModuleSheaf E X :=
  SheafOfModules.pushforward.{1} (F := 𝟭 X.ProEt)
    (coefficientMap E F α continuousα X)

instance coefficientRestriction_additive (α : E →+* F)
    (continuousα : Continuous α) (X : Scheme) :
    (coefficientRestriction E F α continuousα X).Additive where
  map_add := rfl

/-- Extension of scalars: the left adjoint of restriction of scalars, when it exists. -/
abbrev coefficientExtension (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme)
    [(coefficientRestriction E F α continuousα X).IsRightAdjoint] :
    ModuleSheaf E X ⥤ ModuleSheaf F X :=
  SheafOfModules.pullback.{1} (F := 𝟭 X.ProEt)
    (coefficientMap E F α continuousα X)

/-- The adjunction between extension and restriction of scalars. -/
def coefficientAdjunction (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme)
    [(coefficientRestriction E F α continuousα X).IsRightAdjoint] :
    coefficientExtension E F α continuousα X ⊣
      coefficientRestriction E F α continuousα X :=
  Adjunction.ofIsRightAdjoint (coefficientRestriction E F α continuousα X)

/-- The map `E_X → F_X` of `E_X`-modules induced by the coefficient ring map. -/
def coefficientUnitMap (α : E →+* F) (continuousα : Continuous α)
    (X : Scheme) : ringUnit E X ⟶
      (coefficientRestriction E F α continuousα X).obj (ringUnit F X) :=
  SheafOfModules.unitToPushforwardObjUnit
    (F := 𝟭 X.ProEt)
    (S := coefficientRing E X) (R := coefficientRing F X)
    (coefficientMap E F α continuousα X)

end MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations
