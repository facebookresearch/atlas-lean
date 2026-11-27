/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/LocallyQuasiCompact/ZariskiSite.lean` and
`StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/InverseImage.lean` (AxiomMath/Stacks,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: small pro-étale sites and continuous coefficient sheaves, with inverse and direct
image defined by adjunctions.

`Mathlib/CategoryTheory/Functor/Flat.lean` (Mathlib, revision
56a005855ea17e0b0958f73ec801ae140b0a1679), for the left Kan extension arguments:
Copyright (c) 2021 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang
Modifications: generalized to Kan extensions between categories in different universes.
-/

module

public import MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Pullback

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Functoriality of pro-étale cohomology with continuous coefficients

For a morphism of schemes `f : Y ⟶ X`, base change along `f` is a continuous, representably flat
functor between the small pro-étale sites, giving direct image `pushforward` and an exact inverse
image `pullback ⊣ pushforward` on sheaves of modules. Cohomology is `Ext` from the constant sheaf
`R`; `constantPullbackIso` identifies the inverse image of the constant sheaf, by uniqueness of
left adjoints of global sections. `cohomologyPullback` is the map on cohomology induced by
inverse image and a map of coefficient sheaves; for continuous coefficients `C(-, M)` the
coefficient map is the adjoint of precomposition with the projection
(`continuousCohomologyPullback`).
-/

namespace MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

universe u

instance weaklyEtaleComposition : MorphismProperty.IsStableUnderComposition
    (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- The small topology is the restriction of the big topology over X. -/
theorem topology_eq_restricted (X : Scheme.{u}) :
    ProEt.topology X = (ProEt.forget X).restrictedTopology (proetaleTopology.over X) :=
  MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
    proetalePrecoverage proetalePrecoverage_le_precoverage_weaklyEtale

/-- Base change along `f` on the small pro-étale sites (weakly étale maps are stable under base
change). -/
def baseChange {Y X : Scheme.{u}} (f : Y ⟶ X) : X.ProEt ⥤ Y.ProEt := by
  let : MorphismProperty.HasPullbacksAlong (@WeaklyEtale : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.pullback (@WeaklyEtale : MorphismProperty Scheme.{u}) ⊤ f

instance baseChangeFiniteLimits {Y X : Scheme.{u}} (f : Y ⟶ X) :
    PreservesFiniteLimits (baseChange f) := by
  have : PreservesFiniteLimits (baseChange f ⋙ ProEt.forget Y) :=
    inferInstanceAs (PreservesFiniteLimits (ProEt.forget X ⋙ Over.pullback f))
  exact ⟨fun _ _ _ ↦ preservesLimitsOfShape_of_reflects_of_preserves
    (baseChange f) (ProEt.forget Y)⟩

instance baseChangeFlat {Y X : Scheme.{u}} (f : Y ⟶ X) :
    RepresentablyFlat (baseChange f) := flat_of_preservesFiniteLimits _

instance baseChangeContinuous {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (baseChange f).IsContinuous (ProEt.topology X) (ProEt.topology Y) := by
  rw [topology_eq_restricted X, topology_eq_restricted Y,
    Functor.isContinuous_iff_coverPreserving]
  have h : CoverPreserving
      ((ProEt.forget X).restrictedTopology (proetaleTopology.over X))
      (proetaleTopology.over Y) (baseChange f ⋙ ProEt.forget Y) := by
    change CoverPreserving _ _ (ProEt.forget X ⋙ Over.pullback f)
    exact CoverPreserving.comp _ _ (Functor.coverPreserving_restrictedTopology _ _)
      (GrothendieckTopology.coverPreserving_overPullback proetaleTopology f)
  refine ⟨fun {W R} hR ↦ ?_⟩
  rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
  exact h.cover_preserve hR

section GenericKanExtension

universe s₁ s₂ s₃ x₁ x₂ x₃ t

/-- Pointwise colimit description, without identifying site universes. -/
def lanEvaluation {A : Type x₁} [Category.{s₁} A]
    {D : Type x₂} [Category.{s₂} D] (E : Type x₃) [Category.{s₃} E]
    (F : A ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G ↦ F.leftKanExtensionObjIsoColimit G X)
    (fun {G₁ G₂} φ ↦ by
      apply (F.isPointwiseLeftKanExtensionLeftKanExtensionUnit G₁ X).hom_ext
      intro T
      simp [Functor.lan])

/-- Left Kan extension along a representably flat functor preserves finite limits, for presheaves
valued in a concrete category whose forgetful functor preserves the relevant filtered
colimits. -/
theorem flatLanExact {C D E : Type*} [Category* C] [Category* D]
    [Category.{t} E] {FE : E → E → Type*} {CE : E → Type t}
    [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)] [ConcreteCategory.{t} E FE]
    [HasLimits E] [HasColimits E] [ReflectsLimits (forget E)]
    [PreservesLimits (forget E)] (F : C ⥤ D) [RepresentablyFlat F]
    (hPres : ∀ X : Dᵒᵖ,
      PreservesColimitsOfShape (CostructuredArrow F.op X) (forget E))
    [∀ X : Dᵒᵖ, Small.{t} (CostructuredArrow F.op X)]
    [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow F.op X) E] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ (Dᵒᵖ ⥤ E)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro X
  let : IsFiltered (CostructuredArrow F.op X) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F X.unop)
  let : PreservesColimitsOfShape (CostructuredArrow F.op X) (forget E) := hPres X
  have : PreservesLimitsOfShape J (colim : ((CostructuredArrow F.op X) ⥤ E) ⥤ E) :=
    inferInstance
  have : PreservesLimitsOfShape J
      ((Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F.op X) ⋙ colim) :=
    inferInstance
  exact preservesLimitsOfShape_of_natIso (lanEvaluation E F.op X).symm

end GenericKanExtension

variable (R : Type) [CommRing R]

instance moduleGrothendieck : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} R) := by
  let : HasLimits (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  let : AB5 (ModuleCat.{u + 1} R) :=
    { ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor
        (C := ModuleCat.{u + 1} R) (D := AddCommGrpCat.{u + 1}) J
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) }
  exact {}

instance sheafGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (CoefficientSheaf X R) := by
  let : HasLimits (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  let e := equivSmallModel.{u + 1} X.ProEt
  let : ∀ (Z : X.ProEtᵒᵖ),
      HasLimitsOfShape (StructuredArrow Z e.inverse.op) (ModuleCat.{u + 1} R) :=
    fun Z ↦ inferInstance
  let : HasSheafify (e.inverse.inducedTopology (ProEt.topology X))
      (ModuleCat.{u + 1} R) := by
    let : e.symm.inverse.IsDenseSubsite (ProEt.topology X)
        (e.inverse.inducedTopology (ProEt.topology X)) :=
      inferInstanceAs (e.functor.IsDenseSubsite (ProEt.topology X)
        (e.inverse.inducedTopology (ProEt.topology X)))
    exact e.symm.hasSheafify _ (ProEt.topology X) (ModuleCat.{u + 1} R)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (ProEt.topology X) (ModuleCat.{u + 1} R)

/-- Direct image: restriction along base change. -/
abbrev pushforward {Y X : Scheme.{u}} (f : Y ⟶ X) :
    CoefficientSheaf Y R ⥤ CoefficientSheaf X R :=
  (baseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    (ProEt.topology X) (ProEt.topology Y)

instance pushforwardAdditive {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (pushforward R f).Additive where
  map_add := rfl

/-- Inverse image: left Kan extension along base change, followed by sheafification. -/
abbrev pullback {Y X : Scheme.{u}} (f : Y ⟶ X) :
    CoefficientSheaf X R ⥤ CoefficientSheaf Y R :=
  Functor.sheafPullbackConstruction.sheafPullback (baseChange f)
    (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology Y)

def pullbackAdjunction {Y X : Scheme.{u}} (f : Y ⟶ X) :
    pullback R f ⊣ pushforward R f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

instance pullbackAdditive {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (pullback R f).Additive := (pullbackAdjunction R f).left_adjoint_additive

instance pullbackFiniteColimits {Y X : Scheme.{u}} (f : Y ⟶ X) :
    PreservesFiniteColimits (pullback R f) := by
  let := (pullbackAdjunction R f).isLeftAdjoint
  infer_instance

instance pullbackFiniteLimits {Y X : Scheme.{u}} (f : Y ⟶ X) :
    PreservesFiniteLimits (pullback R f) := by
  let : HasLimits (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  let : ReflectsLimits (forget (ModuleCat.{u + 1} R)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have h : PreservesFiniteLimits
      ((baseChange f).op.lan : (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R) ⥤
        (Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R)) := by
    refine flatLanExact (E := ModuleCat.{u + 1} R) (baseChange f) fun V ↦ ?_
    let : IsFiltered (CostructuredArrow (baseChange f).op V) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence (baseChange f) V.unop)
    let : PreservesColimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u, u + 1} R
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
    exact inferInstanceAs (PreservesColimitsOfShape
      (CostructuredArrow (baseChange f).op V)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
        forget AddCommGrpCat.{u + 1}))
  exact inferInstanceAs (PreservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafPullback (baseChange f)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology Y)))

/-- The constant sheaf `R`, which represents global sections. -/
abbrev constantUnit (X : Scheme.{u}) : CoefficientSheaf X R :=
  (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R (ULift.{u + 1} R))

/-- The inverse image of the constant sheaf is the constant sheaf: both are left adjoint to global
sections (at the terminal object and at its base change). -/
def constantPullbackIso {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (pullback R f).obj (constantUnit R X) ≅ constantUnit R Y := by
  let a := (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
    (terminalIsTerminal (C := X.ProEt))).comp (pullbackAdjunction R f)
  let b := constantSheafAdj (ProEt.topology Y) (ModuleCat.{u + 1} R)
    (IsTerminal.isTerminalObj (baseChange f) _ terminalIsTerminal)
  exact (a.leftAdjointUniq b).app (ModuleCat.of R (ULift.{u + 1} R))

/-- Cohomology of a sheaf of modules: `Ext` from the constant sheaf `R`, an `R`-module. -/
abbrev Cohomology (X : Scheme.{u}) (F : CoefficientSheaf X R) (n : ℕ) :=
  Abelian.Ext.{u + 1} (constantUnit R X) F n

/-- The map on cohomology induced by inverse image along `f` and a map of sheaves
`c : f⁻¹ F ⟶ G`. -/
def cohomologyPullback {Y X : Scheme.{u}} (f : Y ⟶ X)
    {F : CoefficientSheaf X R} {G : CoefficientSheaf Y R}
    (c : (pullback R f).obj F ⟶ G) (n : ℕ) :
    Cohomology R X F n →+ Cohomology R Y G n :=
  ((Abelian.Ext.mk₀ (constantPullbackIso R f).inv).precomp G (zero_add n)).comp
    (((Abelian.Ext.mk₀ c).postcomp _ (add_zero n)).comp
      ((pullback R f).mapExtAddHom _ _ n))

section ContinuousCoefficients

variable (M : Type (u + 1)) [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The map `C(-, M) → f_* C(-, M)` given on sections by precomposition with the first projection
of the base change. -/
def coefficientPushforward {Y X : Scheme.{u}} (f : Y ⟶ X) :
    continuousModuleSheaf R M X ⟶
      (pushforward R f).obj (continuousModuleSheaf R M Y) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun a := a.comp (Limits.pullback.fst U.unop.hom f).base.hom
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality U W g := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        let a' : C(U.unop.left, M) := a
        change (a'.comp g.unop.left.base.hom).comp
            (Limits.pullback.fst W.unop.hom f).base.hom =
          (a'.comp (Limits.pullback.fst U.unop.hom f).base.hom).comp
            (((baseChange f).map g.unop).left).base.hom
        apply ContinuousMap.ext
        intro x
        change a' ((Limits.pullback.fst W.unop.hom f ≫ g.unop.left).base.hom x) =
          a' ((((baseChange f).map g.unop).left ≫
            Limits.pullback.fst U.unop.hom f).base.hom x)
        have h : ((baseChange f).map g.unop).left ≫
            Limits.pullback.fst U.unop.hom f =
          Limits.pullback.fst W.unop.hom f ≫ g.unop.left :=
          Limits.pullback.lift_fst _ _ _
        exact congrArg (fun h : Limits.pullback W.unop.hom f ⟶ U.unop.left ↦
          a' (h.base.hom x)) h.symm }

/-- The map `f⁻¹ C(-, M) → C(-, M)`: the adjoint of `coefficientPushforward`. -/
def coefficientPullback {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (pullback R f).obj (continuousModuleSheaf R M X) ⟶
      continuousModuleSheaf R M Y :=
  ((pullbackAdjunction R f).homEquiv _ _).symm (coefficientPushforward R M f)

/-- The map on cohomology with coefficients `C(-, M)` induced by `f`. -/
def continuousCohomologyPullback {Y X : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    Cohomology R X (continuousModuleSheaf R M X) n →+
      Cohomology R Y (continuousModuleSheaf R M Y) n :=
  cohomologyPullback R f (coefficientPullback R M f) n

end ContinuousCoefficients

end MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
