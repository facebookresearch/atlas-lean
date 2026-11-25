/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Derived compact supports for modules over the continuous coefficient ring

All categories are bounded-below derived categories of sheaves of modules over the continuous
coefficient ring `E_X` on small pro-étale sites. For an open immersion `j`, extension by zero is
the left adjoint of restriction (when it exists); when it is exact, its derived unit is an
isomorphism (`extensionNormalization`). For a compactification `c` of `f : X ⟶ S` (an open
immersion into a scheme proper over `S`), `compactifiedPushforward c` is derived extension by zero
followed by derived direct image, and `derivedRelativeCompactSections` its global sections; over
`Spec k` they give compactly supported cohomology. For a proper morphism `p`,
`properExceptionalPullback` is the right adjoint of `Rp_*` and `properTrace` its counit, under the
hypothesis that this right adjoint exists; properness alone is not shown to provide it.

The classes `OpenDerivedAdjunction`, `ImageDerivedAdjunction`, `RingedRefinementPasting`,
`SectionsPushforwardNormalization` and `SectionsDerivedNormalization` specify canonical comparisons
by their normalization on complexes or sections; `ModuleInjectives` and `RefinementExchange` state
the existence of enough injectives and open base change. Their constructions are tracked in
`WantedExt.AlgebraicGeometry.AdicDerivedCompactSupportsWanted`. `DerivedRefinementPasting` is
constructed (`derivedRefinementPasting`). `RefinementIsomorphism` is a hypothesis on a single
complex. Compactification independence, proper base change and the six-functor formalism are not
proved here.

References: Bhatt--Scholze, *The pro-etale topology for schemes*, §§6.1, 6.7, 6.8,
https://arxiv.org/abs/1309.1198; Stacks 0F7H, 0F7I and 09C9.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AdicRingedSiteOperations

attribute [local instance] HasDerivedCategory.standard

variable (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]

/-- For a topological commutative ring $E$, the category of sheaves of modules over the
continuous coefficient ring `E_X` on the small pro-étale site of a scheme $X$ has enough
injectives: an instance of this class asserts it for every scheme $X$. -/
class ModuleInjectives : Prop where
  enoughInjectives (X : Scheme) : EnoughInjectives (ModuleSheaf E X)

attribute [instance] ModuleInjectives.enoughInjectives

/-- A compactification of `f`: a factorization into a quasi-compact open immersion and a proper
morphism. -/
structure Compactification {X S : Scheme} (f : X ⟶ S) where
  ambient : Scheme
  openMap : X ⟶ ambient
  properMap : ambient ⟶ S
  factorization : openMap ≫ properMap = f
  [isOpen : IsOpenImmersion openMap]
  [quasiCompact : QuasiCompact openMap]
  [isProper : IsProper properMap]

attribute [instance] Compactification.isOpen Compactification.quasiCompact
  Compactification.isProper

/-- Identity compactification over the same scheme, for relative support. -/
def Compactification.identity (X : Scheme) : Compactification (𝟙 X) where
  ambient := X
  openMap := 𝟙 X
  properMap := 𝟙 X
  factorization := by simp
  isOpen := inferInstance
  quasiCompact := inferInstance
  isProper := inferInstance

/-- A proper base map turns the same open model into a compactification
over that new base. With target Spec k it yields an absolute model. -/
abbrev Compactification.overProperBase {X S T : Scheme} {f : X ⟶ S}
    (c : Compactification f) (g : S ⟶ T) [IsProper g] : Compactification (f ≫ g) where
  ambient := c.ambient
  openMap := c.openMap
  properMap := c.properMap ≫ g
  factorization := by rw [← Category.assoc, c.factorization]
  isOpen := c.isOpen
  quasiCompact := c.quasiCompact
  isProper := inferInstance

/-- A proper refinement is Cartesian over the original open scheme.
The Cartesian clause excludes additional components over that open. -/
structure Refinement {X S : Scheme} {f : X ⟶ S}
    (c d : Compactification f) where
  map : d.ambient ⟶ c.ambient
  [isProper : IsProper map]
  open_square : d.openMap ≫ map = c.openMap
  base_square : map ≫ c.properMap = d.properMap
  cartesian : IsPullback d.openMap (𝟙 X) map c.openMap

attribute [instance] Refinement.isProper

/-- Cohomology of a complex: morphisms from the unit `E_X` to its shifts. -/
abbrev UnitCohomology (X : Scheme) (K : Derived E X) (n : ℤ) :=
  derivedUnit E X ⟶ K⟦n⟧

/-- The map on cohomology induced by a morphism: postcomposition with its shifts. -/
def unitCohomologyMap {X : Scheme} {K L : Derived E X} (a : K ⟶ L) (n : ℤ) :
    UnitCohomology E X K n →+ UnitCohomology E X L n where
  toFun b := b ≫ a⟦n⟧'
  map_zero' := zero_comp
  map_add' b c := by simp only [Preadditive.add_comp]

@[simp]
theorem unitCohomologyMap_id {X : Scheme} (K : Derived E X) (n : ℤ) :
    unitCohomologyMap E (𝟙 K) n = AddMonoidHom.id _ := by
  ext b
  simp [unitCohomologyMap]

theorem unitCohomologyMap_comp {X : Scheme} {K L M : Derived E X}
    (a : K ⟶ L) (b : L ⟶ M) (n : ℤ) :
    unitCohomologyMap E (a ≫ b) n =
      (unitCohomologyMap E b n).comp (unitCohomologyMap E a n) := by
  ext c
  simp [unitCohomologyMap, Functor.map_comp, Category.assoc]

section Open

variable {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
  [(pushforward E j).IsRightAdjoint] [(pullback E j).IsRightAdjoint]

/-- Extension by zero along an open immersion: the left adjoint of restriction. -/
def extensionByZero {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    [(pushforward E j).IsRightAdjoint] [(pullback E j).IsRightAdjoint] :
    ModuleSheaf E X ⥤ ModuleSheaf E Y :=
  (pullback E j).leftAdjoint

/-- The adjunction between extension by zero and restriction. -/
def extensionAdjunction : extensionByZero E j ⊣ pullback E j :=
  Adjunction.ofIsRightAdjoint (pullback E j)

instance extension_additive : (extensionByZero E j).Additive :=
  (extensionAdjunction E j).left_adjoint_additive

instance extension_finiteColimits : PreservesFiniteColimits (extensionByZero E j) := by
  let := (extensionAdjunction E j).isLeftAdjoint
  infer_instance

variable [ModuleInjectives E]

/-- Derived extension by zero (for an exact extension by zero). -/
def derivedExtensionByZero [PreservesFiniteLimits (extensionByZero E j)] :
    Derived E X ⥤ Derived E Y :=
  (extensionByZero E j).rightDerivedFunctorPlus

variable [PreservesFiniteLimits (extensionByZero E j)]

/-- The derived unit of extension by zero is an isomorphism on every complex: extension by zero is
exact, so its derived functor is computed degreewise (`extensionNormalization`). -/
class ExtensionNormalization : Prop where
  unitIsIso (K : Cochains E X) :
    IsIso ((extensionByZero E j).rightDerivedFunctorPlusUnit.app K)

attribute [instance] ExtensionNormalization.unitIsIso

/-- An exact extension by zero preserves quasi-isomorphisms, so its derived unit is an
isomorphism. -/
instance extensionNormalization : ExtensionNormalization E j where
  unitIsIso K := by
    have hF : (CochainComplex.Plus.quasiIso (ModuleSheaf E X)).IsInvertedBy
        ((extensionByZero E j).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
      intro K L φ hφ
      rw [CochainComplex.Plus.quasiIso_iff] at hφ
      refine Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) _ ?_
      rw [CochainComplex.Plus.quasiIso_iff]
      change QuasiIso (((extensionByZero E j).mapHomologicalComplex _).map φ.hom)
      infer_instance
    have := Functor.isIso_of_isRightDerivedFunctor_of_inverts _
      (extensionByZero E j).rightDerivedFunctorPlusUnit hF
    infer_instance

variable [PreservesFiniteLimits (pullback E j)]

def extensionCochainUnit :
    𝟭 (Cochains E X) ⟶ (extensionByZero E j).mapCochainComplexPlus ⋙
      (pullback E j).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    (((extensionAdjunction E j).unit.mapHomologicalComplex (.up ℤ)).app K.obj)
  naturality K L a := by
    apply ObjectProperty.hom_ext
    exact ((extensionAdjunction E j).unit.mapHomologicalComplex (.up ℤ)).naturality a.hom

/-- The expected unit of the derived adjunction on a complex. -/
def normalizedExtensionUnit (K : Cochains E X) :
    DerivedCategory.Plus.Q.obj K ⟶
      (derivedPullback E j).obj
        ((derivedExtensionByZero E j).obj (DerivedCategory.Plus.Q.obj K)) :=
  DerivedCategory.Plus.Q.map ((extensionCochainUnit E j).app K) ≫
    (pullback E j).rightDerivedFunctorPlusUnit.app
      ((extensionByZero E j).mapCochainComplexPlus.obj K) ≫
    (derivedPullback E j).map
      ((extensionByZero E j).rightDerivedFunctorPlusUnit.app K)

/-- For an open immersion $j$ along which restriction (inverse image) and extension by zero (its
left adjoint) exist and are exact, with enough injectives (`ModuleInjectives`): an adjunction
between derived extension by zero and derived restriction along $j$ whose unit, on every
bounded-below complex, is the expected unit `normalizedExtensionUnit` (the underived unit
applied degreewise, followed by the units of the derived functors). -/
class OpenDerivedAdjunction where
  adjunction : derivedExtensionByZero E j ⊣ derivedPullback E j
  unit_normalization : ∀ K : Cochains E X,
    adjunction.unit.app (DerivedCategory.Plus.Q.obj K) = normalizedExtensionUnit E j K

end Open

section CompactSupport

variable {X S : Scheme} {f : X ⟶ S} (c : Compactification f)
  [(pushforward E c.openMap).IsRightAdjoint]
  [(pullback E c.openMap).IsRightAdjoint]
  [ModuleInjectives E] [PreservesFiniteLimits (extensionByZero E c.openMap)]

/-- Relative compactified direct image, with no chosen f_! field. -/
def compactifiedPushforward : Derived E X ⥤ Derived E S :=
  derivedExtensionByZero E c.openMap ⋙ derivedPushforward E c.properMap

/-- Global sections with proper support relative to the displayed base:
RΓ of the ambient extension by zero. An arbitrary scheme base is not an
absolute compact-support interpretation. -/
def derivedRelativeCompactSections : Derived E X ⥤ DerivedCategory.Plus (ModuleCat.{1} E) :=
  derivedExtensionByZero E c.openMap ⋙ derivedSections E c.ambient

/-- Cohomology with proper support relative to the base: homology of the derived global sections
of the derived extension by zero. -/
def relativeCompactCohomology (K : Derived E X) (n : ℤ) : ModuleCat.{1} E :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} E) n).obj
    ((derivedRelativeCompactSections E c).obj K)

abbrev relativeCompactUnitCohomology (K : Derived E X) (n : ℤ) :=
  UnitCohomology E c.ambient ((derivedExtensionByZero E c.openMap).obj K) n

/-- The extraordinary inverse image: the right adjoint of the compactified direct image, when it
exists. -/
def compactifiedExceptionalPullback [(compactifiedPushforward E c).IsLeftAdjoint] :
    Derived E S ⥤ Derived E X := (compactifiedPushforward E c).rightAdjoint

def compactifiedAdjunction [(compactifiedPushforward E c).IsLeftAdjoint] :
    compactifiedPushforward E c ⊣ compactifiedExceptionalPullback E c :=
  Adjunction.ofIsLeftAdjoint (compactifiedPushforward E c)

/-- The compactification trace is exactly the counit, not a supplied map. -/
def compactificationTrace [(compactifiedPushforward E c).IsLeftAdjoint] :
    compactifiedExceptionalPullback E c ⋙ compactifiedPushforward E c ⟶ 𝟭 (Derived E S) :=
  (compactifiedAdjunction E c).counit

end CompactSupport

section AbsoluteSupport

variable {k : Type} [Field k] {X : Scheme} {f : X ⟶ Spec (.of k)}
  (c : Compactification f) [ModuleInjectives E]
  [(pushforward E c.openMap).IsRightAdjoint]
  [(pullback E c.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]

/-- Absolute RΓ_c for a structural map over a field, with proper ambient. -/
abbrev derivedCompactSections := derivedRelativeCompactSections E c

/-- Compactly supported cohomology, for a scheme over a field. -/
abbrev compactCohomology (K : Derived E X) (n : ℤ) := relativeCompactCohomology E c K n

/-- The unit-Ext form on that same absolute compactification. -/
abbrev compactUnitCohomology (K : Derived E X) (n : ℤ) := relativeCompactUnitCohomology E c K n

end AbsoluteSupport

/-- When the base is proper over a field, the relative and absolute ambient
global-section models coincide without a new cohomology map. -/
def relativeToAbsolute {k : Type} [Field k] {X S : Scheme} {f : X ⟶ S}
    (c : Compactification f) (g : S ⟶ Spec (.of k)) [IsProper g] [ModuleInjectives E]
    [(pushforward E c.openMap).IsRightAdjoint] [(pullback E c.openMap).IsRightAdjoint]
    [PreservesFiniteLimits (extensionByZero E c.openMap)] :
    derivedRelativeCompactSections E c ≅ derivedCompactSections E (c.overProperBase g) :=
  Iso.refl _

section ProperTrace

variable {X Y : Scheme} (p : X ⟶ Y)

/-- The extraordinary inverse image along a proper morphism: the right adjoint of derived direct
image, when it exists. -/
def properExceptionalPullback {X Y : Scheme} (p : X ⟶ Y) [IsProper p]
    [ModuleInjectives E] [(derivedPushforward E p).IsLeftAdjoint] :
    Derived E Y ⥤ Derived E X :=
  (derivedPushforward E p).rightAdjoint

variable [IsProper p] [ModuleInjectives E] [(derivedPushforward E p).IsLeftAdjoint]

def properAdjunction : derivedPushforward E p ⊣ properExceptionalPullback E p :=
  Adjunction.ofIsLeftAdjoint (derivedPushforward E p)

instance properExceptional_additive : (properExceptionalPullback E p).Additive := by
  let : (derivedPushforward E p).Additive := by
    change ((pushforward E p).rightDerivedFunctorPlus).Additive
    infer_instance
  exact (properAdjunction E p).right_adjoint_additive

/-- The trace: the counit of that adjunction. -/
def properTrace : properExceptionalPullback E p ⋙ derivedPushforward E p ⟶ 𝟭 (Derived E Y) :=
  (properAdjunction E p).counit

/-- The trace on cohomology. -/
def properTraceCohomology (K : Derived E Y) (n : ℤ) :
    UnitCohomology E Y
      ((derivedPushforward E p).obj ((properExceptionalPullback E p).obj K)) n →+
        UnitCohomology E Y K n :=
  unitCohomologyMap E ((properTrace E p).app K) n

/-- A triangle identity relating the trace and the unit. -/
theorem properTrace_unit (K : Derived E Y) :
    (properAdjunction E p).unit.app ((properExceptionalPullback E p).obj K) ≫
      (properExceptionalPullback E p).map ((properTrace E p).app K) =
        𝟙 ((properExceptionalPullback E p).obj K) :=
  (properAdjunction E p).right_triangle_components K

end ProperTrace

section ImageAdjunction

variable {X Y : Scheme} (f : X ⟶ Y) [(pushforward E f).IsRightAdjoint]
  [PreservesFiniteLimits (pullback E f)] [ModuleInjectives E]

def imageCochainUnit : 𝟭 (Cochains E Y) ⟶
    (pullback E f).mapCochainComplexPlus ⋙ (pushforward E f).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    (((pullbackPushforwardAdjunction E f).unit.mapHomologicalComplex (.up ℤ)).app K.obj)
  naturality K L a := by
    apply ObjectProperty.hom_ext
    exact ((pullbackPushforwardAdjunction E f).unit.mapHomologicalComplex
      (.up ℤ)).naturality a.hom

def normalizedImageUnit (K : Cochains E Y) : DerivedCategory.Plus.Q.obj K ⟶
    (derivedPushforward E f).obj ((derivedPullback E f).obj (DerivedCategory.Plus.Q.obj K)) :=
  DerivedCategory.Plus.Q.map ((imageCochainUnit E f).app K) ≫
    (pushforward E f).rightDerivedFunctorPlusUnit.app
      ((pullback E f).mapCochainComplexPlus.obj K) ≫
    (derivedPushforward E f).map ((pullback E f).rightDerivedFunctorPlusUnit.app K)

/-- For a morphism of schemes $f$ whose inverse image (the left adjoint of direct image) exists
and is exact, with enough injectives (`ModuleInjectives`): an adjunction between derived inverse
image and derived direct image along $f$ whose unit, on every bounded-below complex, is the
expected unit `normalizedImageUnit` (the underived unit applied degreewise, followed by the units
of the derived functors). -/
class ImageDerivedAdjunction where
  adjunction : derivedPullback E f ⊣ derivedPushforward E f
  unit_normalization : ∀ K : Cochains E Y,
    adjunction.unit.app (DerivedCategory.Plus.Q.obj K) = normalizedImageUnit E f K

end ImageAdjunction

section Refine

variable {X S : Scheme} {f : X ⟶ S} {c d : Compactification f} (r : Refinement c d)

/-- The pasting of base changes along the refinement. -/
def refinementSitePasting :
    ProEtaleCohomologyFunctoriality.baseChange r.map ⋙
      ProEtaleCohomologyFunctoriality.baseChange d.openMap ≅
        ProEtaleCohomologyFunctoriality.baseChange c.openMap :=
  AdicDerivedContracts.baseChangeComp d.openMap r.map ≪≫
    eqToIso (congrArg (fun g : X ⟶ c.ambient ↦
      ProEtaleCohomologyFunctoriality.baseChange g) r.open_square)

/-- For a refinement $r$ of a compactification $c$ of $f$ by another one $d$: an isomorphism from
the direct image along the open immersion of $d$ followed by the direct image along $r$ to the
direct image along the open immersion of $c$ which, on sections over every object of the
pro-étale site of the ambient scheme of $c$, is restriction along the inverse of the pasting of
base changes `refinementSitePasting`. -/
class RingedRefinementPasting where
  pushforwardIso : pushforward E d.openMap ⋙ pushforward E r.map ≅ pushforward E c.openMap
  sections_normalization : ∀ (M : ModuleSheaf E X) (U : c.ambient.ProEt)
      (s : ((pushforward E r.map).obj ((pushforward E d.openMap).obj M)).val.obj (op U)),
    ((pushforwardIso.hom.app M).val.app (op U)) s =
      M.val.map (((refinementSitePasting r).inv.app U).op) s

variable [(pushforward E c.openMap).IsRightAdjoint]
  [(pushforward E d.openMap).IsRightAdjoint] [(pushforward E r.map).IsRightAdjoint]
  [RingedRefinementPasting E r]

/-- Inverse-image pasting is the unique adjunction mate of the normalized
direct-image pasting, not another selected comparison. -/
def refinementPullbackPasting : pullback E r.map ⋙ pullback E d.openMap ≅ pullback E c.openMap :=
  (((pullbackPushforwardAdjunction E r.map).comp
    (pullbackPushforwardAdjunction E d.openMap)).ofNatIsoRight
      (RingedRefinementPasting.pushforwardIso (E := E) (r := r))).leftAdjointUniq
        (pullbackPushforwardAdjunction E c.openMap)

variable [ModuleInjectives E]
  [PreservesFiniteLimits (pullback E c.openMap)]
  [PreservesFiniteLimits (pullback E d.openMap)]
  [PreservesFiniteLimits (pullback E r.map)]

def refinementCochainPasting (K : Cochains E c.ambient) :
    (pullback E d.openMap).mapCochainComplexPlus.obj
      ((pullback E r.map).mapCochainComplexPlus.obj K) ≅
        (pullback E c.openMap).mapCochainComplexPlus.obj K :=
  (CochainComplex.Plus.fullyFaithfulι (ModuleSheaf E X)).preimageIso
    ((Functor.mapHomologicalComplexCompIso (refinementPullbackPasting E r) (.up ℤ)).app K.obj)

def refinementCompositeUnit (K : Cochains E c.ambient) :
    DerivedCategory.Plus.Q.obj
      ((pullback E d.openMap).mapCochainComplexPlus.obj
        ((pullback E r.map).mapCochainComplexPlus.obj K)) ⟶
      (derivedPullback E d.openMap).obj
        ((derivedPullback E r.map).obj (DerivedCategory.Plus.Q.obj K)) :=
  (pullback E d.openMap).rightDerivedFunctorPlusUnit.app
    ((pullback E r.map).mapCochainComplexPlus.obj K) ≫
      (derivedPullback E d.openMap).map ((pullback E r.map).rightDerivedFunctorPlusUnit.app K)

/-- An isomorphism between derived inverse images along the refinement, compatible on every complex
with the pasting of the underived inverse images. It always exists (`derivedRefinementPasting`). -/
class DerivedRefinementPasting where
  comparison : derivedPullback E r.map ⋙ derivedPullback E d.openMap ≅
    derivedPullback E c.openMap
  unit_normalization : ∀ K : Cochains E c.ambient,
    refinementCompositeUnit E r K ≫ comparison.hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map (refinementCochainPasting E r K).hom ≫
        (pullback E c.openMap).rightDerivedFunctorPlusUnit.app K

/-- `refinementCochainPasting` as a natural isomorphism. -/
def refinementCochainPastingIso :
    (pullback E r.map).mapCochainComplexPlus ⋙ (pullback E d.openMap).mapCochainComplexPlus ≅
      (pullback E c.openMap).mapCochainComplexPlus :=
  NatIso.ofComponents (refinementCochainPasting E r) (fun {K L} φ => by
    apply ObjectProperty.hom_ext
    exact (Functor.mapHomologicalComplexCompIso (refinementPullbackPasting E r)
      (.up ℤ)).hom.naturality φ.hom)

/-- The derived refinement pasting exists: the three inverse images are exact, so their derived
units are isomorphisms and the comparison descends through the localization from the pasting on
complexes. -/
noncomputable instance derivedRefinementPasting : DerivedRefinementPasting E r := by
  have : IsIso (pullback E r.map).rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  have : IsIso (pullback E d.openMap).rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  have : IsIso (pullback E c.openMap).rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  let ur := asIso (pullback E r.map).rightDerivedFunctorPlusUnit
  let ud := asIso (pullback E d.openMap).rightDerivedFunctorPlusUnit
  let uc := asIso (pullback E c.openMap).rightDerivedFunctorPlusUnit
  let e : DerivedCategory.Plus.Q ⋙ (derivedPullback E r.map ⋙ derivedPullback E d.openMap) ≅
      DerivedCategory.Plus.Q ⋙ derivedPullback E c.openMap :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ur.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ud.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (refinementCochainPastingIso E r) _ ≪≫ uc
  let W := Localization.whiskeringLeftFunctor' DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf E c.ambient)) (Derived E X)
  exact
    { comparison := W.preimageIso e
      unit_normalization := fun K => by
        have h : (W.preimageIso e).hom.app (DerivedCategory.Plus.Q.obj K) = e.hom.app K :=
          NatTrans.congr_app (W.map_preimage e.hom) K
        rw [h]
        simp only [e, ur, ud, uc, refinementCompositeUnit, Iso.trans_hom, Iso.symm_hom,
          NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
          Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
          Functor.associator_inv_app, asIso_hom, asIso_inv, Category.id_comp, Category.assoc]
        rw [← Functor.map_comp_assoc]
        simp [refinementCochainPastingIso, derivedPullback] }

variable [(pullback E c.openMap).IsRightAdjoint]
  [(pullback E d.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]
  [PreservesFiniteLimits (extensionByZero E d.openMap)]
  [OpenDerivedAdjunction E c.openMap] [OpenDerivedAdjunction E d.openMap]

/-- The open exchange map `j_{d!} K ⟶ r^* j_{c!} K`: the adjoint of the extension unit followed by
the inverse of the derived pasting. -/
def extensionRefinementMap (K : Derived E X) :
    (derivedExtensionByZero E d.openMap).obj K ⟶
      (derivedPullback E r.map).obj ((derivedExtensionByZero E c.openMap).obj K) :=
  ((OpenDerivedAdjunction.adjunction (E := E) (j := d.openMap)).homEquiv _ _).symm
    ((OpenDerivedAdjunction.adjunction (E := E) (j := c.openMap)).unit.app K ≫
      (derivedRefinementPasting E r).comparison.inv.app
        ((derivedExtensionByZero E c.openMap).obj K))

/-- For a refinement $r$ of a compactification $c$ of $f$ by another one $d$, with enough injectives
(`ModuleInjectives`), with inverse images along the open immersions of $c$ and $d$ and along $r$
that exist and are exact, with exact extensions by zero along both open immersions, and with the
given comparison data (`RingedRefinementPasting` for $r$ and `OpenDerivedAdjunction` along both
open immersions): the condition that the open exchange map `extensionRefinementMap`
$j_{d!} K ⟶ r^* j_{c!} K$ is an isomorphism for every object $K$ of the bounded-below derived
category of $X$. -/
class RefinementExchange : Prop where
  mapIsIso (K : Derived E X) : IsIso (extensionRefinementMap E r K)

attribute [instance] RefinementExchange.mapIsIso

variable [RefinementExchange E r] [ImageDerivedAdjunction E r.map]

/-- The proper-refinement comparison is the original direct-image unit
followed by the inverse of the open exchange map. -/
def refinementComparison (K : Derived E X) :
    (derivedExtensionByZero E c.openMap).obj K ⟶
      (derivedPushforward E r.map).obj ((derivedExtensionByZero E d.openMap).obj K) :=
  (ImageDerivedAdjunction.adjunction (E := E) (f := r.map)).unit.app
    ((derivedExtensionByZero E c.openMap).obj K) ≫
      (derivedPushforward E r.map).map (inv (extensionRefinementMap E r K))

/-- The refinement comparison is an isomorphism on the complex `K` (a hypothesis on a single
complex; no claim is made for all coefficient rings or all complexes). -/
class RefinementIsomorphism (K : Derived E X) : Prop where
  mapIsIso : IsIso (refinementComparison E r K)

attribute [instance] RefinementIsomorphism.mapIsIso

end Refine

section SectionsComparison

variable {X Y : Scheme} (p : X ⟶ Y) [ModuleInjectives E]

def baseChangeTerminalIso :
    (ProEtaleCohomologyFunctoriality.baseChange p).obj (⊤_ Y.ProEt) ≅ (⊤_ X.ProEt) :=
  (IsTerminal.isTerminalObj (ProEtaleCohomologyFunctoriality.baseChange p) _
    terminalIsTerminal).uniqueUpToIso terminalIsTerminal

/-- For a morphism of schemes $p : X ⟶ Y$, with enough injectives (`ModuleInjectives`): an
isomorphism from global sections on $Y$ of direct images along $p$ to global sections on $X$
which, on every module $M$, is the restriction map of $M$ along the canonical isomorphism from the
terminal object of the pro-étale site of $X$ to the base change of the terminal object of that of
$Y$ (`baseChangeTerminalIso`). -/
class SectionsPushforwardNormalization where
  ordinary : pushforward E p ⋙ sections E Y ≅ sections E X
  sections_normalization : ∀ (M : ModuleSheaf E X)
      (s : (sections E Y).obj ((pushforward E p).obj M)),
    (ordinary.hom.app M) s = M.val.map ((baseChangeTerminalIso p).inv.op) s

variable [SectionsPushforwardNormalization E p]

def derivedOrdinarySectionsComparison :
    (pushforward E p ⋙ sections E Y).rightDerivedFunctorPlus ≅ derivedSections E X where
  hom := (SectionsPushforwardNormalization.ordinary (E := E) (p := p)).hom.rightDerivedFunctorPlus
  inv := (SectionsPushforwardNormalization.ordinary (E := E) (p := p)).inv.rightDerivedFunctorPlus
  hom_inv_id := by
    rw [← NatTrans.rightDerivedFunctorPlus_comp, Iso.hom_inv_id]
    exact NatTrans.rightDerivedFunctorPlus_id _
  inv_hom_id := by
    rw [← NatTrans.rightDerivedFunctorPlus_comp, Iso.inv_hom_id]
    exact NatTrans.rightDerivedFunctorPlus_id _

def compositeSectionsUnit (K : Cochains E X) :
    DerivedCategory.Plus.Q.obj
      ((sections E Y).mapCochainComplexPlus.obj ((pushforward E p).mapCochainComplexPlus.obj K)) ⟶
        (derivedSections E Y).obj ((derivedPushforward E p).obj (DerivedCategory.Plus.Q.obj K)) :=
  (sections E Y).rightDerivedFunctorPlusUnit.app ((pushforward E p).mapCochainComplexPlus.obj K) ≫
    (derivedSections E Y).map ((pushforward E p).rightDerivedFunctorPlusUnit.app K)

/-- For a morphism of schemes $p : X ⟶ Y$, with enough injectives (`ModuleInjectives`) and a given
normalized comparison of global sections `SectionsPushforwardNormalization` for $p$: an
isomorphism from the right derived functor of direct image along $p$ followed by global sections
on $Y$ to derived direct image followed by derived global sections, compatible with the units: on
every bounded-below complex, the derived unit of the composite followed by this isomorphism is
`compositeSectionsUnit` (the derived unit of global sections, then derived global sections of
the derived unit of direct image). -/
class SectionsDerivedNormalization where
  comparison : (pushforward E p ⋙ sections E Y).rightDerivedFunctorPlus ≅
    derivedPushforward E p ⋙ derivedSections E Y
  unit_normalization : ∀ K : Cochains E X,
    (pushforward E p ⋙ sections E Y).rightDerivedFunctorPlusUnit.app K ≫
      comparison.hom.app (DerivedCategory.Plus.Q.obj K) = compositeSectionsUnit E p K

variable [SectionsDerivedNormalization E p]

/-- Derived global sections of a derived direct image are derived global sections, assembled from
`SectionsPushforwardNormalization` and `SectionsDerivedNormalization`. -/
def sectionsDirectImageComparison : derivedPushforward E p ⋙ derivedSections E Y ≅
    derivedSections E X :=
  (SectionsDerivedNormalization.comparison (E := E) (p := p)).symm ≪≫
    derivedOrdinarySectionsComparison E p

end SectionsComparison

section RelativeBaseSections

variable {X S : Scheme} {f : X ⟶ S} (c : Compactification f) [ModuleInjectives E]
  [(pushforward E c.openMap).IsRightAdjoint] [(pullback E c.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]
  [SectionsPushforwardNormalization E c.properMap] [SectionsDerivedNormalization E c.properMap]

/-- `RΓ(S, Rf_! K)` is the relative compactly supported cohomology, through the comparisons of
global sections along the proper morphism. -/
def relativeBaseSectionsComparison :
    compactifiedPushforward E c ⋙ derivedSections E S ≅ derivedRelativeCompactSections E c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedExtensionByZero E c.openMap)
      (sectionsDirectImageComparison E c.properMap)

end RelativeBaseSections

section CompactRefinement

variable {X S : Scheme} {f : X ⟶ S} {c d : Compactification f} (r : Refinement c d)
  [ModuleInjectives E]
  [(pushforward E c.openMap).IsRightAdjoint]
  [(pushforward E d.openMap).IsRightAdjoint] [(pushforward E r.map).IsRightAdjoint]
  [(pullback E c.openMap).IsRightAdjoint] [(pullback E d.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (pullback E c.openMap)]
  [PreservesFiniteLimits (pullback E d.openMap)]
  [PreservesFiniteLimits (pullback E r.map)]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]
  [PreservesFiniteLimits (extensionByZero E d.openMap)]
  [RingedRefinementPasting E r]
  [OpenDerivedAdjunction E c.openMap] [OpenDerivedAdjunction E d.openMap]
  [RefinementExchange E r] [ImageDerivedAdjunction E r.map]
  [SectionsPushforwardNormalization E r.map] [SectionsDerivedNormalization E r.map]

/-- The map between relative compactly supported cohomologies induced by a refinement: the unit
along the proper map, the inverse open exchange, and the comparisons of global sections. -/
def relativeRefinementMap (K : Derived E X) :
    (derivedRelativeCompactSections E c).obj K ⟶ (derivedRelativeCompactSections E d).obj K :=
  (derivedSections E c.ambient).map (refinementComparison E r K) ≫
    (sectionsDirectImageComparison E r.map).hom.app
      ((derivedExtensionByZero E d.openMap).obj K)

/-- The induced map on cohomology. -/
def relativeRefinementCohomologyMap (K : Derived E X) (n : ℤ) :
    relativeCompactCohomology E c K n ⟶ relativeCompactCohomology E d K n :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} E) n).map (relativeRefinementMap E r K)

instance relativeRefinementMap_isIso (K : Derived E X) [RefinementIsomorphism E r K] :
    IsIso (relativeRefinementMap E r K) := by
  dsimp only [relativeRefinementMap]
  infer_instance

instance relativeRefinementCohomologyMap_isIso (K : Derived E X)
    [RefinementIsomorphism E r K] (n : ℤ) :
    IsIso (relativeRefinementCohomologyMap E r K n) := by
  dsimp only [relativeRefinementCohomologyMap]
  infer_instance

end CompactRefinement

section TraceComparison

variable {X S : Scheme} {f : X ⟶ S} (c d : Compactification f) [ModuleInjectives E]
  [(pushforward E c.openMap).IsRightAdjoint] [(pushforward E d.openMap).IsRightAdjoint]
  [(pullback E c.openMap).IsRightAdjoint] [(pullback E d.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]
  [PreservesFiniteLimits (extensionByZero E d.openMap)]
  [(compactifiedPushforward E c).IsLeftAdjoint] [(compactifiedPushforward E d).IsLeftAdjoint]

/-- An isomorphism between compactified direct images induces a map between their right adjoints
(the mate). -/
def exceptionalComparison
    (comparison : compactifiedPushforward E c ≅ compactifiedPushforward E d) :
    compactifiedExceptionalPullback E d ⟶ compactifiedExceptionalPullback E c :=
  conjugateEquiv (compactifiedAdjunction E d) (compactifiedAdjunction E c) comparison.hom

/-- The traces are compatible with that mate. -/
theorem comparison_trace
    (comparison : compactifiedPushforward E c ≅ compactifiedPushforward E d) (K : Derived E S) :
    (compactifiedPushforward E c).map ((exceptionalComparison E c d comparison).app K) ≫
      (compactificationTrace E c).app K =
    comparison.hom.app ((compactifiedExceptionalPullback E d).obj K) ≫
      (compactificationTrace E d).app K :=
  conjugateEquiv_counit (compactifiedAdjunction E d)
    (compactifiedAdjunction E c) comparison.hom K

end TraceComparison

end MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports
