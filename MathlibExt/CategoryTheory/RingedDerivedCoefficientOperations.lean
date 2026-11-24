/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Native ringed derived coefficient operations

The objects are Mathlib's sheaves of modules and bounded-below derived
categories. Pullback, pushforward and both ordinary adjunction maps are
the actual native operators of the specified ringed site morphism.

The derived adjunction source below fixes its unit on every cochain and
its counit on native injective cochains. It supplies no period comparison
isomorphism or higher de Rham output.

References: Scholze, arXiv:1205.3463v2, Sections 7--8; Mathlib sheaf-module
pullback and right-derived functors, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe v u

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}]

local instance commutativeRingSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{1} RingCat.{1}) :=
  hasSheafCompose_of_preservesLimitsOfSize J

/-- The native ring sheaf underlying a commutative ring sheaf. -/
def moduleRing (S : Sheaf J CommRingCat.{1}) : Sheaf J RingCat.{1} :=
  (sheafCompose J (forget₂ CommRingCat.{1} RingCat.{1})).obj S

abbrev Modules (S : Sheaf J CommRingCat.{1}) := SheafOfModules.{1} (moduleRing S)

variable (G : C ⥤ D) [G.IsContinuous J T]
  (S : Sheaf J CommRingCat.{1}) (R : Sheaf T CommRingCat.{1})
  (φ : S ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj R)

/-- The specified ringed-site map, retaining every original scalar component. -/
def moduleScalarMap : moduleRing S ⟶
    (G.sheafPushforwardContinuous RingCat.{1} J T).obj (moduleRing R) := by
  refine ObjectProperty.homMk { app := fun U =>
    (forget₂ CommRingCat.{1} RingCat.{1}).map (φ.hom.app U), naturality := ?_ }
  intro U V f
  ext x
  exact congrArg (fun g => g.hom x) (φ.hom.naturality f)

/-- Actual restriction and ringed pushforward of module sheaves. -/
abbrev pushforward : Modules R ⥤ Modules S :=
  SheafOfModules.pushforward (moduleScalarMap G S R φ)

instance pushforward_additive : (pushforward G S R φ).Additive where
  map_add := by intros; rfl

variable [(pushforward G S R φ).IsRightAdjoint]

/-- Actual inverse image and scalar extension, as the native left adjoint. -/
abbrev pullback : Modules S ⥤ Modules R :=
  SheafOfModules.pullback (moduleScalarMap G S R φ)

def adjunction : pullback G S R φ ⊣ pushforward G S R φ :=
  SheafOfModules.pullbackPushforwardAdjunction (moduleScalarMap G S R φ)

instance pullback_additive : (pullback G S R φ).Additive :=
  (adjunction G S R φ).left_adjoint_additive

variable [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]

abbrev Derived (S : Sheaf J CommRingCat.{1}) := DerivedCategory.Plus (Modules S)

def cohomology (S : Sheaf J CommRingCat.{1}) (A : Derived S) (i : ℤ) : Modules S :=
  (DerivedCategory.Plus.homologyFunctor (Modules S) i).obj A

variable [EnoughInjectives (Modules S)] [EnoughInjectives (Modules R)]

/-- Native derived pushforward, with the native cochain resolution unit. -/
def derivedPushforward : Derived R ⥤ Derived S :=
  (pushforward G S R φ).rightDerivedFunctorPlus

/-- Exactness source qualification on the original cochain inverse images. -/
class PullbackSourceUnit where
  unitIso : ∀ K : CochainComplex.Plus (Modules S),
    IsIso ((pullback G S R φ).rightDerivedFunctorPlusUnit.app K)

attribute [instance] PullbackSourceUnit.unitIso

/-- The derived inverse image of the exact source operator. It is the right-derived functor of the
pullback, which is the derived inverse image only because `PullbackSourceUnit` makes the pullback
exact on bounded-below complexes; without it the right-derived functor is not the inverse image
(for `ℤ → 𝔽_p` on a point it kills `ℤ/p`, whose derived tensor with `𝔽_p` is nonzero). -/
@[nolint unusedArguments]
def derivedPullback [PullbackSourceUnit G S R φ] : Derived S ⥤ Derived R :=
  (pullback G S R φ).rightDerivedFunctorPlus

variable [PullbackSourceUnit G S R φ]

instance pullbackUnitIsIso (K : CochainComplex.Plus (Modules S)) :
    IsIso ((pullback G S R φ).rightDerivedFunctorPlusUnit.app K) :=
  PullbackSourceUnit.unitIso K

def pullbackUnitInverse (K : CochainComplex.Plus (Modules S)) :
    (derivedPullback G S R φ).obj (DerivedCategory.Plus.Q.obj K) ⟶
      DerivedCategory.Plus.Q.obj ((pullback G S R φ).mapCochainComplexPlus.obj K) :=
  @inv _ _ _ _ ((pullback G S R φ).rightDerivedFunctorPlusUnit.app K)
    (PullbackSourceUnit.unitIso (G := G) (S := S) (R := R) (φ := φ) K)

/-- The derived adjunction is pinned to the original cochain unit and counit. -/
structure DerivedAdjunctionSource where
  adj : derivedPullback G S R φ ⊣ derivedPushforward G S R φ
  unit_source : ∀ K : CochainComplex.Plus (Modules S),
    adj.unit.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((adjunction G S R φ).unit.mapCochainComplexPlus.app K) ≫
      (pushforward G S R φ).rightDerivedFunctorPlusUnit.app
        ((pullback G S R φ).mapCochainComplexPlus.obj K) ≫
      (derivedPushforward G S R φ).map
        ((pullback G S R φ).rightDerivedFunctorPlusUnit.app K)
  counit_source : ∀ I : CochainComplex.Plus (InjectiveObject (Modules R)),
    let K := (InjectiveObject.ι (Modules R)).mapCochainComplexPlus.obj I
    adj.counit.app (DerivedCategory.Plus.Q.obj K) =
      (derivedPullback G S R φ).map
        (inv ((pushforward G S R φ).rightDerivedFunctorPlusUnit.app K)) ≫
      pullbackUnitInverse G S R φ ((pushforward G S R φ).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map
        ((adjunction G S R φ).counit.mapCochainComplexPlus.app K)

end MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
