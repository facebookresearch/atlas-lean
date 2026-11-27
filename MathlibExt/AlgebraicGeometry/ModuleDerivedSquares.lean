/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BirationalDualityReferences
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Fixed module-derived squares and duality base-change mates

All functors are FourierMukai's native Kan-derived module functors.
The adjunction and pullback-pasting adapters are normalized against the
actual ordinary cochain unit and pullbackComp; generic derived existence
and localization proofs are source integration, not new Wanted results.

The direct-image base-change arrow is computed as an adjunction mate.
The duality base-change arrow is then the transpose of the *fixed*
base-change inverse followed by the *fixed* duality trace and unit
pullback. Thus no canonical-complex or base-change arrow is a free oracle.

Sources: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/Duality/FiniteTwistedTrace.lean and the derived
base-change modules, Apache 2.0; Stacks Tags 08IB and 0A9Y.
The formal normalization pattern reuses Atlas AdicDerivedContracts
on the actual structure-module categories.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ModuleDerivedSquares

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}]

/-- The actual ordinary module adjunction unit on a cochain model. -/
def cochainUnit {X Y : Scheme.{0}} (f : X ⟶ Y) (K : Cochains Y) :
    K ⟶ (Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ) |>.obj
      ((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ) |>.obj K) where
  f j := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (K.X j)
  comm' i j hij := by
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (K.d i j)).symm

/-- The prescribed derived unit on cochains for which the actual pullback counit is invertible. -/
def normalizedUnit {X Y : Scheme.{0}} (f : X ⟶ Y) (K : Cochains Y)
    (h : IsIso ((derivedPullbackCounit f).app K)) :
    DerivedCategory.Q.obj K ⟶ (derivedPushforward f).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj K)) := by
  letI := h
  exact DerivedCategory.Q.map (cochainUnit f K) ≫
    (derivedPushforwardUnit f).app
      ((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ) |>.obj K) ≫
        (derivedPushforward f).map (inv ((derivedPullbackCounit f).app K))

/-- An adjunction $Lf^* \dashv Rf_*$ between the total derived pullback and direct image along a
morphism of schemes $f : X \to Y$ (assumed to exist: `HasDerivedPullbacks`,
`HasDerivedPushforwards`), whose unit is normalized by the ordinary unit: for every cochain complex
$K$ of $\mathcal{O}_Y$-modules such that the canonical map $Lf^*(QK) \to Q(f^*K)$ is an
isomorphism, the unit at $QK$ is `normalizedUnit f K h`, the composite of the localized termwise
unit $QK \to Q(f_*f^*K)$, the canonical map $Q(f_*f^*K) \to Rf_*(Q(f^*K))$ and $Rf_*$ of the
inverse of that isomorphism. Here $Q$ is the localization functor and $f^*$, $f_*$ act termwise. -/
structure PullPushAdjunction {X Y : Scheme.{0}} (f : X ⟶ Y) where
  adjunction : derivedPullback f ⊣ derivedPushforward f
  normalized : ∀ (K : Cochains Y) (h : IsIso ((derivedPullbackCounit f).app K)),
    adjunction.unit.app (DerivedCategory.Q.obj K) = normalizedUnit f K h

/-- The actual ordinary cochain comparison of composite scheme-module pullbacks. -/
def cochainPullbackComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Cochains Z) :
    ((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj K) ≅
        ((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj K :=
  (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp f g) (.up ℤ)).app K

/-- Composite derived counit to the fixed ordinary composite pullback source. -/
def compositeCounit {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (K : Cochains Z) :
    (derivedPullback f).obj ((derivedPullback g).obj (DerivedCategory.Q.obj K)) ⟶
      (pullbackSource (f ≫ g)).obj K :=
  (derivedPullback f).map ((derivedPullbackCounit g).app K) ≫
    (derivedPullbackCounit f).app
      ((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ) |>.obj K) ≫
        DerivedCategory.Q.map (cochainPullbackComp f g K).hom

/-- A natural isomorphism $Lf^* \circ Lg^* \cong L(g \circ f)^*$ of total derived pullbacks along
morphisms of schemes $f : X \to Y$ and $g : Y \to Z$ (assumed to exist), normalized on every
cochain complex $K$ of $\mathcal{O}_Z$-modules: its component at $QK$, followed by the canonical
map $L(g \circ f)^*(QK) \to Q((g \circ f)^*K)$, is `compositeCounit f g K`, the composite of
$Lf^*$ of the canonical map $Lg^*(QK) \to Q(g^*K)$, the canonical map
$Lf^*(Q(g^*K)) \to Q(f^*g^*K)$ and the localized termwise isomorphism $f^*g^* \cong (g \circ f)^*$.
Here $Q$ is the localization functor and $f^*$, $g^*$ act termwise. -/
structure PullbackPasting {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) where
  comparison : derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g)
  normalized : ∀ K : Cochains Z,
    comparison.hom.app (DerivedCategory.Q.obj K) ≫ (derivedPullbackCounit (f ≫ g)).app K =
      compositeCounit f g K

/-- The actual pullback square comparison from the two normalized pasting maps. -/
def pullbackSquare {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (A : PullbackPasting f' g) (B : PullbackPasting p f) :
    derivedPullback g ⋙ derivedPullback f' ≅ derivedPullback f ⋙ derivedPullback p :=
  A.comparison ≪≫ eqToIso (congrArg (derivedPullback) comm.symm) ≪≫ B.comparison.symm

/-- Canonical direct-image base change is computed as the actual adjunction mate. -/
def baseChangeMap {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (AF : PullPushAdjunction f)
    (AF' : PullPushAdjunction f') (A : PullbackPasting f' g) (B : PullbackPasting p f)
    (K : D X) :
    (derivedPullback g).obj ((derivedPushforward f).obj K) ⟶
      (derivedPushforward f').obj ((derivedPullback p).obj K) :=
  AF'.adjunction.unit.app _ ≫
    (derivedPushforward f').map ((pullbackSquare p f' f g comm A B).hom.app
      ((derivedPushforward f).obj K)) ≫
        (derivedPushforward f').map ((derivedPullback p).map (AF.adjunction.counit.app K))

/-- A structure-unit pullback comparison pinned to the actual ordinary unit isomorphism. -/
structure UnitPullback {X Y : Scheme.{0}} (f : X ⟶ Y) where
  comparison : (derivedPullback f).obj (derivedUnit Y) ≅ derivedUnit X
  normalized : comparison.hom =
    (derivedPullbackCounit f).app
      ((CochainComplex.singleFunctor Y.Modules 0).obj (structureModule Y)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pullback f) (.up ℤ) 0).hom.app (structureModule Y)) ≫
        DerivedCategory.Q.map
          ((CochainComplex.singleFunctor X.Modules 0).map
            (MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison.pullbackStructureIso f).hom)

/-- Dualizing base change is the transpose of the fixed proper-base-change square and trace.
All geometric invertibility assumptions remain explicit input; the arrow is computed. -/
def dualityBaseChange {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (AF : PullPushAdjunction f)
    (AF' : PullPushAdjunction f') (A : PullbackPasting f' g) (B : PullbackPasting p f)
    (U : UnitPullback g)
    [(derivedPushforward f).IsLeftAdjoint] [(derivedPushforward f').IsLeftAdjoint]
    (h : IsIso (baseChangeMap p f' f g comm AF AF' A B (relativeDuality f))) :
    (derivedPullback p).obj (relativeDuality f) ⟶ relativeDuality f' := by
  letI := h
  exact ((Adjunction.ofIsLeftAdjoint (derivedPushforward f')).homEquiv _ _)
    (inv (baseChangeMap p f' f g comm AF AF' A B (relativeDuality f)) ≫
      (derivedPullback g).map (trace f) ≫ U.comparison.hom)


/-- The actual ordinary pullback square is computed from native pullbackComp/Congr. -/
def ordinaryPullbackSquare {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p :=
  Scheme.Modules.pullbackComp f' g ≪≫
    Scheme.Modules.pullbackCongr comm.symm ≪≫ (Scheme.Modules.pullbackComp p f).symm

/-- Ordinary direct-image base change is the literal native adjunction mate. -/
def ordinaryBaseChangeMap {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app _ ≫
    (Scheme.Modules.pushforward f').map
      ((ordinaryPullbackSquare p f' f g comm).hom.app ((Scheme.Modules.pushforward f).obj M)) ≫
        (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M))

end MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
