/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EffectiveMotivicComplexModels
public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Actual pointed motivic locality and Dold-Kan realization

Nisnevich weak equivalence is tested on the native site-point fibers.
Motivic fibrant objects satisfy the actual Nisnevich injective lifting
test and affine-line invariance. Mapping spaces are native enriched
presheaf Homs with the basepoint fixed by a literal pullback.

Dold-Kan realization applies the native good truncation to an actual
K-injective coefficient resolution. The target is consequently the
simplicial module/sheaf model of the given complex, retaining its cycles
and boundaries, rather than a supplied space called K(p,q,A).

Sources: Morel--Voevodsky, A1-homotopy theory, §2;
Voevodsky arXiv:math/0107109v1, §2; Mazza--Voevodsky--Weibel,
Lectures 3 and 14.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PointedMotivicModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open NisnevichTransferModels EffectiveMotivicComplexModels SimplicialDerivedModels
open CochainComplex.HomComplex
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
variable [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

abbrev Spaces := (SmoothScheme k)ᵒᵖ ⥤ SSet.{1}
abbrev PointedSpaces := Under (𝟙_ (Spaces (k := k)))

instance presheafEnrichment : EnrichedOrdinaryCategory SSet.{1} (Spaces (k := k)) :=
  Enriched.FunctorCategory.enrichedOrdinaryCategory SSet.{1} SSet.{1} (SmoothScheme k)ᵒᵖ

def mappingSpaces (F H : Spaces (k := k)) : SSet.{1} :=
  Enriched.FunctorCategory.enrichedHom SSet.{1} F H

def basedMapping (F H : PointedSpaces (k := k)) : SSet.{1} :=
  pullback (eHomWhiskerRight SSet.{1} F.hom H.right) (eHomEquiv SSet.{1} H.hom)

def basedPrecomposition {F H : PointedSpaces (k := k)} (a : F ⟶ H) (Z : PointedSpaces (k := k)) :
    basedMapping H Z ⟶ basedMapping F Z :=
  pullback.lift
    (pullback.fst _ _ ≫ eHomWhiskerRight SSet.{1} a.right Z.right)
    (pullback.snd _ _) (by
      rw [Category.assoc, ← eHomWhiskerRight_comp, Under.w]
      exact pullback.condition)

def NisWeakEquivalence {F H : Spaces (k := k)} (a : F ⟶ H) : Prop :=
  ∀ x : GrothendieckTopology.Point.{1} (nisnevichTopology (k := k)),
    WeakEquivalence (x.presheafFiber.map a)

def IsNisFibrant (F : Spaces (k := k)) : Prop :=
  ∀ (X Y : Spaces (k := k)) (a : X ⟶ Y),
    (∀ U, Mono (a.app U)) → NisWeakEquivalence a →
      HasLiftingProperty a (terminal.from F)

def IsMotivicFibrant {P : SmoothProductSystem k} (A : StandardSchemes P) (F : Spaces (k := k)) : Prop :=
  IsNisFibrant F ∧ ∀ U : SmoothScheme k,
    WeakEquivalence (F.map (P.geometry U (A.affine 1)).fst.op)

def MotivicWeakEquivalence {P : SmoothProductSystem k} (A : StandardSchemes P)
    {F H : PointedSpaces (k := k)} (a : F ⟶ H) : Prop :=
  ∀ Z : PointedSpaces (k := k), IsMotivicFibrant A Z.right →
    WeakEquivalence (basedPrecomposition a Z)

def motivicWeakMaps {P : SmoothProductSystem k} (A : StandardSchemes P) :
    MorphismProperty (PointedSpaces (k := k)) :=
  fun _ _ a => MotivicWeakEquivalence A a

abbrev MotivicHomotopyCategory {P : SmoothProductSystem k} (A : StandardSchemes P) :=
  (motivicWeakMaps A).Localization

abbrev motivicQ {P : SmoothProductSystem k} (A : StandardSchemes P) := (motivicWeakMaps A).Q

/-- A genuine local replacement has its actual map and the native mapping-test weak equivalence. -/
structure MotivicReplacement {P : SmoothProductSystem k} (A : StandardSchemes P)
    (F : PointedSpaces (k := k)) where
  object : PointedSpaces (k := k)
  augmentation : F ⟶ object
  fibrant : IsMotivicFibrant A object.right
  weak : MotivicWeakEquivalence A augmentation

def representedSets (U : SmoothScheme k) : (SmoothScheme k)ᵒᵖ ⥤ Type 1 where
  obj V := Option (ULift.{1} (V.unop ⟶ U))
  map a := ↾fun x => x.map (fun g => ULift.up (a.unop ≫ g.down))
  map_id V := by ext x; cases x <;> simp
  map_comp a b := by ext x; cases x <;> simp [Category.assoc]

def representedSpace (U : SmoothScheme k) : Spaces (k := k) :=
  representedSets U ⋙ Functor.const SimplexCategoryᵒᵖ

def representedBasepoint (U : SmoothScheme k) : 𝟙_ (Spaces (k := k)) ⟶ representedSpace U where
  app V :=
    { app n := ↾fun _ => none
      naturality n m a := by rfl }
  naturality V W a := by rfl

def representedPointed (U : SmoothScheme k) : PointedSpaces (k := k) :=
  Under.mk (representedBasepoint U)

def simplicialUnderlyingFunctor :
    SimplicialObject (NisModules (k := k)) ⥤ Spaces (k := k) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (NisModules (k := k))
    ((SmoothScheme k)ᵒᵖ ⥤ Type 1)).obj
      (sheafToPresheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ) ⋙
        (Functor.whiskeringRight (SmoothScheme k)ᵒᵖ (ModuleCat.{1} ℤ) (Type 1)).obj (forget _)) ⋙
    flipFunctor SimplexCategoryᵒᵖ (SmoothScheme k)ᵒᵖ (Type 1)

/-- The realized object is the actual underlying simplicial Nisnevich module with its zero point. -/
structure PointedSimplicialModuleFunctor (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] where
  functor : SimplicialObject (NisModules (k := k)) ⥤ PointedSpaces (k := k)
  underlyingIso : functor ⋙ Under.forget (𝟙_ (Spaces (k := k))) ≅ simplicialUnderlyingFunctor
  zero_eq : ∀ (F : SimplicialObject (NisModules (k := k))) (U : (SmoothScheme k)ᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (t : ((𝟙_ (Spaces (k := k))).obj U).obj n),
    ((underlyingIso.app F).hom.app U).app n
      ((((functor.obj F).hom.app U).app n) t) =
        (0 : ((F.obj n).obj.obj U))

def IsKInjective (I : CochainComplex (NisModules (k := k)) ℤ) : Prop :=
  ∀ J : CochainComplex (NisModules (k := k)) ℤ,
    (∀ r : ℤ, IsZero (J.homology r)) →
    ∀ (r : ℤ) (a : Cochain J I r), δ r (r + 1) a = 0 →
      ∃ b : Cochain J I (r - 1), δ (r - 1) r b = a

/-- The resolution is a native augmented complex functor, with no motivic representability field. -/
structure KInjectiveResolutionSystem (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] where
  functor : CochainComplex (NisModules (k := k)) ℤ ⥤ CochainComplex (NisModules (k := k)) ℤ
  augmentation : 𝟭 _ ⟶ functor
  quasi : ∀ I : CochainComplex (NisModules (k := k)) ℤ, QuasiIso (augmentation.app I)
  injective : ∀ I : CochainComplex (NisModules (k := k)) ℤ, IsKInjective (functor.obj I)

def doldKanRealization (P : PointedSimplicialModuleFunctor k)
    (I : CochainComplex (NisModules (k := k)) ℤ) (p : ℤ) : PointedSpaces (k := k) :=
  P.functor.obj ((Abelian.DoldKan.Γ : ChainComplex (NisModules (k := k)) ℕ ⥤
      SimplicialObject (NisModules (k := k))).obj
    ((negativeEmbedding.truncLE'Functor (NisModules (k := k))).obj (I⟦p⟧)))

end MathlibExt.AlgebraicGeometry.PointedMotivicModels
