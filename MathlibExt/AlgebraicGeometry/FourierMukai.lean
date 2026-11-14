/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks:
https://github.com/AxiomMath/Stacks
at commit c496df0d9beea9deaeabcea8492605f9a0a2313b:

Files in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/`:
* `Basic.lean`;
* `Composition.lean`.

These portions are licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0

Modification notice: reused Mathlib's module-sheaf and complex constructions,
used Mathlib Kan-extension constructors under explicit derived-existence
assumptions, and separated the unresolved existence and geometric comparison
proofs from these completed constructions. No Stacks dependency is added.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Localization.Prod

@[expose] public section

/-!
# Fourier–Mukai constructions for complexes of module sheaves

The ordinary pullback, pushforward and tensor sources below are fixed Mathlib
constructions on actual complexes of module sheaves. Given their genuine
left/right derived-existence assumptions, Mathlib's Kan-extension constructors
provide the operators, comparison transformations and universal properties.
The existence classes contain only those actual assumptions; no existence
instance is asserted in this proved module.

The tensor source forgets module sheaves to module presheaves, forms the total
cochain tensor with its Koszul differential, and sheafifies. It is derived
along the product of the two actual localization functors, deriving both
variables. All derived categories use `HasDerivedCategory.standard`.

The Fourier–Mukai functor and convolution have complete bodies under these
assumptions. Derived existence, quasi-coherent preservation, derived base
change and the projection formula are separate mathematical obligations.

## References

* The Stacks Project, Tags 06YJ (derived pullback), 06YU (derived tensor),
  0FYQ (Fourier–Mukai functor), 0FYS (composition), 08IB (derived base change),
  and 08EU (projection formula).
* AxiomMath/Stacks, the public source paths and revision in the notice above.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace MathlibExt.AlgebraicGeometry.FourierMukai

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The unbounded derived category of module sheaves on a scheme. -/
abbrev D (X : Scheme.{u}) := DerivedCategory X.Modules

/-- Actual cochain complexes of module sheaves. -/
abbrev Cochains (X : Scheme.{u}) := CochainComplex X.Modules ℤ

/-- The actual quasi-isomorphisms inverted by `DerivedCategory.Q`. -/
abbrev quasiIso (X : Scheme.{u}) : MorphismProperty (Cochains X) :=
  HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)

/-- Apply the actual module-sheaf pullback term by term, then localize. -/
def pullbackSource {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Cochains Y ⥤ D X :=
  (Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Apply the actual module-sheaf pushforward term by term, then localize. -/
def pushforwardSource {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Cochains X ⥤ D Y :=
  (Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- The fixed cochain tensor source: presheaf tensor totalization followed by
module sheafification and localization. -/
def tensorSource (X : Scheme.{u}) :
    (Cochains X × Cochains X) ⥤ D X :=
  let P := PresheafOfModulesOfCommRing.{u} X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  let A := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  letI : (curriedTensor P).PreservesZeroMorphisms := by
    constructor
    intro M N
    apply NatTrans.ext
    funext L
    exact Functor.map_zero (tensorRight L) M N
  (U.mapHomologicalComplex (ComplexShape.up ℤ)).prod
      (U.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
    Functor.uncurry.obj ((curriedTensor P).map₂CochainComplex) ⋙
    A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- Existence of the right Kan extensions defining derived pullback of the
fixed module-sheaf cochain sources. No existence instance is asserted here. -/
class HasDerivedPullbacks : Prop where
  /-- Every actual pullback source admits a left derived functor. -/
  hasLeftDerivedFunctor : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (pullbackSource f).HasLeftDerivedFunctor (quasiIso Y)

/-- Existence of the left Kan extensions defining unbounded derived direct
image of the fixed module-sheaf cochain sources. -/
class HasDerivedPushforwards : Prop where
  /-- Every actual pushforward source admits a right derived functor. -/
  hasRightDerivedFunctor : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (pushforwardSource f).HasRightDerivedFunctor (quasiIso X)

/-- Existence of derived tensor along the product of the two localizations,
with the total cochain tensor source fixed. -/
class HasDerivedTensors : Prop where
  /-- The right Kan extension along `Q × Q` exists. -/
  hasLeftDerivedFunctor : ∀ X : Scheme.{u},
    (tensorSource X).HasLeftDerivedFunctor ((quasiIso X).prod (quasiIso X))

attribute [instance] HasDerivedPullbacks.hasLeftDerivedFunctor
  HasDerivedPushforwards.hasRightDerivedFunctor HasDerivedTensors.hasLeftDerivedFunctor

variable [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}] [HasDerivedTensors.{u}]

/-- `Lf*`, chosen by the right Kan extension that defines a left derived
functor. Its source is `pullbackSource f`. -/
def derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : D Y ⥤ D X :=
  (pullbackSource f).totalLeftDerived DerivedCategory.Q (quasiIso Y)

/-- The canonical comparison `Lf*(Q M) ⟶ Q(f* M)`. -/
def derivedPullbackCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ derivedPullback f ⟶ pullbackSource f :=
  (pullbackSource f).totalLeftDerivedCounit DerivedCategory.Q (quasiIso Y)

/-- The constructed pullback has the genuine left-derived universal
property of its fixed cochain source. -/
instance derivedPullback_isLeftDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback f).IsLeftDerivedFunctor (derivedPullbackCounit f) (quasiIso Y) := by
  dsimp only [derivedPullback, derivedPullbackCounit]
  infer_instance

/-- `Rf*`, chosen by the left Kan extension that defines a right derived
functor. Its source is `pushforwardSource f`. -/
def derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    D X ⥤ D Y :=
  (pushforwardSource f).totalRightDerived DerivedCategory.Q (quasiIso X)

/-- The canonical comparison `Q(f_* M) ⟶ Rf_*(Q M)`. -/
def derivedPushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushforwardSource f ⟶ DerivedCategory.Q ⋙ derivedPushforward f :=
  (pushforwardSource f).totalRightDerivedUnit DerivedCategory.Q (quasiIso X)

/-- The constructed direct image has the genuine right-derived universal
property of its fixed cochain source. -/
instance derivedPushforward_isRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPushforward f).IsRightDerivedFunctor (derivedPushforwardUnit f) (quasiIso X) := by
  dsimp only [derivedPushforward, derivedPushforwardUnit]
  infer_instance

/-- The uncurried derived tensor, chosen as the genuine total left derived
functor of `tensorSource X` along `Q × Q`. -/
def derivedTensorUncurried (X : Scheme.{u}) :
    (D X × D X) ⥤ D X :=
  (tensorSource X).totalLeftDerived
    (DerivedCategory.Q.prod DerivedCategory.Q) ((quasiIso X).prod (quasiIso X))

/-- The canonical comparison from derived tensor of representatives to their
ordinary cochain tensor. -/
def derivedTensorCounit (X : Scheme.{u}) :
    (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ derivedTensorUncurried X ⟶
      tensorSource X :=
  (tensorSource X).totalLeftDerivedCounit
    (DerivedCategory.Q.prod DerivedCategory.Q) ((quasiIso X).prod (quasiIso X))

/-- The uncurried tensor derives both variables of its fixed cochain source. -/
instance derivedTensorUncurried_isLeftDerivedFunctor (X : Scheme.{u}) :
    (derivedTensorUncurried X).IsLeftDerivedFunctor (derivedTensorCounit X)
      ((quasiIso X).prod (quasiIso X)) := by
  dsimp only [derivedTensorUncurried, derivedTensorCounit]
  infer_instance

/-- The curried derived tensor, obtained from the same derived construction. -/
def derivedTensor (X : Scheme.{u}) : D X ⥤ D X ⥤ D X :=
  Functor.curry.obj (derivedTensorUncurried X)

/-- Complexes whose actual cohomology module sheaves are quasi-coherent. -/
def quasicoherent (X : Scheme.{u}) : ObjectProperty (D X) :=
  fun M => ∀ n : ℤ,
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules n).obj M)

/-- The full subcategory of complexes with quasi-coherent cohomology. -/
abbrev QCohDerived (X : Scheme.{u}) := (quasicoherent X).FullSubcategory

/-- `Φ_K = L pr₁* ⋙ (− ⊗ᴸ K) ⋙ R pr₂,*`, for an actual kernel on `X ×_S Y`.
Source: Stacks 0FYQ; AxiomMath/Stacks `FourierMukai/Basic.lean`. -/
def fourierMukai {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : D (pullback f g)) : D X ⥤ D Y :=
  derivedPullback (pullback.fst f g) ⋙
    ((derivedTensor (pullback f g)).flip.obj K) ⋙
    derivedPushforward (pullback.snd f g)

/-- The actual relative triple product `(X ×_S Y) ×_S Z`. -/
abbrev tripleProduct {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) :=
  pullback (pullback.fst f g ≫ f) h

/-- Projection from the relative triple product to `X ×_S Y`. -/
def pr12 {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    tripleProduct f g h ⟶ pullback f g :=
  pullback.fst (pullback.fst f g ≫ f) h

/-- Projection from the relative triple product to `X ×_S Z`. -/
def pr13 {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    tripleProduct f g h ⟶ pullback f h :=
  pullback.lift (pr12 f g h ≫ pullback.fst f g)
    (pullback.snd (pullback.fst f g ≫ f) h) (by
      rw [Category.assoc]
      exact pullback.condition)

/-- Projection from the relative triple product to `Y ×_S Z`. -/
def pr23 {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    tripleProduct f g h ⟶ pullback g h :=
  pullback.lift (pr12 f g h ≫ pullback.snd f g)
    (pullback.snd (pullback.fst f g ≫ f) h) (by
      rw [Category.assoc, ← pullback.condition (f := f) (g := g)]
      exact pullback.condition)

/-- The convolution kernel `R pr₁₃,* (L pr₁₂* K ⊗ᴸ L pr₂₃* K')` on `X ×_S Z`.
Source: Stacks 0FYS; AxiomMath/Stacks `FourierMukai/Composition.lean`. -/
def convolution {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (K : D (pullback f g)) (K' : D (pullback g h)) :
    D (pullback f h) :=
  (derivedPushforward (pr13 f g h)).obj
    (((derivedTensor (tripleProduct f g h)).obj
      ((derivedPullback (pr12 f g h)).obj K)).obj
        ((derivedPullback (pr23 f g h)).obj K'))

/-- Restrict a Fourier–Mukai functor to two full subcategories once
preservation of their actual object properties has been proved.
Source: Stacks 0FYQ; AxiomMath/Stacks `FourierMukai/Basic.lean`. -/
def fourierMukaiOn {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : D (pullback f g)) (P : ObjectProperty (D X)) (Q : ObjectProperty (D Y))
    (hPQ : ∀ M : P.FullSubcategory, Q ((fourierMukai f g K).obj M.obj)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ fourierMukai f g K) hPQ

/-- The restricted functor has the same underlying values. -/
theorem fourierMukaiOn_obj {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : D (pullback f g)) (P : ObjectProperty (D X)) (Q : ObjectProperty (D Y))
    (hPQ : ∀ M : P.FullSubcategory, Q ((fourierMukai f g K).obj M.obj))
    (M : P.FullSubcategory) :
    ((fourierMukaiOn f g K P Q hPQ).obj M).obj = (fourierMukai f g K).obj M.obj := rfl

/-- A kernel for a functor is an actual complex giving a naturally
isomorphic Fourier–Mukai functor. Source: Stacks 0FYQ. -/
def IsFourierMukaiKernel {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Φ : D X ⥤ D Y) (K : D (pullback f g)) : Prop :=
  Nonempty (Φ ≅ fourierMukai f g K)

/-- A functor is Fourier–Mukai if it admits such a kernel. -/
def IsFourierMukaiFunctor {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Φ : D X ⥤ D Y) : Prop :=
  ∃ K : D (pullback f g), IsFourierMukaiKernel f g Φ K

/-- A complex is a kernel for the functor constructed from it. -/
theorem isFourierMukaiKernel_self {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : D (pullback f g)) : IsFourierMukaiKernel f g (fourierMukai f g K) K :=
  ⟨Iso.refl _⟩

/-- The constructed functor is Fourier–Mukai. -/
theorem isFourierMukaiFunctor_fourierMukai {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : D (pullback f g)) : IsFourierMukaiFunctor f g (fourierMukai f g K) :=
  ⟨K, isFourierMukaiKernel_self f g K⟩

/-- Transfer a kernel along an actual natural isomorphism. -/
theorem IsFourierMukaiKernel.of_iso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {Φ Ψ : D X ⥤ D Y} {K : D (pullback f g)}
    (hK : IsFourierMukaiKernel f g Φ K) (e : Ψ ≅ Φ) : IsFourierMukaiKernel f g Ψ K :=
  hK.elim fun i => ⟨e ≪≫ i⟩

/-- Transfer the Fourier–Mukai property along an actual natural isomorphism. -/
theorem IsFourierMukaiFunctor.of_iso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {Φ Ψ : D X ⥤ D Y} (hΦ : IsFourierMukaiFunctor f g Φ) (e : Ψ ≅ Φ) :
    IsFourierMukaiFunctor f g Ψ :=
  hΦ.imp fun _ hK => hK.of_iso f g e

/-- Tensor on the right with an actual complex, using the same fixed
derived tensor construction. -/
abbrev tensorRightDerived (X : Scheme.{u}) (K : D X) : D X ⥤ D X :=
  (derivedTensor X).flip.obj K

/-- The tensor of the two pulled-back kernels on the actual triple product. -/
def convolutionTensor {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (K : D (pullback f g)) (K' : D (pullback g h)) : D (tripleProduct f g h) :=
  ((derivedTensor (tripleProduct f g h)).obj
    ((derivedPullback (pr12 f g h)).obj K)).obj ((derivedPullback (pr23 f g h)).obj K')

/-- Assemble the seven-step comparison proof from public AxiomMath/Stacks
`FourierMukai/Composition.lean`.

The supplied natural isomorphisms are the derived base-change comparison,
monoidality of derived pullback, the two projection-formula comparisons,
tensor associativity, and the pullback/pushforward composition comparisons.
Base change and the projection formulas are supplied only on their actual
quasi-coherent input subcategories. The three preservation hypotheses allow
the preceding functors to enter those subcategories.

This is a complete conditional construction. It asserts neither existence
nor invertibility of any geometric comparison. In the flat, quasi-compact,
quasi-separated setting those must be established separately using Stacks
08IB, 08EU and the quasi-coherent preservation results. -/
def fourierMukaiCompIsoOfComparisons {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (K : D (pullback f g)) (K' : D (pullback g h))
    (hA : ∀ M : QCohDerived X,
      quasicoherent (pullback f g)
        ((tensorRightDerived (pullback f g) K).obj
          ((derivedPullback (pullback.fst f g)).obj M.obj)))
    (hB : ∀ M : QCohDerived X,
      quasicoherent (tripleProduct f g h)
        ((tensorRightDerived (tripleProduct f g h)
          ((derivedPullback (pr12 f g h)).obj K)).obj
          ((derivedPullback (pr12 f g h)).obj
            ((derivedPullback (pullback.fst f g)).obj M.obj))))
    (hC : ∀ M : QCohDerived X,
      quasicoherent (pullback f h) ((derivedPullback (pullback.fst f h)).obj M.obj))
    (baseChange :
      (quasicoherent (pullback f g)).ι ⋙ derivedPushforward (pullback.snd f g) ⋙
          derivedPullback (pullback.fst g h) ≅
        (quasicoherent (pullback f g)).ι ⋙ derivedPullback (pr12 f g h) ⋙
          derivedPushforward (pr23 f g h))
    (pullbackTensor :
      tensorRightDerived (pullback f g) K ⋙ derivedPullback (pr12 f g h) ≅
        derivedPullback (pr12 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr12 f g h)).obj K))
    (projection23 :
      (quasicoherent (tripleProduct f g h)).ι ⋙ derivedPushforward (pr23 f g h) ⋙
          tensorRightDerived (pullback g h) K' ≅
        (quasicoherent (tripleProduct f g h)).ι ⋙
          tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr23 f g h)).obj K') ⋙
          derivedPushforward (pr23 f g h))
    (tensorAssociativity :
      tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr12 f g h)).obj K) ⋙
          tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr23 f g h)).obj K') ≅
        tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K'))
    (pullbackComposition :
      derivedPullback (pullback.fst f g) ⋙ derivedPullback (pr12 f g h) ≅
        derivedPullback (pullback.fst f h) ⋙ derivedPullback (pr13 f g h))
    (pushforwardComposition :
      derivedPushforward (pr23 f g h) ⋙ derivedPushforward (pullback.snd g h) ≅
        derivedPushforward (pr13 f g h) ⋙ derivedPushforward (pullback.snd f h))
    (projection13 :
      (quasicoherent (pullback f h)).ι ⋙ derivedPullback (pr13 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K') ⋙
          derivedPushforward (pr13 f g h) ≅
        (quasicoherent (pullback f h)).ι ⋙
          tensorRightDerived (pullback f h) (convolution f g h K K')) :
    (quasicoherent X).ι ⋙ fourierMukai f g K ⋙ fourierMukai g h K' ≅
      (quasicoherent X).ι ⋙ fourierMukai f h (convolution f g h K K') := by
  let A := (quasicoherent (pullback f g)).lift
    ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
      tensorRightDerived (pullback f g) K) hA
  let B := (quasicoherent (tripleProduct f g h)).lift
    ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
      derivedPullback (pr12 f g h) ⋙
      tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr12 f g h)).obj K)) hB
  let C := (quasicoherent (pullback f h)).lift
    ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f h)) hC
  calc
    (quasicoherent X).ι ⋙ fourierMukai f g K ⋙ fourierMukai g h K'
        ≅ ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
            tensorRightDerived (pullback f g) K) ⋙
          derivedPullback (pr12 f g h) ⋙ derivedPushforward (pr23 f g h) ⋙
          tensorRightDerived (pullback g h) K' ⋙ derivedPushforward (pullback.snd g h) :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft A baseChange)
        (tensorRightDerived (pullback g h) K' ⋙ derivedPushforward (pullback.snd g h))
    _ ≅ ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
          derivedPullback (pr12 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr12 f g h)).obj K)) ⋙
          derivedPushforward (pr23 f g h) ⋙ tensorRightDerived (pullback g h) K' ⋙
          derivedPushforward (pullback.snd g h) :=
      Functor.isoWhiskerLeft ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g))
        (Functor.isoWhiskerRight pullbackTensor
          (derivedPushforward (pr23 f g h) ⋙ tensorRightDerived (pullback g h) K' ⋙
            derivedPushforward (pullback.snd g h)))
    _ ≅ ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
          derivedPullback (pr12 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr12 f g h)).obj K)) ⋙
          tensorRightDerived (tripleProduct f g h) ((derivedPullback (pr23 f g h)).obj K') ⋙
          derivedPushforward (pr23 f g h) ⋙ derivedPushforward (pullback.snd g h) :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft B projection23)
        (derivedPushforward (pullback.snd g h))
    _ ≅ (quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
          derivedPullback (pr12 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K') ⋙
          derivedPushforward (pr23 f g h) ⋙ derivedPushforward (pullback.snd g h) :=
      Functor.isoWhiskerLeft ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f g) ⋙
        derivedPullback (pr12 f g h))
        (Functor.isoWhiskerRight tensorAssociativity
          (derivedPushforward (pr23 f g h) ⋙ derivedPushforward (pullback.snd g h)))
    _ ≅ (quasicoherent X).ι ⋙ derivedPullback (pullback.fst f h) ⋙
          derivedPullback (pr13 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K') ⋙
          derivedPushforward (pr23 f g h) ⋙ derivedPushforward (pullback.snd g h) :=
      Functor.isoWhiskerLeft (quasicoherent X).ι
        (Functor.isoWhiskerRight pullbackComposition
          (tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K') ⋙
            derivedPushforward (pr23 f g h) ⋙ derivedPushforward (pullback.snd g h)))
    _ ≅ ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f h)) ⋙
          derivedPullback (pr13 f g h) ⋙
          tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K') ⋙
          derivedPushforward (pr13 f g h) ⋙ derivedPushforward (pullback.snd f h) :=
      Functor.isoWhiskerLeft ((quasicoherent X).ι ⋙ derivedPullback (pullback.fst f h) ⋙
        derivedPullback (pr13 f g h) ⋙
        tensorRightDerived (tripleProduct f g h) (convolutionTensor f g h K K'))
        pushforwardComposition
    _ ≅ (quasicoherent X).ι ⋙ fourierMukai f h (convolution f g h K K') :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft C projection13)
        (derivedPushforward (pullback.snd f h))

end MathlibExt.AlgebraicGeometry.FourierMukai
