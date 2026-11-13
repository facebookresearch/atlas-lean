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
* `Composition.lean`;
* `CompositionIso.lean`.

These portions are licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0

Modification notice: reused Mathlib's module-sheaf and complex constructions,
replaced the Stacks derived-operator implementations by wanted existence
obligations with their genuine Kan universal properties, and restricted the
composition statement to flat structure maps. No Stacks dependency is added.
-/

module

public import Batteries.Util.ProofWanted
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

This file records the missing unbounded derived operators needed to construct
`Φ_K(M) = R pr₂,* (L pr₁* M ⊗ᴸ K)` on actual module-sheaf derived categories.
The ordinary pullback, pushforward, tensor and total complex are Mathlib
constructions. Only existence of their genuine derived functors is deferred.

The tensor source is fixed: forget module sheaves to module presheaves, form
the total cochain tensor with its Koszul differential, and sheafify. Deriving
that functor along the product of the two localization functors derives both
variables. The Kan universal property determines each operator up to natural
isomorphism; no independently chosen tensor or zero functor is supplied.

The composition request is the flat special case of Stacks 0FYS. All three
structure maps are quasi-compact, quasi-separated and flat. Flatness of the
outer maps implies the Tor independence needed by the general source theorem.
The kernels and the source objects have quasi-coherent cohomology. The
isomorphism is natural in source objects and is stated in the ambient derived
category, so no additional choice of a restricted target functor is needed.

This statement about complexes of module sheaves does not supply a
compactified-Jacobian cohomological Fourier equivalence or the Fourier
vanishing results of a particular paper.

## References

* The Stacks Project, Tags 06YJ (derived pullback), 06YU (derived tensor),
  0FYQ (Fourier–Mukai functor), 0FYS (composition), 08IB (derived base change),
  and 08EU (projection formula).
* AxiomMath/Stacks, the precise source paths and revision in the notice above.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace WantedExt.AlgebraicGeometry.FourierMukaiWanted

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

/-- Existence of derived module-sheaf pullback, with the ordinary pullback
source and actual quasi-isomorphisms fixed. Source: Stacks 06YJ. -/
public instance_wanted derivedPullback_exists {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackSource f).HasLeftDerivedFunctor (quasiIso Y)

/-- `Lf*`, chosen by the right Kan extension that defines a left derived
functor. Its source is `pullbackSource f`. -/
public def_wanted derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : D Y ⥤ D X :=
  letI := ❰derivedPullback_exists❱ f
  (pullbackSource f).totalLeftDerived DerivedCategory.Q (quasiIso Y)

/-- The canonical comparison `Lf*(Q M) ⟶ Q(f* M)`. -/
public def_wanted derivedPullbackCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ ❰derivedPullback❱ f ⟶ pullbackSource f :=
  letI := ❰derivedPullback_exists❱ f
  (pullbackSource f).totalLeftDerivedCounit DerivedCategory.Q (quasiIso Y)

/-- Existence of unbounded derived direct image, pinned to the actual
module-sheaf pushforward source. Source: Stacks 0FYQ's direct-image factor. -/
public instance_wanted derivedPushforward_exists {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (pushforwardSource f).HasRightDerivedFunctor (quasiIso X)

/-- `Rf*`, chosen by the left Kan extension that defines a right derived
functor. Its source is `pushforwardSource f`. -/
public def_wanted derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    D X ⥤ D Y :=
  letI := ❰derivedPushforward_exists❱ f
  (pushforwardSource f).totalRightDerived DerivedCategory.Q (quasiIso X)

/-- The canonical comparison `Q(f_* M) ⟶ Rf_*(Q M)`. -/
public def_wanted derivedPushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushforwardSource f ⟶ DerivedCategory.Q ⋙ ❰derivedPushforward❱ f :=
  letI := ❰derivedPushforward_exists❱ f
  (pushforwardSource f).totalRightDerivedUnit DerivedCategory.Q (quasiIso X)

/-- Existence of derived tensor in both variables, with the ordinary cochain
tensor and product quasi-isomorphisms fixed. Source: Stacks 06YU. -/
public instance_wanted derivedTensor_exists (X : Scheme.{u}) :
    (tensorSource X).HasLeftDerivedFunctor ((quasiIso X).prod (quasiIso X))

/-- The uncurried derived tensor, chosen as the genuine total left derived
functor of `tensorSource X` along `Q × Q`. -/
public def_wanted derivedTensorUncurried (X : Scheme.{u}) :
    (D X × D X) ⥤ D X :=
  letI := ❰derivedTensor_exists❱ X
  (tensorSource X).totalLeftDerived
    (DerivedCategory.Q.prod DerivedCategory.Q) ((quasiIso X).prod (quasiIso X))

/-- The canonical comparison from derived tensor of representatives to their
ordinary cochain tensor. -/
public def_wanted derivedTensorCounit (X : Scheme.{u}) :
    (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ ❰derivedTensorUncurried❱ X ⟶
      tensorSource X :=
  letI := ❰derivedTensor_exists❱ X
  (tensorSource X).totalLeftDerivedCounit
    (DerivedCategory.Q.prod DerivedCategory.Q) ((quasiIso X).prod (quasiIso X))

/-- The curried derived tensor, obtained from the same derived construction. -/
public def_wanted derivedTensor (X : Scheme.{u}) : D X ⥤ D X ⥤ D X :=
  Functor.curry.obj (❰derivedTensorUncurried❱ X)

/-- Complexes whose actual cohomology module sheaves are quasi-coherent. -/
def quasicoherent (X : Scheme.{u}) : ObjectProperty (D X) :=
  fun M => ∀ n : ℤ,
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules n).obj M)

/-- The full subcategory of complexes with quasi-coherent cohomology. -/
abbrev QCohDerived (X : Scheme.{u}) := (quasicoherent X).FullSubcategory

/-- `Φ_K = L pr₁* ⋙ (− ⊗ᴸ K) ⋙ R pr₂,*`, for an actual kernel on `X ×_S Y`.
Source: Stacks 0FYQ; AxiomMath/Stacks `FourierMukai/Basic.lean`. -/
public def_wanted fourierMukai {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : D (pullback f g)) : D X ⥤ D Y :=
  ❰derivedPullback❱ (pullback.fst f g) ⋙
    ((❰derivedTensor❱ (pullback f g)).flip.obj K) ⋙
    ❰derivedPushforward❱ (pullback.snd f g)

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
public def_wanted convolution {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (K : D (pullback f g)) (K' : D (pullback g h)) :
    D (pullback f h) :=
  (❰derivedPushforward❱ (pr13 f g h)).obj
    (((❰derivedTensor❱ (tripleProduct f g h)).obj
      ((❰derivedPullback❱ (pr12 f g h)).obj K)).obj
        ((❰derivedPullback❱ (pr23 f g h)).obj K'))

/-- The flat special case of composition of Fourier–Mukai functors, natural
on source complexes with quasi-coherent cohomology. The source's Tor
independence follows here from the flat outer structure maps.

Source: Stacks 0FYS, 08IB and 08EU; AxiomMath/Stacks
`FourierMukai/CompositionIso.lean`, `quasiCoherentFourierMukaiCompNatIso`. -/
public theorem_wanted fourierMukai_comp_of_flat {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h] [Flat f] [Flat g] [Flat h]
    (K : D (pullback f g)) (K' : D (pullback g h))
    (hK : quasicoherent (pullback f g) K)
    (hK' : quasicoherent (pullback g h) K') :
    Nonempty
      ((quasicoherent X).ι ⋙ ❰fourierMukai❱ f g K ⋙ ❰fourierMukai❱ g h K' ≅
        (quasicoherent X).ι ⋙ ❰fourierMukai❱ f h (❰convolution❱ f g h K K'))

end WantedExt.AlgebraicGeometry.FourierMukaiWanted
