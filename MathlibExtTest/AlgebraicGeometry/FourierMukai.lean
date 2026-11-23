/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FourierMukai

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai

universe u

attribute [local instance] HasDerivedCategory.standard

section Existence

variable [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}]

-- The existence classes provide the Kan extensions, and the constructed functors have the
-- universal properties of left and right derived functors of their fixed sources.
example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackSource f).HasLeftDerivedFunctor (quasiIso Y) := inferInstance

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback f).IsLeftDerivedFunctor (derivedPullbackCounit f) (quasiIso Y) :=
  inferInstance

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPushforward f).IsRightDerivedFunctor (derivedPushforwardUnit f) (quasiIso X) :=
  inferInstance

end Existence

variable [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}] [HasDerivedTensors.{u}]

example (X : Scheme.{u}) :
    (derivedTensorUncurried X).IsLeftDerivedFunctor (derivedTensorCounit X)
      ((quasiIso X).prod (quasiIso X)) := inferInstance

-- The Fourier–Mukai functor is pull back, tensor with the kernel, push forward.
example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (K : D (pullback f g)) :
    fourierMukai f g K = derivedPullback (pullback.fst f g) ⋙
      tensorRightDerived (pullback f g) K ⋙ derivedPushforward (pullback.snd f g) := rfl

-- A complex is a kernel for its own Fourier–Mukai functor, and the Fourier–Mukai property
-- transfers along natural isomorphisms.
example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (K : D (pullback f g)) :
    IsFourierMukaiFunctor f g (fourierMukai f g K) :=
  isFourierMukaiFunctor_fourierMukai f g K

example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) {Φ Ψ : D X ⥤ D Y} (e : Ψ ≅ Φ)
    (h : IsFourierMukaiFunctor f g Φ) : IsFourierMukaiFunctor f g Ψ :=
  h.of_iso f g e

-- The restriction to full subcategories has the same underlying values.
example {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (K : D (pullback f g))
    (P : ObjectProperty (D X)) (Q : ObjectProperty (D Y))
    (hPQ : ∀ M : P.FullSubcategory, Q ((fourierMukai f g K).obj M.obj))
    (M : P.FullSubcategory) :
    ((fourierMukaiOn f g K P Q hPQ).obj M).obj = (fourierMukai f g K).obj M.obj :=
  fourierMukaiOn_obj f g K P Q hPQ M

-- The projections from the relative triple product are compatible.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    pr13 f g h ≫ pullback.fst f h = pr12 f g h ≫ pullback.fst f g := by
  simp [pr13]

example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    pr23 f g h ≫ pullback.snd g h = pr13 f g h ≫ pullback.snd f h := by
  simp [pr13, pr23]

example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    pr12 f g h ≫ pullback.snd f g = pr23 f g h ≫ pullback.fst g h := by
  simp [pr23]

-- The convolution kernel is the pushforward to `X ×_S Z` of the tensor of the two pulled-back
-- kernels on the triple product.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (K : D (pullback f g)) (K' : D (pullback g h)) :
    convolution f g h K K' = (derivedPushforward (pr13 f g h)).obj (convolutionTensor f g h K K') :=
  rfl

-- Given the comparison isomorphisms, the composite of two Fourier–Mukai functors on
-- quasi-coherent inputs is the Fourier–Mukai functor of the convolution.
example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (K : D (pullback f g)) (K' : D (pullback g h))
    (e : (quasicoherent X).ι ⋙ fourierMukai f g K ⋙ fourierMukai g h K' ≅
      (quasicoherent X).ι ⋙ fourierMukai f h (convolution f g h K K')) :
    ∀ M : QCohDerived X, Nonempty ((fourierMukai g h K').obj ((fourierMukai f g K).obj M.obj) ≅
      (fourierMukai f h (convolution f g h K K')).obj M.obj) :=
  fun M ↦ ⟨e.app M⟩
