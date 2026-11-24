/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison.Homology
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Tensor homology of relative resolutions

The fixed-coefficient heterogeneous tensor functor is additive. It therefore sends relative
comparison homotopies to homotopies and identifies the homology of any two split relative
resolutions. The coefficient and resolution module universes are independent.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w uC vC
namespace ModuleCat

variable {R : Type u} [CommRing R]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  (U : ModuleCat.{v} R ⥤ C) [U.Additive]

/-- The original fixed-coefficient heterogeneous tensor functor. -/
abbrev relativeTensorFunctor (M : ModuleCat.{w} R) :
    ModuleCat.{v} R ⥤ ModuleCat.{max v w} R :=
  (tensorBifunctorAt R : ModuleCat.{w} R ⥤ ModuleCat.{v} R ⥤ ModuleCat.{max v w} R).obj M

/-- Tensor-relative comparison homology for any original endpoint morphism. -/
def tensorRelativeComparisonHomologyMap (M : ModuleCat.{w} R)
    (Q P : ChainComplex (ModuleCat.{v} R) ℕ) (X Y : ModuleCat.{v} R)
    (α : Q ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj X)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj Y)
    (σP : Functor.AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (n : ℕ) :
    (Functor.mappedResolution (relativeTensorFunctor M) Q).homology n ⟶
      (Functor.mappedResolution (relativeTensorFunctor M) P).homology n :=
  Functor.comparisonHomologyMap U (relativeTensorFunctor M) Q P X Y α β σP hQ kP f n

/-- Tensoring the two inverse comparison maps earns the homology isomorphism. -/
def tensorRelativeResolutionHomologyIso (M : ModuleCat.{w} R)
    (Q P : ChainComplex (ModuleCat.{v} R) ℕ) (X : ModuleCat.{v} R)
    (α : Q ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj X)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj X)
    (σQ : Functor.AugmentationSplit U Q X α) (σP : Functor.AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (n : ℕ) :
    (Functor.mappedResolution (relativeTensorFunctor M) Q).homology n ≅
      (Functor.mappedResolution (relativeTensorFunctor M) P).homology n :=
  Functor.comparisonHomologyIso U (relativeTensorFunctor M) Q P X α β σQ σP hQ hP kQ kP n

end ModuleCat
