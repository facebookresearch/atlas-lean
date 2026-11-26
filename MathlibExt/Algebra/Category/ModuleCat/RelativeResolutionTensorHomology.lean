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
# Tensor homology comparisons of split relative resolutions

Let `R` be commutative, `C` preadditive, and
`U : ModuleCat_v(R) → C` additive. A chain augmentation split by a
contracting family after applying `U`, together with preservation of
its augmentation and differential kernels, admits comparisons from
complexes with `U`-relative-projective terms. Tensoring these comparisons
with any `M : ModuleCat_w(R)` gives homology maps in `max(v,w)`.
Two split relative resolutions have canonically isomorphic tensor
homology. The coefficient and resolution carrier worlds are independent.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w uC vC
namespace ModuleCat

variable {R : Type u} [CommRing R]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  (U : ModuleCat.{v} R ⥤ C) [U.Additive]

/-- For a commutative ring `R` and coefficient module
`M : ModuleCat_w(R)`, the additive functor `M ⊗[R] -` maps
`ModuleCat_v(R)` to `ModuleCat_max(v,w)(R)`. -/
abbrev relativeTensorFunctor (M : ModuleCat.{w} R) :
    ModuleCat.{v} R ⥤ ModuleCat.{max v w} R :=
  (tensorBifunctorAt R : ModuleCat.{w} R ⥤ ModuleCat.{v} R ⥤ ModuleCat.{max v w} R).obj M

/-- Let `R` be commutative, `C` preadditive, and
`U : ModuleCat_v(R) → C` additive. Fix an arbitrary coefficient
`M : ModuleCat_w(R)`. Let `Q → X[0]`, `P → Y[0]` be chain augmentations. Suppose
`U(P → Y[0])` has a contracting splitting, every `Q_n` is
`U`-relative-projective, and `U` preserves the kernels of `P₀ → Y`
and every `P_(n+1) → P_n`. Any `f : X → Y` gives the canonical
comparison `H_n(M ⊗ Q) → H_n(M ⊗ P)`. -/
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

/-- Let `R` be commutative, `C` preadditive, and
`U : ModuleCat_v(R) → C` additive. Fix an arbitrary coefficient
`M : ModuleCat_w(R)`. Let `Q → X[0]`, `P → X[0]` have contracting splittings after
`U`, with all terms `U`-relative-projective. If `U` preserves each
augmentation kernel and every differential kernel of both complexes,
the inverse comparison maps give
`H_n(M ⊗ Q) ≅ H_n(M ⊗ P)` for every `n`. -/
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
