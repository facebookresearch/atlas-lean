/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.AbsolutelyIrreducible

@[expose] public section

open scoped TensorProduct

/-- Consumer with the original binders. -/
example {F k G V W : Type} [Field F] [Field k] [Algebra F k] [Group G]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower F k W]
    (ρ : Representation F G V) [Representation.IsAbsolutelyIrreducible.{0} ρ]
    (τ : Representation k G W)
    (ι : V →ₗ[F] W) (hι : Function.Injective ι)
    (hιG : ∀ (g : G) (v : V), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k) :=
  Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible ρ τ ι hι hιG

universe u v w x

/-- The same consumer in higher universes. -/
example {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k] {G : Type v} [Group G]
    {V : Type w} [AddCommGroup V] [Module F V]
    {W : Type x} [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower F k W]
    (ρ : Representation F G V) [Representation.IsAbsolutelyIrreducible.{u} ρ]
    (τ : Representation k G W)
    (ι : V →ₗ[F] W) (hι : Function.Injective ι)
    (hιG : ∀ (g : G) (v : V), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k) :=
  Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible ρ τ ι hι hιG

/-- Base change acts on pure tensors through the original action. -/
example {k : Type u} [Field k] {G : Type v} [Group G] {V : Type w} [AddCommGroup V]
    [Module k V] (k' : Type x) [CommRing k'] [Algebra k k']
    (ρ : Representation k G V) (g : G) (a : k') (v : V) :
    Representation.baseChange k' ρ g (a ⊗ₜ[k] v) = a ⊗ₜ[k] (ρ g v) :=
  Representation.baseChange_tmul k' ρ g a v

/-- The zero map is not injective after base change over a field, so the
injectivity hypothesis in the main theorem cannot simply be dropped. -/
example {F : Type} [Field F] :
    ¬ Function.Injective ((0 : F →ₗ[F] F).liftBaseChange F) := by
  intro h
  have h01 : (1 : F) ⊗ₜ[F] (1 : F) ≠ 0 := by
    intro hzero
    have hcon := congrArg (TensorProduct.lid F F) hzero
    simp [TensorProduct.lid_tmul] at hcon
  apply h01
  apply h
  simp
