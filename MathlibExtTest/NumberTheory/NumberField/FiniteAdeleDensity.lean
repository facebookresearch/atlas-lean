/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.FiniteAdeleDensity

@[expose] public section

open IsDedekindDomain NumberField

/-- `exactSource` consumer with the original binders. -/
example (K : Type) [Field K] [NumberField K] :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) ∧
    (∀ (R : Type) [Ring R] [TopologicalSpace R] [T2Space R]
        (Ψ Ψ' : FiniteAdeleRing (𝓞 K) K →+* R), Continuous Ψ → Continuous Ψ' →
        (∀ a : K, Ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) =
          Ψ' (algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) → Ψ = Ψ') :=
  NumberField.denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext K

/-- Higher-universe consumer: the statement is universe-polymorphic. -/
example (K : Type*) [Field K] [NumberField K] (R : Type*) [Ring R]
    [TopologicalSpace R] [T2Space R]
    (Ψ Ψ' : FiniteAdeleRing (𝓞 K) K →+* R) (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ')
    (h : ∀ a : K, Ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) =
      Ψ' (algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) : Ψ = Ψ' :=
  (NumberField.denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext K).2 R Ψ Ψ' hΨ hΨ' h

/-- Boundary example: density fails without the number-field hypothesis in
the sense that the diagonal map need not even be defined by this statement;
concretely, agreement on `K` forces equality already for maps into `ℂ`. -/
example (K : Type*) [Field K] [NumberField K]
    (Ψ Ψ' : FiniteAdeleRing (𝓞 K) K →+* ℂ) (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ')
    (h : ∀ a : K, Ψ (algebraMap K (FiniteAdeleRing (𝓞 K) K) a) =
      Ψ' (algebraMap K (FiniteAdeleRing (𝓞 K) K) a)) : Ψ = Ψ' :=
  (NumberField.denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext K).2 ℂ Ψ Ψ' hΨ hΨ' h
