/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.MinimalPrimesTensorProduct

@[expose] public section

open scoped TensorProduct

-- Consumer with the original binders, recovering the first two conclusions.
example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (j₀ : B)
    [IsDomain ↥(Algebra.adjoin A ({j₀} : Set B))]
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({j₀} : Set B)) B)
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({j₀} : Set B)) B) 𝔭 = ⊥) :
    (∀ 𝔓 : Ideal (FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
        ({j₀} : Set B))] B), 𝔓.IsPrime →
      Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[↥(Algebra.adjoin A
        ({j₀} : Set B))] FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
        ({j₀} : Set B))] B) 𝔓 ∈ (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      ∃! 𝔓 : Ideal (FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
        ({j₀} : Set B))] B), 𝔓.IsPrime ∧
        Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[↥(Algebra.adjoin A
          ({j₀} : Set B))] FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
          ({j₀} : Set B))] B) 𝔓 = 𝔭) := by
  haveI := hint
  exact Ideal.minimalPrimes_tensorProduct_fractionRing_dictionary hdom

-- Higher-universe consumer: the statement is universe-polymorphic.
example (A B : Type 1) [CommRing A] [CommRing B] [Algebra A B] (j₀ : B)
    [IsDomain ↥(Algebra.adjoin A ({j₀} : Set B))]
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({j₀} : Set B)) B)
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({j₀} : Set B)) B) 𝔭 = ⊥) :
    (∀ 𝔓 : Ideal (FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
        ({j₀} : Set B))] B), 𝔓.IsPrime →
      Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[↥(Algebra.adjoin A
        ({j₀} : Set B))] FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
        ({j₀} : Set B))] B) 𝔓 ∈ (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      ∃! 𝔓 : Ideal (FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
        ({j₀} : Set B))] B), 𝔓.IsPrime ∧
        Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[↥(Algebra.adjoin A
          ({j₀} : Set B))] FractionRing ↥(Algebra.adjoin A ({j₀} : Set B)) ⊗[↥(Algebra.adjoin A
          ({j₀} : Set B))] B) 𝔓 = 𝔭) := by
  haveI := hint
  exact Ideal.minimalPrimes_tensorProduct_fractionRing_dictionary hdom

-- Boundary: with `B = S`, the zero ideal is minimal, so it has a unique
-- prime above it in the generic fibre.
example {S : Type*} [CommRing S] [IsDomain S] :
    ∀ 𝔭 ∈ (⊥ : Ideal S).minimalPrimes, ∃! 𝔓 : Ideal (FractionRing S ⊗[S] S),
      𝔓.IsPrime ∧ Ideal.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[S] FractionRing S ⊗[S] S) 𝔓 = 𝔭 := by
  have hdom : ∀ 𝔭 ∈ (⊥ : Ideal S).minimalPrimes,
      Ideal.comap (algebraMap S S) 𝔭 = ⊥ := by
    intro 𝔭 h𝔭
    have h𝔭0 : 𝔭 = ⊥ := by
      rcases h𝔭 with ⟨⟨-, -⟩, hmin⟩
      exact le_antisymm (hmin ⟨Ideal.isPrime_bot, bot_le⟩ bot_le) bot_le
    rw [h𝔭0]
    simp
  exact (Ideal.minimalPrimes_tensorProduct_fractionRing_dictionary hdom).2
