/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.CyclotomicDvr

@[expose] public section

open IsLocalRing Polynomial

-- `exactSource` consumer, with the original binders.
example
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type) [Field k] [CharP k q]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = IsLocalRing.maximalIdeal W₀) :
    ∃ (𝒪 : Type) (_ : CommRing 𝒪) (_ : IsDomain 𝒪) (_ : IsDiscreteValuationRing 𝒪)
      (_ : Algebra W₀ 𝒪)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪) (ζ : 𝒪) (res : 𝒪 →+* k),
      (∑ i ∈ Finset.range q, ζ ^ i) = 0 ∧
      IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ζ - 1} ∧
      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal 𝒪 ∧
      (∀ w : W₀, res (algebraMap W₀ 𝒪 w) = res₀ w) ∧
      (∀ (S : Type) [CommRing S] [Algebra W₀ S] (z : S),
        (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃! f : 𝒪 →ₐ[W₀] S, f ζ = z) :=
  IsDiscreteValuationRing.exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime
    q W₀ hW₀ k res₀ hres₀ hker₀

-- Higher-universe consumer.
example
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type 1) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type 1) [Field k] [CharP k q]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = IsLocalRing.maximalIdeal W₀) :
    ∃ (𝒪 : Type 1) (_ : CommRing 𝒪) (_ : IsDomain 𝒪)
      (_ : IsDiscreteValuationRing 𝒪) (_ : Algebra W₀ 𝒪)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪) (ζ : 𝒪) (res : 𝒪 →+* k),
      (∑ i ∈ Finset.range q, ζ ^ i) = 0 ∧
      IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ζ - 1} ∧
      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal 𝒪 ∧
      (∀ w : W₀, res (algebraMap W₀ 𝒪 w) = res₀ w) ∧
      (∀ (S : Type 1) [CommRing S] [Algebra W₀ S] (z : S),
        (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃! f : 𝒪 →ₐ[W₀] S, f ζ = z) :=
  IsDiscreteValuationRing.exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime
    q W₀ hW₀ k res₀ hres₀ hker₀

-- Boundary: `ζ = 1` does not satisfy the cyclotomic sum equation over `ℤ`
-- unless `q = 0`, so the adjoined root is genuinely nontrivial.
example (q : ℕ) : (∑ i ∈ Finset.range q, (1 : ℤ) ^ i) = q := by simp
