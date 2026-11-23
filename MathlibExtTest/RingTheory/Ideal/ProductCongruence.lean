/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.ProductCongruence

@[expose] public section

/-- Consumer with the original binders, including `R : Type`. -/
private theorem exactSource
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hq : ((q : ℕ) : R) ∈ 𝔪)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) :=
  Ideal.mul_prod_sub_mem_pow_of_sub_mem_sq_of_natCast_mem q 𝔪 hq x₀ x₁ hx₀ hx₁ P hP

/-- Higher-universe consumer: the theorem is universe-polymorphic. -/
example (q : ℕ) [Fact q.Prime] {R : Type 1} [CommRing R] (𝔪 : Ideal R)
    (hq : ((q : ℕ) : R) ∈ 𝔪) (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R)
    (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) :=
  Ideal.mul_prod_sub_mem_pow_of_sub_mem_sq_of_natCast_mem q 𝔪 hq x₀ x₁ hx₀ hx₁ P hP

/-- Boundary: without `x₀ ∈ 𝔪` the conclusion can fail. Here `q = 2`,
`R = ℤ`, `𝔪 = (2)`, `x₀ = 1`, `x₁ = 2`, and `P c = x₁ + c.val * x₀`, so every
hypothesis except `x₀ ∈ 𝔪` holds, but the difference is `4 ∉ (2) ^ 4 = (16)`. -/
example : ¬ ((1 : ℤ) * (∏ c : ZMod 2, ((2 : ℤ) + ((c.val : ℕ) : ℤ) * 1)) -
      ((1 : ℤ) * (2 : ℤ) ^ 2 - (1 : ℤ) ^ 2 * (2 : ℤ)) ∈
      (Ideal.span {(2 : ℤ)}) ^ (2 + 2)) := by
  have hprod : (∏ c : ZMod 2, ((2 : ℤ) + ((c.val : ℕ) : ℤ) * 1)) = 6 := by
    decide
  rw [hprod]
  norm_num [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
