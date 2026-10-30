/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.Characterizations

@[expose] public section

/-!
# Tests for Dedekind criteria (Theorem 3.23, (1), (5), corrected (6))

Concrete checks at `ℤ` and `ℚ`: contain-is-divide, the principal-product
property, and the three-way equivalence.
-/

/-- Contain-is-divide at `ℤ`: `(6) ∣ (12)` because `(12) ≤ (6)`. -/
example : (Ideal.span {(6 : ℤ)} : Ideal ℤ) ∣ Ideal.span {(12 : ℤ)} :=
  ((isDedekindDomain_iff_contain_isDivide.mp inferInstance).2 _ _).mpr
    (Ideal.span_singleton_le_span_singleton.mpr ⟨2, by norm_num⟩)

/-- Contain-is-divide at `ℤ`, the other direction: `(12) ≤ (6)` from
`(6) ∣ (12)`. -/
example : (Ideal.span {(12 : ℤ)} : Ideal ℤ) ≤ Ideal.span {(6 : ℤ)} :=
  ((isDedekindDomain_iff_contain_isDivide.mp inferInstance).2 _ _).mp
    ⟨Ideal.span {(2 : ℤ)}, by
      rw [Ideal.span_singleton_mul_span_singleton]
      norm_num⟩

/-- Principal-product at `ℤ`: `(6)` becomes principal after multiplying
by a suitable ideal. -/
example : ∃ J : Ideal ℤ,
    (Ideal.span {(6 : ℤ)} * J).IsPrincipal ∧
      Ideal.span {(6 : ℤ)} * J ≠ ⊥ :=
  isDedekindDomain_iff_principalProduct.mp inferInstance _ (by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num)

/-- The three-way equivalence at `ℤ`. -/
example : List.TFAE
    [IsDedekindDomain ℤ,
     IsNoetherianRing ℤ ∧ ∀ I J : Ideal ℤ, I ∣ J ↔ J ≤ I,
     ∀ I : Ideal ℤ, I ≠ ⊥ →
       ∃ J : Ideal ℤ, (I * J).IsPrincipal ∧ I * J ≠ ⊥] :=
  isDedekindDomain_tfae_contain_isDivide_principalProduct

/-- Principal-product at `ℚ`: every nonzero ideal is `⊤`. -/
example : ∀ I : Ideal ℚ, I ≠ ⊥ →
    ∃ J : Ideal ℚ, (I * J).IsPrincipal ∧ I * J ≠ ⊥ :=
  isDedekindDomain_iff_principalProduct.mp inferInstance

#print axioms isDedekindDomain_iff_contain_isDivide
#print axioms isDedekindDomain_iff_principalProduct
#print axioms isDedekindDomain_tfae_contain_isDivide_principalProduct
