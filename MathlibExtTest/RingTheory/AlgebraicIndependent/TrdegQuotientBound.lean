/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AlgebraicIndependent.TrdegQuotientBound

@[expose] public section

universe u v

-- exactSource consumer: the original binders apply verbatim.
example {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) :=
  Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le 𝔮

-- Higher-universe consumer: the statement is universe-polymorphic.
example {A : Type 1} {B : Type 2} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) :=
  Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le 𝔮

-- Field boundary: for `A = B = ℚ` and `𝔮 = ⊥`, every prime of `ℚ` is `⊥`, so the avoidance
-- condition holds automatically for the element `s ∉ ⊥.under ℚ` produced (it only says
-- `s ≠ 0`): no specialization is excluded, and the bound applies at every prime of `ℚ`.
example : ∀ (𝔔 : Ideal ℚ) [𝔔.IsPrime],
    Algebra.trdeg (ℚ ⧸ 𝔔.under ℚ) (ℚ ⧸ 𝔔) ≤
      Algebra.trdeg (ℚ ⧸ (⊥ : Ideal ℚ).under ℚ) (ℚ ⧸ (⊥ : Ideal ℚ)) := by
  obtain ⟨s, hs, hbound⟩ :=
    Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le (A := ℚ) (B := ℚ)
      (⊥ : Ideal ℚ)
  intro 𝔔 _
  obtain rfl := Ideal.eq_bot_of_prime 𝔔
  exact hbound ⊥ le_rfl hs
