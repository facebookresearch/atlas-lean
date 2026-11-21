/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.ChevalleyCofinality

@[expose] public section

universe v

-- Consumer with the original binders, at a higher universe.
example {A : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (I : ℕ → Ideal A) (hI : Antitone I) (hinf : ⨅ n, I n = ⊥) (N : ℕ) :
    ∃ n, I n ≤ IsLocalRing.maximalIdeal A ^ N :=
  IsLocalRing.exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete I hI hinf N

-- The zero-intersection hypothesis matters: the constant sequence at the
-- maximal ideal itself is not contained in the square of the maximal ideal
-- in a field viewed as a local ring (where the maximal ideal is zero, this
-- is vacuous), so instead we record the conclusion for the zero sequence.
example {A : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (N : ℕ) :
    ∃ n : ℕ, (⊥ : Ideal A) ≤ IsLocalRing.maximalIdeal A ^ N := by
  obtain ⟨n, hn⟩ := IsLocalRing.exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete
    (fun _ => (⊥ : Ideal A)) (by intro a b _; exact le_rfl) (by simp) N
  exact ⟨n, hn⟩
