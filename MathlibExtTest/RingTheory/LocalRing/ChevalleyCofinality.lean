/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.ChevalleyCofinality

@[expose] public section

universe u

/-- Consumer with the original binders. -/
private theorem exactSource
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : ℕ → Ideal A) (hK : Antitone K) (hinf : ⨅ w, K w = ⊥) (N : ℕ) :
    ∃ w : ℕ, K w ≤ IsLocalRing.maximalIdeal A ^ N :=
  IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot K hK hinf N

/-- Higher-universe consumer. -/
private theorem exactSourceHigherUniverse
    {A : Type 1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : ℕ → Ideal A) (hK : Antitone K) (hinf : ⨅ w, K w = ⊥) (N : ℕ) :
    ∃ w : ℕ, K w ≤ IsLocalRing.maximalIdeal A ^ N :=
  IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot K hK hinf N

/-- Boundary: without the zero-intersection hypothesis the conclusion can
fail. The constant sequence at `⊤` is antitone, but no term lies in the
first power of the maximal ideal of a nontrivial local ring. -/
example {A : Type u} [CommRing A] [IsLocalRing A] :
    ¬ ∃ w : ℕ, (⊤ : Ideal A) ≤ IsLocalRing.maximalIdeal A ^ 1 := by
  rintro ⟨_, hw⟩
  rw [pow_one] at hw
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.1 hw)
