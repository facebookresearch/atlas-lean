/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.RingTheory.Filtration

/-!
# Finite order in an adic filtration

In a Noetherian local ring, every nonzero element has a final nonzero
initial form for the powers of any proper ideal.  This is the element-first
counterpart to the Dedekind-domain result that fixes an exponent and then
produces an element in one power but not the next.

This file deliberately does not define a total adic-order function: the
zero element has infinite order, so such a definition requires a separately
reviewed extended-natural-valued interface.

## Main declaration

* `Ideal.exists_mem_pow_notMem_pow_succ_of_ne_zero`
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

private theorem exists_mem_pow_not_mem_pow_succ_of_iInf_eq_bot
    {R : Type u} [CommRing R] (I : Ideal R)
    (hsep : ⨅ n : ℕ, I ^ n = ⊥) {x : R} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ I ^ n ∧ x ∉ I ^ (n + 1) := by
  classical
  have hex : ∃ n : ℕ, x ∉ I ^ n := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hxbot : x ∈ (⊥ : Ideal R) := by
      rw [← hsep]
      exact Ideal.mem_iInf.mpr h
    exact hx (by simpa using hxbot)
  have hfind0 : Nat.find hex ≠ 0 := by
    intro hzero
    have htop : x ∈ I ^ Nat.find hex := by rw [hzero]; simp
    exact (Nat.find_spec hex) htop
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hfind0
  refine ⟨n, ?_, ?_⟩
  · by_contra hnot
    exact (Nat.find_min hex (by omega : n < Nat.find hex)) hnot
  · simpa [hn] using Nat.find_spec hex

/-- In a Noetherian local ring, every nonzero element belongs to some power
of a proper ideal but not to the next power. -/
theorem exists_mem_pow_notMem_pow_succ_of_ne_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) {x : R} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ I ^ n ∧ x ∉ I ^ (n + 1) :=
  exists_mem_pow_not_mem_pow_succ_of_iInf_eq_bot I
    (Ideal.iInf_pow_eq_bot_of_isLocalRing I hI) hx

end Ideal
