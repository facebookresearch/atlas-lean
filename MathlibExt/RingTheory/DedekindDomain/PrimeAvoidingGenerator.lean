/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The generator statement is adapted from `P2M/Sol/S_flt_regular.lean`,
lines 3325–3408, anthropics/fermats-last-theorem commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC; Apache License, Version 2.0.
That source ports the flt-regular project, copyright its authors:
Alex J. Best, Christopher Birkbeck, Riccardo Brasca, Eric Rodriguez Boidi,
Ruben Van de Velde, Andrew Yang; Apache License, Version 2.0.
See the source NOTICE and ATTRIBUTION.md §3. The proof below is independently
authored using Mathlib's simultaneous integer-multiple theorem.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Fractional generators avoiding a prime element

A principal quotient of integral ideals avoiding `(x)` has a presentation
`a / b` with both numerator and denominator avoiding the prime element `x`.
The integral ideals need not be principal, and `a,b` need not be coprime.
-/

@[expose] public section

open scoped nonZeroDivisors
open FractionalIdeal

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private lemma exists_integer_pair (P : Ideal R) (hP : P ≠ ⊤) (z : K) :
    ∃ a b : R, b ≠ 0 ∧
      algebraMap R K a / algebraMap R K b = z ∧ (a ∉ P ∨ b ∉ P) := by
  classical
  obtain ⟨t, ht, i, _, hi⟩ := Ideal.exist_integer_multiples_notMem
    (K := K) hP Finset.univ (fun i : Bool => if i then z else 1)
    (j := false) (Finset.mem_univ _) (by simp)
  obtain ⟨b, hb⟩ := ht false (Finset.mem_univ _)
  obtain ⟨a, ha⟩ := ht true (Finset.mem_univ _)
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hb
  simp only [↓reduceIte] at ha
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at hi
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
    exact ht0 hb.symm
  refine ⟨a, b, hb0, ?_, ?_⟩
  · rw [ha, hb, mul_div_cancel_left₀ _ ht0]
  · cases i
    · right
      intro h
      apply hi
      simpa only [Bool.false_eq_true, ↓reduceIte, mul_one, hb] using
        (mem_coeIdeal_of_mem (S := R⁰) (P := K) h)
    · left
      intro h
      apply hi
      simpa only [↓reduceIte, ha] using
        (mem_coeIdeal_of_mem (S := R⁰) (P := K) h)

/-- A principal quotient of ideals avoiding a prime element admits a
numerator and denominator both avoiding that element. -/
theorem exists_not_dvd_spanSingleton_eq {x : R} (hx : Prime x)
    (I J : Ideal R) (hI : ¬ Ideal.span {x} ∣ I)
    (hJ : ¬ Ideal.span {x} ∣ J)
    (h : Submodule.IsPrincipal
      ((I / J : FractionalIdeal R⁰ K) : Submodule R K)) :
    ∃ a b : R, ¬ x ∣ a ∧ ¬ x ∣ b ∧
      spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
  have hP := Ideal.isPrime_span_singleton_of_prime hx
  have hI' : ¬ I ≤ Ideal.span {x} := fun h => hI (Ideal.dvd_iff_le.mpr h)
  have hJ' : ¬ J ≤ Ideal.span {x} := fun h => hJ (Ideal.dvd_iff_le.mpr h)
  have hJ0 : (J : FractionalIdeal R⁰ K) ≠ 0 :=
    coeIdeal_ne_zero.mpr (fun h => hJ' (h ▸ bot_le))
  obtain ⟨z, hz⟩ := (isPrincipal_iff _).mp h
  obtain ⟨a, b, hb0, hab, hav⟩ := exists_integer_pair _ hP.ne_top z
  have heq : spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) *
      (J : FractionalIdeal R⁰ K) = I := by
    rw [hab, ← hz, div_mul_cancel₀ _ hJ0]
  have hcross : Ideal.span {a} * J = Ideal.span {b} * I :=
    (mk'_mul_coeIdeal_eq_coeIdeal K
      (mem_nonZeroDivisors_iff_ne_zero.mpr hb0)).mp
      (by simpa only [IsFractionRing.mk'_eq_div] using heq)
  have hmem : a ∈ Ideal.span {x} ↔ b ∈ Ideal.span {x} := by
    have hmul := congrArg (fun L : Ideal R => L ≤ Ideal.span {x}) hcross
    simpa only [hP.mul_le, Ideal.span_singleton_le_iff_mem,
      hI', hJ', or_false] using Iff.of_eq hmul
  have ha : a ∉ Ideal.span {x} := fun h => hav.elim (· h) (· (hmem.mp h))
  exact ⟨a, b, fun h => ha (Ideal.mem_span_singleton.mpr h),
    fun h => ha (hmem.mpr (Ideal.mem_span_singleton.mpr h)), by rw [hab, hz]⟩

end FractionalIdeal
