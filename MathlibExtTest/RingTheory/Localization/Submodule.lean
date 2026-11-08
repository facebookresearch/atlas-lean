/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Int.Basic

@[expose] public section

/-- The ideal `(3)` in `ℤ` is prime. -/
instance : (Ideal.span {(3 : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (Int.prime_iff_natAbs_prime.mpr Nat.prime_three)

/-- The ideal `(2)` in `ℤ` is prime. -/
instance : (Ideal.span {(2 : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)

/-- The maximal-ideal intersection at `span ℤ {1}` in `ℚ`. -/
example : (⨅ 𝔪 : MaximalSpectrum ℤ,
    (Submodule.span ℤ {(1 : ℚ)}).localizedAt 𝔪.asIdeal.primeCompl) =
    Submodule.span ℤ {(1 : ℚ)} :=
  Submodule.eq_iInf_localizedAt_maximal _

/-- The prime-ideal intersection at `span ℤ {1}` in `ℚ`. -/
example : (⨅ 𝔭 : PrimeSpectrum ℤ,
    (Submodule.span ℤ {(1 : ℚ)}).localizedAt 𝔭.asIdeal.primeCompl) =
    Submodule.span ℤ {(1 : ℚ)} :=
  Submodule.eq_iInf_localizedAt_prime _

/-- The maximal- and prime-ideal intersections agree at `span ℤ {1}` in `ℚ`. -/
example : (⨅ 𝔪 : MaximalSpectrum ℤ,
    (Submodule.span ℤ {(1 : ℚ)}).localizedAt 𝔪.asIdeal.primeCompl) =
    (⨅ 𝔭 : PrimeSpectrum ℤ,
      (Submodule.span ℤ {(1 : ℚ)}).localizedAt 𝔭.asIdeal.primeCompl) :=
  Submodule.eq_iInf_localizedAt_maximal_eq_prime _

/-- The maximal-ideal intersection at `⊤` over `ℤ`, in `ℚ`. -/
example : (⨅ 𝔪 : MaximalSpectrum ℤ,
    (⊤ : Submodule ℤ ℚ).localizedAt 𝔪.asIdeal.primeCompl) = ⊤ :=
  Submodule.eq_iInf_localizedAt_maximal _

/-- The prime-ideal intersection at `⊥` over `ℤ`, in `ℚ`. -/
example : (⨅ 𝔭 : PrimeSpectrum ℤ,
    (⊥ : Submodule ℤ ℚ).localizedAt 𝔭.asIdeal.primeCompl) = ⊥ :=
  Submodule.eq_iInf_localizedAt_prime _

/-- The element-wise maximal-ideal form at `span ℤ {1}` in `ℚ`. -/
example (v : ℚ)
    (h : ∀ 𝔪 : MaximalSpectrum ℤ,
      v ∈ (Submodule.span ℤ {(1 : ℚ)}).localizedAt 𝔪.asIdeal.primeCompl) :
    v ∈ Submodule.span ℤ {(1 : ℚ)} :=
  Submodule.mem_of_forall_mem_localizedAt_maximal _ h

/-- `1 / 2` lies in the localization of `ℤ` (as a submodule of `ℚ`) at
the prime `(3)`: the denominator `2` is prime to `3`. -/
example : (1 / 2 : ℚ) ∈
    (Submodule.span ℤ {(1 : ℚ)}).localizedAt
      (Ideal.span {(3 : ℤ)}).primeCompl := by
  refine ⟨2, ?_, ?_⟩
  · rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
    norm_num
  · show (2 : ℤ) • (1 / 2 : ℚ) ∈ Submodule.span ℤ {(1 : ℚ)}
    have h : (2 : ℤ) • (1 / 2 : ℚ) = 1 := by norm_num
    rw [h]
    exact Submodule.subset_span (Set.mem_singleton _)

/-- `1 / 2` does not lie in the localization of `ℤ` (as a submodule of
`ℚ`) at the prime `(2)`: every denominator prime to `2` is odd, and an
odd multiple of `1 / 2` is never an integer. -/
example : (1 / 2 : ℚ) ∉
    (Submodule.span ℤ {(1 : ℚ)}).localizedAt
      (Ideal.span {(2 : ℤ)}).primeCompl := by
  rintro ⟨s, hs, hsm⟩
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] at hs
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsm
  have key : (2 : ℚ) * (a : ℚ) = (s : ℚ) := by
    have h := congrArg (fun x : ℚ => 2 * x) ha
    norm_num at h
    linarith [h]
  have h2 : (2 : ℤ) * a = s := by
    have h' : ((2 * a : ℤ) : ℚ) = (s : ℚ) := by push_cast; linarith [key]
    exact Int.cast_injective h'
  exact hs ⟨a, h2.symm⟩

/-- The same localization phenomenon in a product: `(1 / 2, 0)` lies in
the localization of `span ℤ {(1, 0)}` at the prime `(3)`, showing the
result is about submodules of an arbitrary module, not only about
submodules of a fraction field. -/
example : ((1 / 2, 0) : ℚ × ℚ) ∈
    (Submodule.span ℤ {((1, 0) : ℚ × ℚ)}).localizedAt
      (Ideal.span {(3 : ℤ)}).primeCompl := by
  refine ⟨2, ?_, ?_⟩
  · rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
    norm_num
  · show (2 : ℤ) • ((1 / 2, 0) : ℚ × ℚ) ∈
      Submodule.span ℤ {((1, 0) : ℚ × ℚ)}
    have h : (2 : ℤ) • ((1 / 2, 0) : ℚ × ℚ) = ((1, 0) : ℚ × ℚ) := by
      ext <;> norm_num
    rw [h]
    exact Submodule.subset_span (Set.mem_singleton _)
