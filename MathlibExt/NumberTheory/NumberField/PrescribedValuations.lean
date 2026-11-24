/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

open IsDedekindDomain NumberField

namespace IsDedekindDomain.HeightOneSpectrum

private theorem exists_ne_zero_intValuation_eq_exp_neg (K : Type*) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      ∀ v : ↥S, v.1.intValuation a = WithZero.exp (-(m v : ℤ)) := by
  classical
  rcases isEmpty_or_nonempty (↥S) with hS | hne
  · exact ⟨1, one_ne_zero, fun v => (hS.false v).elim⟩
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v => if h : v ∈ S then m ⟨v, h⟩ + 1 else 0)
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v : ↥S => π v.1 ^ m v)
  have hval : ∀ v : ↥S, v.1.intValuation a = WithZero.exp (-(m v : ℤ)) := by
    intro v
    have hx : v.1.intValuation (π v.1 ^ m v) = WithZero.exp (-(m v : ℤ)) := by
      rw [map_pow, hπ v.1, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hmem : a - π v.1 ^ m v ∈ v.1.asIdeal ^ (m v + 1) := by
      simpa using ha v.1 v.2
    have hlt : v.1.intValuation (a - π v.1 ^ m v) < v.1.intValuation (π v.1 ^ m v) := by
      rw [hx]
      calc v.1.intValuation (a - π v.1 ^ m v) ≤ WithZero.exp (-((m v + 1 : ℕ) : ℤ)) :=
            (v.1.intValuation_le_pow_iff_dvd _ _).2 (Ideal.dvd_span_singleton.2 hmem)
        _ < WithZero.exp (-(m v : ℤ)) := by
            rw [WithZero.exp_lt_exp]
            omega
    have hadd := v.1.intValuation.map_add_eq_of_lt_left hlt
    rw [add_sub_cancel] at hadd
    exact hadd.trans hx
  refine ⟨a, fun h0 => ?_, hval⟩
  have h := hval hne.some
  rw [h0, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

/-- Every prescribed finite list of integer exponents at height-one primes of
a number field is realized by a nonzero field element: at each selected prime
`v`, the element can be chosen with `v`-adic valuation `exp (-n v)`. Negative
exponents are allowed, so the element need not be integral. -/
theorem exists_ne_zero_valuation_eq_exp_neg (K : Type*) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥S, v.1.valuation K α = WithZero.exp (-(n v)) := by
  rcases isEmpty_or_nonempty (↥S) with hS | hne
  · exact ⟨1, one_ne_zero, fun v => (hS.false v).elim⟩
  obtain ⟨a, -, ha⟩ :=
    exists_ne_zero_intValuation_eq_exp_neg K S fun v => (n v).toNat
  obtain ⟨b, -, hb⟩ :=
    exists_ne_zero_intValuation_eq_exp_neg K S fun v => (-n v).toNat
  have hval : ∀ v : ↥S,
      v.1.valuation K (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
        WithZero.exp (-(n v)) := by
    intro v
    simp only [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, ha, hb,
      ← WithZero.exp_sub]
    congr 1
    omega
  refine ⟨_, fun h0 => ?_, hval⟩
  have h := hval hne.some
  rw [h0, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

end IsDedekindDomain.HeightOneSpectrum
