/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.NumberTheory.NumberField.PrescribedValuations

@[expose] public section

open IsDedekindDomain NumberField

private theorem exactSource (K : Type) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥S, v.1.valuation K α = WithZero.exp (-(n v)) :=
  IsDedekindDomain.HeightOneSpectrum.exists_ne_zero_valuation_eq_exp_neg K S n

-- The same statement for a field in a higher universe.
example (K : Type 1) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ↥S → ℤ) :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥S, v.1.valuation K α = WithZero.exp (-(n v)) :=
  IsDedekindDomain.HeightOneSpectrum.exists_ne_zero_valuation_eq_exp_neg K S n

-- Boundary case: with no primes selected, the element `1` realizes the
-- vacuous prescription, and the prescribed value at any prime would force
-- a nonzero element, since `WithZero.exp` never takes the value `0`.
example (K : Type) [Field K] [NumberField K] :
    ∃ α : K, α ≠ 0 ∧ ∀ v : ↥(∅ : Finset (HeightOneSpectrum (𝓞 K))),
      v.1.valuation K α = WithZero.exp (-((fun _ => (0 : ℤ)) v)) :=
  IsDedekindDomain.HeightOneSpectrum.exists_ne_zero_valuation_eq_exp_neg
    K ∅ (fun _ => 0)
