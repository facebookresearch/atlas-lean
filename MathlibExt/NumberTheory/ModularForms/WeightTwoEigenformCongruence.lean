/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_heckeT_congr.lean`,
`P2M/Sol/S_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_heckeT_congr.lean`,
`Theorems/Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized.lean`, and
`P2M/Sol/S_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FormalHeckeReduction
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
import MathlibExt.NumberTheory.ModularForms.HeckeEigenformIntegral

/-!
# Weight-two eigenforms congruent to a residual eigensystem

A Deligne–Serre lifting statement in weight two. Let `N ≥ 1` be such that the cusp forms of
weight two on `Γ₀(N)` have an integral structure (`CuspForm.HasIntegralStructure N 2`: the forms
with integral `q`-expansions span them over `ℂ`), and let `a : ℕ → ℤ` with
`a 1 = 1` be a residual eigensystem modulo `3`: the formal series
`bridgeProduct a = (∑ aₙ qⁿ) · E₁(χ₋₃)` is a `T_ℓ`-eigenvector modulo `3` with eigenvalue `a ℓ`
for every prime `ℓ ∤ N`, and is congruent modulo `3` to the `q`-expansion of an integral cusp
form. Then there is a normalized eigenform `f` of weight two on `Γ₀(N)` and a maximal ideal
`𝔪'` above `3` of the ring of algebraic integers such that `a_ℓ(f) ≡ a ℓ (mod 𝔪')` for every
prime `ℓ ∤ N`.

## Main statements

* `CuspForm.exists_isNormalizedEigenform_congruent_of_heckeT_congr`: the statement above.
* `CuspForm.exists_isNormalizedEigenform_congruent_of_isLatticeRealized`: the same conclusion
  when `a` is a formal Hecke eigensystem with nebentypus values `χ₋₃(ℓ)` at the primes `ℓ ∤ N`
  and `0` at the primes `ℓ ∣ N`.
-/

@[expose] public section

open CongruenceSubgroup EisensteinWeightOne

namespace CuspForm

/-- **Deligne–Serre lifting in weight two.** Let `N ≠ 0` be such that the weight-two cusp forms
on `Γ₀(N)` have an integral structure, and let `a 1 = 1`. If `bridgeProduct a` is, modulo `3`, a
`T_ℓ`-eigenvector with eigenvalue `a ℓ` for every prime `ℓ ∤ N`, and is congruent modulo `3` to
the `q`-expansion of a cusp form in the integral lattice, then some normalized eigenform on
`Γ₀(N)` has Hecke eigenvalues congruent to `a ℓ` modulo a maximal ideal above `3` of the
algebraic integers, for every prime `ℓ ∤ N`. -/
theorem exists_isNormalizedEigenform_congruent_of_heckeT_congr
    {N : ℕ} [NeZero N] (hN : HasIntegralStructure N 2) {a : ℕ → ℤ} (h1 : a 1 = 1)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    (hreal : IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' := by
  obtain ⟨M, hACG, hMod, red, hker, hker', h3M, hop⟩ :=
    exists_reductionModule_of_isLatticeRealized h1 hreal
  obtain ⟨𝔪₁, h𝔪₁, h3𝔪₁, hT𝔪₁⟩ :=
    @exists_isMaximal_three_mem_heckeT_sub_mem N _ a h1 hT M hACG hMod red hker hker' h3M hop
  obtain ⟨f, hf, 𝔪', h𝔪', h3𝔪', hcong⟩ :=
    exists_isNormalizedEigenform_congruent_of_isMaximal hN 𝔪₁ h𝔪₁ (p := 3) h3𝔪₁
  exact ⟨f, hf, 𝔪', h𝔪', h3𝔪', fun ℓ hℓ hℓN => hcong ℓ hℓ hℓN (a ℓ) (hT𝔪₁ ℓ hℓ hℓN)⟩

/-- **Deligne–Serre lifting in weight two, eigensystem form.** Let `N ≠ 0` be such that the
weight-two cusp forms on `Γ₀(N)` have an integral structure, and let `a` be a formal Hecke
eigensystem with nebentypus values `χ₋₃(ℓ)` at the primes `ℓ ∤ N` and `0` at the primes `ℓ ∣ N`
(there the recursion reads `a (ℓ n) = a ℓ · a n`), whose bridge series is congruent modulo `3` to
the `q`-expansion of a cusp form in the integral lattice. Then some normalized eigenform on
`Γ₀(N)` has eigenvalues congruent to `a ℓ` modulo a maximal ideal above `3` of the algebraic
integers, for every prime `ℓ ∤ N`. -/
theorem exists_isNormalizedEigenform_congruent_of_isLatticeRealized
    {N : ℕ} [NeZero N] (hN : HasIntegralStructure N 2) {a : ℕ → ℤ}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a)
    (hreal : IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' :=
  exists_isNormalizedEigenform_congruent_of_heckeT_congr hN heig.1
    (fun _ hℓ hℓN n => heig.three_dvd_coeff_heckeT_bridgeProduct_sub_smul hℓ hℓN n) hreal

end CuspForm
