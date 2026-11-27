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
The source statements restated in this file are copied from
`Definitions/Def_CuspForm_IntegralLattice.lean`,
`Theorems/Thm_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem.lean`,
`Theorems/Thm_CuspForm_exists_reductionModule_of_isLatticeRealized.lean`,
`Theorems/Thm_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two.lean`,
`Theorems/Thm_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean`, and
`Theorems/Thm_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd.lean`
in https://github.com/anthropics/fermats-last-theorem, compared with the source files at
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FormalHeckeReduction

@[expose] public section

open EisensteinWeightOne

/-- exactSource consumer: the original binders apply verbatim. -/
example (g : PowerSeries ℤ) (n : ℕ) :
    3 ∣ (PowerSeries.coeff n) (g * EisensteinWeightOne.e1Chi3) - (PowerSeries.coeff n) g :=
  EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub g n

/-- The source's weight-two cusp forms on `Γ₀(N)` with integral `q`-expansion coefficients. -/
private def srcIntegralSet (N : ℕ) : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  {f | ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ (⊥ : Subring ℂ)}

private theorem coe_intLattice_two (N : ℕ) :
    ((CuspForm.intLattice N 2 : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :
      Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = srcIntegralSet N := by
  ext f
  simp only [SetLike.mem_coe, CuspForm.mem_intLattice_iff, srcIntegralSet, Set.mem_ofPred_eq,
    Subring.mem_bot, ModularFormClass.qCoeff_eq]
  exact forall_congr' fun n => ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩

/-- exactSource restatement: the source's `HasIntegralBasis N`, that the weight-two cusp forms
with integral `q`-expansion span everything over `ℂ`, is `CuspForm.HasIntegralStructure N 2`. -/
example (N : ℕ) :
    Submodule.span ℂ (srcIntegralSet N) = ⊤ ↔ CuspForm.HasIntegralStructure N 2 := by
  rw [CuspForm.hasIntegralStructure_iff, coe_intLattice_two]

/-- exactSource restatement: the source's lattice realization, with the integral cusp form taken
from `srcIntegralSet N`, is `CuspForm.IsLatticeRealized N a`. -/
example (N : ℕ) (a : ℕ → ℤ) :
    (∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f ∈ srcIntegralSet N ∧
      ∃ af : ℕ → ℤ, (∀ n, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
        ∀ n, (3 : ℤ) ∣ af n - (bridgeProduct a).coeff n) ↔
      CuspForm.IsLatticeRealized N a := by
  rw [CuspForm.IsLatticeRealized, ← coe_intLattice_two]
  rfl

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {a : ℕ → ℤ} (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    {M : Type*} [AddCommGroup M] [Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M]
    (red : PowerSeries ℤ → M)
    (hker : ∀ g : PowerSeries ℤ, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0)
    (hker' : ∀ g : PowerSeries ℤ, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g)
    (h3M : (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0)
    (hop : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      (CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) • red (bridgeProduct a)
        = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) :
    ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}), 𝔪₁.IsMaximal ∧
      ((3 : ℕ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ :=
  CuspForm.exists_isMaximal_three_mem_heckeT_sub_mem h1 hT red hker hker' h3M hop

/-- exactSource consumer: the original binders apply verbatim; the integral structure is no
longer needed. -/
example {N : ℕ} [NeZero N] (_hN : CuspForm.HasIntegralStructure N 2) {a : ℕ → ℤ}
    (h1 : a 1 = 1) (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M)
      (red : PowerSeries ℤ → M),
      (∀ g, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0) ∧
      (∀ g, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g) ∧
      (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        (CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
            ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) • red (bridgeProduct a)
          = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) :=
  CuspForm.exists_reductionModule_of_isLatticeRealized h1 hreal

/-- exactSource consumer: the original binders apply verbatim. -/
example {R : Type*} [CommRing R] {N : ℕ} {a : ℕ → R}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : R)) a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) :=
  FormalHecke.IsEigensystem.three_dvd_coeff_heckeT_bridgeProduct_sub_smul heig hℓ hℓN n

/-- The two lattice-realization pieces combine: a lattice realization with `a 1 = 1` yields a
maximal ideal of the Hecke algebra above `3` containing every `T_ℓ - a ℓ`, once `bridgeProduct a`
is a formal eigenvector modulo `3`. -/
example {N : ℕ} [NeZero N] {a : ℕ → ℤ}
    (h1 : a 1 = 1) (hreal : CuspForm.IsLatticeRealized N a)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) :
    ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}), 𝔪₁.IsMaximal ∧
      ((3 : ℕ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ := by
  obtain ⟨M, _, _, red, hker, hker', h3M, hop⟩ :=
    CuspForm.exists_reductionModule_of_isLatticeRealized h1 hreal
  exact CuspForm.exists_isMaximal_three_mem_heckeT_sub_mem h1 hT red hker hker' h3M hop

/-- `U_ℓ` is a left inverse of `V_ℓ` on power series. -/
example (f : PowerSeries ℤ) : PowerSeries.heckeU 5 (PowerSeries.heckeV 5 f) = f :=
  PowerSeries.heckeU_heckeV 5 (by norm_num) f

/-- Boundary case: the constant series `1` is unchanged modulo `3` by `E₁,χ₋₃`. -/
example (n : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff n ((1 : PowerSeries ℤ) * e1Chi3) - PowerSeries.coeff n 1 :=
  three_dvd_coeff_mul_e1Chi3_sub 1 n

/-- The character `χ₋₃` takes the values `1, -1, 0` on `1, 2, 3`. -/
example : chiNegThree 1 = 1 ∧ chiNegThree 2 = -1 ∧ chiNegThree 3 = 0 := by decide
