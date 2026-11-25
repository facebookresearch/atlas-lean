/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FormalHeckeReduction

@[expose] public section

open EisensteinWeightOne

/-- exactSource consumer: the original binders apply verbatim. -/
example (g : PowerSeries ℤ) (n : ℕ) :
    3 ∣ (PowerSeries.coeff n) (g * EisensteinWeightOne.e1Chi3) - (PowerSeries.coeff n) g :=
  EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub g n

/-- exactSource consumer: the original binders apply verbatim. -/
example (N : ℕ) : CuspForm.HasIntegralBasis N ↔ CuspForm.HasIntegralStructure N 2 :=
  CuspForm.hasIntegralBasis_iff_hasIntegralStructure_two N

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

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {a : ℕ → ℤ}
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
  CuspForm.exists_reductionModule_of_isLatticeRealized hN h1 hreal

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
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {a : ℕ → ℤ}
    (h1 : a 1 = 1) (hreal : CuspForm.IsLatticeRealized N a)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a)) :
    ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}), 𝔪₁.IsMaximal ∧
      ((3 : ℕ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN -
          ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ := by
  obtain ⟨M, _, _, red, hker, hker', h3M, hop⟩ :=
    CuspForm.exists_reductionModule_of_isLatticeRealized hN h1 hreal
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
