/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.DualNumberDeformation

@[expose] public section

/-- Consumer with the original level binders. -/
example (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : Nat.Prime ℓg) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    {A B Ω : Type*} [CommRing A] [CommRing B] [Field Ω]
    [Algebra A B] [Algebra A Ω]
    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    [IsAlgClosed Ω] [CharZero Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (φ₀ : B →ₐ[A] Ω) (D : B → Ω)
    (hDadd : ∀ x y : B, D (x + y) = D x + D y)
    (hDmul : ∀ x y : B, D (x * y) = φ₀ x * D y + D x * φ₀ y)
    (hDA : ∀ (a : A) (x : B), D (algebraMap A B a * x) = algebraMap A Ω a * D x)
    (hD : ∃ b : B, D b ≠ 0) :
    ∃ φ : B →ₐ[A] DualNumber Ω,
      (∀ b : B, (φ b).fst = φ₀ b) ∧ ∃ b : B, (φ b).snd ≠ 0 :=
  ModularCurve.FullLevel.Diamond.exists_algHom_dualNumber_fst_eq_snd_ne_zero_rigidDataH1Pow
    q M' hqM' ℓg hℓg hℓg12 hℓgM' hℓA hM'A hqΩ φ₀ D hDadd hDmul hDA hD

/-- Concrete boundary example: the second projection on dual numbers
over `ℚ` is itself such a derivation over the first projection, and
it is nonzero, as seen at `ε`. -/
example :
    ∃ φ : DualNumber ℚ →ₐ[ℚ] DualNumber ℚ,
      (∀ b : DualNumber ℚ, (φ b).fst = b.fst) ∧
        ∃ b : DualNumber ℚ, (φ b).snd ≠ 0 :=
  Algebra.exists_algHom_dualNumber_fst_eq_snd_ne_zero
    (TrivSqZeroExt.fstHom ℚ ℚ ℚ) (fun b => b.snd)
    (fun x y => rfl) (fun x y => DualNumber.snd_mul x y)
    (fun a x => by simp [TrivSqZeroExt.algebraMap_eq_inl'])
    ⟨DualNumber.eps, by simp⟩
