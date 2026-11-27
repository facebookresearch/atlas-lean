/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.SupersingularInertia
import MathlibExt.AlgebraicGeometry.EllipticCurve.TorsionCardinality

-- The point API needs decidable equality on `AlgebraicClosure ℚ`, as in the source file.
attribute [local instance] Classical.decEq

@[expose] public section

open Matrix WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

namespace WeierstrassCurveSupersingularInertiaTest

/-- Consumer with the original binders, including a coefficient field in `Type`. -/
private theorem exactSource
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type} [Field k]
    [Finite k] (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ σ).val =
      LinearMap.toMatrix b b
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).ρ σ))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ ψk : k →+* IsLocalRing.ResidueField P,
      ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
        ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v = P.tameCharacter π σ • v) ∨
          (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v =
              P.tameCharacter π σ ^ p • v)) :=
  W.exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular p hp2 ι hgood
    hss hcard hker ρ b hρ P hP π hπ

/-- Higher-universe consumer: the coefficient field may live in `Type 1`. -/
private theorem exactSourceTypeOne
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type 1} [Field k]
    [Finite k] (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ σ).val =
      LinearMap.toMatrix b b
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).ρ σ))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = p) :
    Nonempty (k →+* IsLocalRing.ResidueField P) :=
  let ⟨ψk, _⟩ :=
    W.exists_inertia_eigenvector_tameCharacter_residualGaloisRepOf_of_supersingular p hp2 ι
      hgood hss hcard hker ρ b hρ P hP π hπ
  ⟨ψk⟩

/-- Consumer of the torsion valuation lemma with the original binders. -/
private theorem exactSourceValuation (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (x y : AlgebraicClosure ℚ)
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hP : p • (Point.some x y h :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0) :
    A.valuation x ^ ((p ^ 2 - 1) / 2) * A.valuation (p : AlgebraicClosure ℚ) = 1 ∧
      A.valuation y ^ 2 = A.valuation x ^ 3 :=
  W.valuation_torsion_of_coeff_prePsi_dvd p hp2 hgood hss A hA x y h hP

/-- Consumer of the strong form: inertia acts through the tame character itself. -/
private theorem exactSourceStrong
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type} [Field k]
    [Finite k] (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (b : Module.Basis (Fin 2) k
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ σ).val =
      LinearMap.toMatrix b b
        ((((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι).ρ σ))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ ψk : k →+* IsLocalRing.ResidueField P,
      ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (Matrix.GeneralLinearGroup.map ψk (ρ σ)).val.mulVec v = P.tameCharacter π σ • v :=
  W.exists_inertia_mulVec_eq_tameCharacter_smul_of_supersingular p hp2 ι hgood hss hcard hker ρ
    b hρ P hP π hπ

/-- The base change along a ring homomorphism is the scalar extension for the induced
algebra structure. -/
example {k K : Type} [Field k] [Field K] (φ : k →+* K) (ρ : ResidualGaloisRep k) :
    ρ.baseChangeAlong φ = (letI : Algebra k K := φ.toAlgebra; ρ.baseChange K) :=
  rfl

/-! A concrete instance: `y ^ 2 = x ^ 3 + x` at `p = 3`, where `Δ = -64`, satisfies every
hypothesis on the curve, and its reduction is supersingular; `y ^ 2 = x ^ 3 + x ^ 2 + 1`
(`Δ = -496`) has good ordinary reduction at `3`, and the divisibility hypothesis fails there. -/

/-- The curve `y ^ 2 = x ^ 3 + x`. -/
private def W₀ : WeierstrassCurve ℤ := ⟨0, 0, 0, 1, 0⟩

/-- The curve `y ^ 2 = x ^ 3 + x ^ 2 + 1`. -/
private def W₁ : WeierstrassCurve ℤ := ⟨0, 1, 0, 0, 1⟩

private theorem W₀_Δ : W₀.Δ = -64 := by
  simp only [W₀, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

private theorem W₀_good : W₀.IsGoodPrimeFor 3 := by
  rw [WeierstrassCurve.IsGoodPrimeFor, W₀_Δ]
  decide

private theorem W₁_good : W₁.IsGoodPrimeFor 3 := by
  have hΔ : W₁.Δ = -496 := by
    simp only [W₁, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    norm_num
  rw [WeierstrassCurve.IsGoodPrimeFor, hΔ]
  decide

/-- At `p = 3` the inner coefficients of `preΨ' 3 = Ψ₃` are `3 b₆`, `3 b₄` and `b₂`; for `W₀`
they are `0`, `6` and `0`. -/
private theorem W₀_hss :
    ∀ i, 1 ≤ i → i < (3 ^ 2 - 1) / 2 → ((3 : ℕ) : ℤ) ∣ (W₀.preΨ' 3).coeff i := by
  intro i hi hi4
  norm_num at hi4
  rw [WeierstrassCurve.preΨ'_three]
  obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals
    simp only [WeierstrassCurve.Ψ₃, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_ofNat_mul, mul_assoc,
      Polynomial.coeff_X_pow]
    norm_num [W₀, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

private theorem W₀_card : Nat.card (Submodule.torsionBy ℤ
    ((W₀.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (3 : ℕ)) = 3 ^ 2 := by
  have : (W₀.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (by rw [WeierstrassCurve.map_Δ, W₀_Δ]; norm_num)⟩
  exact WeierstrassCurve.card_torsion_of_isAlgClosed _ (Nat.cast_ne_zero.mpr (by norm_num))

/-- The torsion valuation lemma on `W₀` at `3`: every nonzero `3`-torsion point has
`v(x) ^ 4 * v(3) = 1`. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 3)
    (x y : AlgebraicClosure ℚ)
    (h : ((W₀.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hP : (3 : ℕ) • (Point.some x y h :
      ((W₀.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0) :
    A.valuation x ^ 4 * A.valuation ((3 : ℕ) : AlgebraicClosure ℚ) = 1 :=
  (W₀.valuation_torsion_of_coeff_prePsi_dvd 3 (by decide) W₀_good W₀_hss A hA x y h hP).1

private instance : (W₀.map (Int.castRingHom (AlgebraicClosure (ZMod 3)))).IsElliptic :=
  W₀_good.isElliptic_map _

private instance : (W₁.map (Int.castRingHom (AlgebraicClosure (ZMod 3)))).IsElliptic :=
  W₁_good.isElliptic_map _

/-- `y ^ 2 = x ^ 3 + x` has supersingular reduction at `3`. -/
example : (W₀.map (Int.castRingHom (AlgebraicClosure (ZMod 3)))).toAffine.IsSupersingular :=
  (W₀.isSupersingular_map_iff_coeff_prePsi_dvd 3 (by decide)).mpr W₀_hss

/-- `y ^ 2 = x ^ 3 + x ^ 2 + 1` has ordinary reduction at `3`: the coefficient `b₂ = 4` of
`X ^ 3` in `Ψ₃` is not divisible by `3`. -/
example : ¬ (W₁.map (Int.castRingHom (AlgebraicClosure (ZMod 3)))).toAffine.IsSupersingular := by
  rw [W₁.isSupersingular_map_iff_coeff_prePsi_dvd 3 (by decide)]
  intro h
  have h3 := h 3 (by norm_num) (by norm_num)
  rw [WeierstrassCurve.preΨ'_three] at h3
  simp only [WeierstrassCurve.Ψ₃, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_ofNat_mul, mul_assoc,
    Polynomial.coeff_X_pow] at h3
  norm_num [W₁, WeierstrassCurve.b₂] at h3

end WeierstrassCurveSupersingularInertiaTest
