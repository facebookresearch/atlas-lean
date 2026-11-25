/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.SupersingularInertia

-- The point API needs decidable equality on `AlgebraicClosure ℚ`, as in the source file.
attribute [local instance] Classical.decEq

@[expose] public section

open Matrix WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

namespace WeierstrassCurveSupersingularInertiaTest

/-- Consumer with the original binders, including a coefficient field in `Type`. -/
public theorem exactSource
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
public theorem exactSourceTypeOne
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
public theorem exactSourceValuation (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
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

/-- The base change along a ring homomorphism is the scalar extension for the induced
algebra structure. -/
public example {k K : Type} [Field k] [Field K] (φ : k →+* K) (ρ : ResidualGaloisRep k) :
    ρ.baseChangeAlong φ = (letI : Algebra k K := φ.toAlgebra; ρ.baseChange K) :=
  rfl

end WeierstrassCurveSupersingularInertiaTest
