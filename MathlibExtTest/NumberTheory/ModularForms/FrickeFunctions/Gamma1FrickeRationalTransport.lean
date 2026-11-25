/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.Gamma1FrickeRationalTransport
public import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.QExpansionSigmaTransport
public import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.SLTwoZModSurjective

/-! # Tests for Galois transport of `Γ₁(N)` cusp forms with Fricke-rational expressions -/

@[expose] public section

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/-- Source consumer with the original binders. -/
private theorem exactSource
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) τ) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) τ =
        ModularForm.discriminant τ ^ m *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) τ :=
  CuspForm.exists_gamma1_frickeRational_sigmaTransport N L hL W hW fricke hfricke jf hjf K hK s hs
      φ hφ k a b m hk f P Q hQ0 hid

universe u

/-- Higher-universe consumer: the polynomial-transport clause accepts index types in any
universe, not only `Type`. -/
example (N : ℕ) [NeZero N] (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (hφK : ∀ z : ↥K, φ z ∈ K)
    (T : (ℍ → ℂ) → (ℍ → ℂ) → Prop)
    (hT : ∀ g g' : ℍ → ℂ, T g g' ↔
        (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
          ∃ m : ℕ,
            (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            ∀ (n : ℕ) (z : ↥K),
              (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
              (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z))
    (ι : Type (u + 1)) (g g' : ι → ℍ → ℂ) (hg : ∀ i, T (g i) (g' i)) (R : MvPolynomial ι ↥K) :
    T (MvPolynomial.aeval g (MvPolynomial.map (algebraMap ↥K ℂ) R))
      (MvPolynomial.aeval g' (MvPolynomial.map φ R)) :=
  (ModularForm.qExpansion_sigmaTransport_package N K φ hφK T hT).1 g g' hg R

/-- A concrete level: every matrix in `SL(2, ZMod 6)` lifts to `SL(2, ℤ)`. -/
example : Function.Surjective
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod 6))) :=
  Matrix.SpecialLinearGroup.map_intCastRingHom_zmod_surjective 6
