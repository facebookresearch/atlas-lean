/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.UnramifiedLifts

@[expose] public section

universe u


/-- `exactSource` consumer with the original binders. -/
theorem exactSource_charP
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r ∧
      ∀ a : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π},
        ∃ b : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, b ^ r = a :=
  IsDiscreteValuationRing.charP_residue_and_forall_exists_pow_eq
    𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed

/-- `exactSource` consumer with the original binders. -/
theorem exactSource_ringHomExt
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (C : Type u) [CommRing C] (hC : IsNilpotent ((r : ℕ) : C)) (f g : 𝒪 →+* C) : f = g :=
  IsDiscreteValuationRing.ringHom_ext_of_isNilpotent_natCast
    𝒪 hdvr π hπ hcomplete hres hunr C hC f g

/-- `exactSource` consumer with the original binders. -/
theorem exactSource_existsRingHom
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type u) [Field k] [CharP k r] [PerfectRing k r]
    (ρ₁ : Onr →+* k) (hρ₁ : Function.Surjective ρ₁)
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) :
    ∀ N : ℕ, ∃ f : WittVector r k →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N},
      (0 < N → ∀ (x : Onr) (w : WittVector r k),
          Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x = f w →
            ρ₁ x = WittVector.constantCoeff w) ∧
      Function.Surjective f ∧
      (∀ w : WittVector r k, f w = 0 ↔
        w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ N}) :=
  IsDiscreteValuationRing.exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span
    𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    k ρ₁ hρ₁ hker

/-- `exactSource` consumer with the original binders. -/
theorem exactSource_existsUniqueAlgHom
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type u) [CommRing B] [Algebra 𝒪 B] (B₀ : Type u) [CommRing B₀] [Algebra 𝒪 B₀]
    (p : B →ₐ[𝒪] B₀)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π))
    (hp : Function.Surjective p) (hsq : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ₀ : Onr →ₐ[𝒪] B₀) :
    ∃! ψ : Onr →ₐ[𝒪] B, p.comp ψ = ψ₀ :=
  IsDiscreteValuationRing.existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
    𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    B B₀ p hB hB₀ hp hsq ψ₀

/-- Higher-universe consumer in `Type 1`. -/
theorem exactSource_charP_type1
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type 1) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type 1) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r ∧
      ∀ a : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π},
        ∃ b : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, b ^ r = a :=
  IsDiscreteValuationRing.charP_residue_and_forall_exists_pow_eq
    𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed

/-- Boundary example: without a nilpotence hypothesis, ring maps need not
agree; evaluation at `0` and at `1` differ on `ℤ[X] → ℤ`. -/
example : (Polynomial.evalRingHom (0 : ℤ)) ≠ Polynomial.evalRingHom (1 : ℤ) := by
  intro h
  have := congrArg (fun φ : Polynomial ℤ →+* ℤ => φ Polynomial.X) h
  simp at this
