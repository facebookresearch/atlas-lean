/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.FrobeniusEqualizer

@[expose] public section

universe u


/-- `exactSource` consumer with the original binders. -/
private theorem exactSource_frobTwo
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (n : ℕ)
    (Fr₂ : ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪]
        Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) ≃ₐ[𝒪] ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr
          ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪
            ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
              π) ^ (n + 1)})))
    (hFr₂ : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id
      𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
      Fr₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') :
    (∀ z : ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪]
        Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), Fr₂ (Fr₂ z) = z) ∧
    ∃ α : ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸
      Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
        (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), IsUnit (Fr₂ α - α) ∧
      Algebra.adjoin 𝒪 {α} = ⊤ ∧
      ∃ s t : 𝒪, α ^ 2 = algebraMap 𝒪 _ s * α + algebraMap 𝒪 _ t :=
  IsDiscreteValuationRing.frobTwo_frobTwo_and_exists_generator
    𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    hFr n Fr₂ hFr₂

/-- `exactSource` consumer with the original binders. -/
private theorem exactSource_algHom
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (n : ℕ)
    (Fr₂ : ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪]
        Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) ≃ₐ[𝒪] ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr
          ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪
            ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
              π) ^ (n + 1)})))
    (hFr₂ : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id
      𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
      Fr₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (ε ε' : ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪]
        Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) →ₐ[𝒪] B) :
    ε' = ε ∨ ε' = ε.comp Fr₂.toAlgHom :=
  IsDiscreteValuationRing.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing
    𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    hFr n Fr₂ hFr₂ B ε ε'
