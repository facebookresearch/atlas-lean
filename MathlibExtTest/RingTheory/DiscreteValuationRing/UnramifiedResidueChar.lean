/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.UnramifiedResidueChar

@[expose] public section

/-- Consumer with the original universe-zero binders. -/
theorem exactSource
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧
      Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
      ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r ∧
      ∀ a : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π},
        ∃ b : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, b ^ r = a :=
  charP_quotient_span_algebraMap_and_forall_exists_pow_eq 𝒪 hdvr π hπ hcomplete
    hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed

/-- Higher-universe consumer. -/
theorem exactSource_univ1
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type 1) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    (hdvr : IsDiscreteValuationRing 𝒪)
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
  charP_quotient_span_algebraMap_and_forall_exists_pow_eq 𝒪 hdvr π hπ hcomplete
    hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
