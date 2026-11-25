/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.AnnulusAttached

@[expose] public section

open AlgebraicCurve IsLocalRing

-- `exactSource` consumer of the main theorem with the original binders.
example
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar')
    (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0)
    (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) :
    ∀ R ∈ An.dom, μ (R.evalAt g) ≤ max 1 (μ b) ∧
      (μ b ≠ 1 → μ (R.evalAt g) < max 1 (μ b)) :=
  Annulus.abv_evalAt_le_max_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x hatt
    C' x' hatt' hwide g hg0 hpole hgC b hb0 hgC'

-- `exactSource` consumer of the two-end bound with the original binders.
example
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar')
    (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers)
    (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h) :
    0 ≤ x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) ∧
    (∀ R ∈ An.dom, μ (R.evalAt h) ≤ 1 ∧
      ((μ c' < 1 ∨
          0 < x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩)) →
        μ (R.evalAt h) < 1)) ∧
    ((μ c' = 1 ∧ x.ord (C.residue ⟨h, hC⟩) = 0 ∧
        x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0) →
      ∀ R ∈ An.dom, R.ord h = 0 ∧ μ (R.evalAt h) = 1) :=
  Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA An An' hdom hmod
    hmod0 htwo C x hatt C' x' hatt' hwide h hC hres c' hc'0 hc'A hC' hres' hpole

-- Universe check: the base field, function field and component fields may sit in different
-- universes.
universe u₁ u₂ u₃ u₄ in
example
    {L : Type u₁} [Field L] {A : ValuationSubring L} {F : Type u₂} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type u₃} {Fbar' : Type u₄} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar')
    (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0)
    (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) (R : Place L F) (hR : R ∈ An.dom) :
    μ (R.evalAt g) ≤ max 1 (μ b) :=
  (Annulus.abv_evalAt_le_max_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x hatt
    C' x' hatt' hwide g hg0 hpole hgC b hb0 hgC' R hR).1
