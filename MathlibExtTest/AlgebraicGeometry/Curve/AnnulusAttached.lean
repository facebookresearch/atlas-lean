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
    (hwide : ∃ (Q₁ : Place L F) (hQ₁ : Q₁ ∈ An.dom) (Q₂ : Place L F) (hQ₂ : Q₂ ∈ An.dom),
      μ (Q₁.evalAt (An.isRational Q₁ hQ₁) An.param) ≠
        μ (Q₂.evalAt (An.isRational Q₂ hQ₂) An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0)
    (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) :
    ∀ (R : Place L F) (hR : R ∈ An.dom), μ (R.evalAt (An.isRational R hR) g) ≤ max 1 (μ b) ∧
      (μ b ≠ 1 → μ (R.evalAt (An.isRational R hR) g) < max 1 (μ b)) :=
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
    (hwide : ∃ (Q₁ : Place L F) (hQ₁ : Q₁ ∈ An.dom) (Q₂ : Place L F) (hQ₂ : Q₂ ∈ An.dom),
      μ (Q₁.evalAt (An.isRational Q₁ hQ₁) An.param) ≠
        μ (Q₂.evalAt (An.isRational Q₂ hQ₂) An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers)
    (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h) :
    0 ≤ x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) ∧
    (∀ (R : Place L F) (hR : R ∈ An.dom), μ (R.evalAt (An.isRational R hR) h) ≤ 1 ∧
      ((μ c' < 1 ∨
          0 < x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩)) →
        μ (R.evalAt (An.isRational R hR) h) < 1)) ∧
    ((μ c' = 1 ∧ x.ord (C.residue ⟨h, hC⟩) = 0 ∧
        x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0) →
      ∀ (R : Place L F) (hR : R ∈ An.dom),
        R.ord h = 0 ∧ μ (R.evalAt (An.isRational R hR) h) = 1) :=
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
    (hwide : ∃ (Q₁ : Place L F) (hQ₁ : Q₁ ∈ An.dom) (Q₂ : Place L F) (hQ₂ : Q₂ ∈ An.dom),
      μ (Q₁.evalAt (An.isRational Q₁ hQ₁) An.param) ≠
        μ (Q₂.evalAt (An.isRational Q₂ hQ₂) An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0)
    (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) (R : Place L F) (hR : R ∈ An.dom) :
    μ (R.evalAt (An.isRational R hR) g) ≤ max 1 (μ b) :=
  (Annulus.abv_evalAt_le_max_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x hatt
    C' x' hatt' hwide g hg0 hpole hgC b hb0 hgC' R hR).1

-- The source evaluates at every place through `Function.invFun`; at rational places, such as the
-- places of an annulus, its values are those of `Place.evalAt`.
open Classical in
private noncomputable def sourceEvalAt {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    Function.invFun (algebraMap K v.ResidueField)
      (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  else 0

private theorem evalAt_eq_sourceEvalAt {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (f : F) : v.evalAt hv f = sourceEvalAt v f := by
  by_cases hf : f ∈ v.toValuationSubring
  · rw [v.evalAt_of_mem hv hf]
    unfold sourceEvalAt
    rw [dite_eq_left hf]
    apply (algebraMap K v.ResidueField).injective
    rw [v.algebraMap_residueInv hv, Function.invFun_eq (hv _)]
  · unfold Place.evalAt sourceEvalAt
    rw [dite_eq_right hf, dite_eq_right hf]

-- The source's `mem_dom`, with its rationality conjunct and the source's evaluation, follows from
-- the fields `isRational` and `mem_dom`.
example {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) :
    ∀ P ∈ An.dom, P.IsRational ∧ An.param ∈ P.toValuationSubring ∧
      (∃ h : sourceEvalAt P An.param ∈ A,
        (⟨sourceEvalAt P An.param, h⟩ : A) ∈ maximalIdeal A) ∧
      sourceEvalAt P An.param ≠ 0 ∧
      ∃ m ∈ maximalIdeal A, (An.modulus : L) = sourceEvalAt P An.param * m := by
  intro P hP
  rw [← evalAt_eq_sourceEvalAt P (An.isRational P hP)]
  exact ⟨An.isRational P hP, An.mem_dom P hP⟩

-- The main theorem in the source's form, with the source's binders and evaluation.
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
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      μ (sourceEvalAt Q₁ An.param) ≠ μ (sourceEvalAt Q₂ An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0)
    (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) :
    ∀ R ∈ An.dom, μ (sourceEvalAt R g) ≤ max 1 (μ b) ∧
      (μ b ≠ 1 → μ (sourceEvalAt R g) < max 1 (μ b)) := by
  intro R hR
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  rw [← evalAt_eq_sourceEvalAt Q₁ (An.isRational Q₁ hQ₁),
    ← evalAt_eq_sourceEvalAt Q₂ (An.isRational Q₂ hQ₂)] at hne
  rw [← evalAt_eq_sourceEvalAt R (An.isRational R hR)]
  exact Annulus.abv_evalAt_le_max_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x
    hatt C' x' hatt' ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ g hg0 hpole hgC b hb0 hgC' R hR
