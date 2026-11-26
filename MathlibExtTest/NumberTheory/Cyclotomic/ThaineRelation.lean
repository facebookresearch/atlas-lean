/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.CyclotomicUnitOmegaTwo
public import MathlibExt.NumberTheory.Cyclotomic.ThaineRelation
public import MathlibExt.NumberTheory.Cyclotomic.UnitsOmegaEigenspaceFinrank

@[expose] public section

open scoped NumberField nonZeroDivisors

open NumberField Stickelberger

universe u

section ExactSource

variable (p : ℕ) [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in

/-- Source-faithful consumer: the `ω²`-eigenspace of units modulo `p`-th powers is a line. -/
theorem exactSource_finrank_unitsOmegaEigenspace_two (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1 :=
  finrank_unitsOmegaEigenspace_two p hp5

/-- Source-faithful consumer: the `ω²`-component of the cyclotomic unit `1 + ζ` is nonzero. -/
theorem exactSource_omegaIdempotent_two_cycloUnitTwo_ne_zero (hp5 : 5 ≤ p)
    (ζ : 𝓞 (CyclotomicField p ℚ)) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (c₂ : (𝓞 (CyclotomicField p ℚ))ˣ) (hc : (c₂ : 𝓞 (CyclotomicField p ℚ)) = 1 + ζ) :
    omegaIdempotent p (unitsGalAction p) 2
        (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p
          (Additive.ofMul c₂)) ≠ 0 :=
  omegaIdempotent_two_cycloUnitTwo_ne_zero p hp5 ζ hζ c₂ hc

section Thaine

attribute [-simp] Stickelberger.unitsEnd_proj

set_option backward.isDefEq.respectTransparency false

/-- Source-faithful consumer for Thaine's relation in `ℚ(ζ_p)⁺`, with the original binders. -/
theorem exactSource_thaine_relation_plusField (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [IsTotallyReal Kplus]
    [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (𝔏 : Ideal (𝓞 Kplus)) (h𝔏max : 𝔏.IsMaximal)
    (h𝔏deg : Ideal.absNorm 𝔏 = ℓ)
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hδ𝔏 : (Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus))
      ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x}) :
    ∃ (α : Kplus) (_hα : α ≠ 0) (t : ZMod p) (_ht : t ≠ 0) (J : Ideal (𝓞 Kplus)),
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 Kplus)) α =
        (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom :
          FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^
            (t * ((d : ZMod p) ^ 2)⁻¹).val) *
        (J : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ p :=
  thaine_relation_plusField p hp5 Kplus hKplus Δact hΔact ℓ hℓ hℓp 𝔏 h𝔏max h𝔏deg δ hδeig hδ𝔏

end Thaine

end ExactSource

set_option backward.isDefEq.respectTransparency false in
/-- The relation applies to a totally real field in any universe. -/
example (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (Kplus : Type u) [Field Kplus] [NumberField Kplus] [IsTotallyReal Kplus]
    [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (𝔏 : Ideal (𝓞 Kplus)) (h𝔏max : 𝔏.IsMaximal) (h𝔏deg : Ideal.absNorm 𝔏 = ℓ)
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hδ𝔏 : (Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus)) ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x}) :
    ∃ t : ZMod p, t ≠ 0 :=
  let ⟨_, _, t, ht, _⟩ :=
    thaine_relation_plusField p hp5 Kplus hKplus Δact hΔact ℓ hℓ hℓp 𝔏 h𝔏max h𝔏deg δ hδeig hδ𝔏
  ⟨t, ht⟩
