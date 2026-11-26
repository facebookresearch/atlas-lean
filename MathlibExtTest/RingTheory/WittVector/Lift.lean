/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.WittVector.Lift

@[expose] public section

universe u


/-- `exactSource` consumer with the original binders. -/
private theorem exactSource_constantCoeff
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B : Type u) [CommRing B] (ρ : B →+* k) (hρ : Function.Surjective ρ)
    (hnil : IsNilpotent (RingHom.ker ρ)) :
    ∃! f : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff :=
  WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker p k B ρ hρ hnil

/-- `exactSource` consumer with the original binders. -/
private theorem exactSource_surjective
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B B₀ : Type u) [CommRing B] [CommRing B₀] (q : B →+* B₀) (hq : Function.Surjective q)
    (hsq : ∀ s t : B, q s = 0 → q t = 0 → s * t = 0) (hpB : IsNilpotent (p : B))
    (ψ₀ : WittVector p k →+* B₀) :
    ∃! ψ : WittVector p k →+* B, q.comp ψ = ψ₀ :=
  WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
    p k B B₀ q hq hsq hpB ψ₀

/-- Higher-universe consumer in `Type 1`. -/
private theorem exactSource_constantCoeff_type1
    (p : ℕ) [Fact p.Prime] (k : Type 1) [Field k] [CharP k p] [PerfectRing k p]
    (B : Type 1) [CommRing B] (ρ : B →+* k) (hρ : Function.Surjective ρ)
    (hnil : IsNilpotent (RingHom.ker ρ)) :
    ∃! f : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff :=
  WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker p k B ρ hρ hnil

/-- Concrete consumer: the constant-coefficient map itself is the lift
through the identity on `ZMod 2`. -/
example : ∃! f : WittVector 2 (ZMod 2) →+* ZMod 2,
    (RingHom.id (ZMod 2)).comp f = WittVector.constantCoeff :=
  WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker 2 (ZMod 2)
    (ZMod 2) (RingHom.id _) Function.surjective_id ⟨1, by rw [pow_one]; ext x; simp⟩
