/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.RingTheory.Length

/-!
# Length identities for exact linear maps

An exact pair `L → M → N` presents `M` as an extension of the ranges of
the two maps.  This file records the resulting length identity, including a
natural-number form under explicit finiteness hypotheses.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w x

namespace Module

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [AddCommGroup L] [Module R L]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- A ring equivalence preserves the length of the regular module. -/
theorem length_self_eq_of_ringEquiv
    {S : Type v} [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let eAlg : R ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv fun _ => rfl
  exact eAlg.toLinearEquiv.length_eq.trans
    (Module.length_eq_of_surjective e.surjective)

/-- The length of the middle module of an exact pair is the sum of the
lengths of the two consecutive ranges. -/
theorem length_eq_range_add_range_of_exact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (h : Function.Exact f g) :
    Module.length R M =
      Module.length R f.range + Module.length R g.range := by
  apply Module.length_eq_add_of_exact
    f.range.subtype g.rangeRestrict
      (Submodule.injective_subtype f.range) g.surjective_rangeRestrict
  exact h.rangeFactorization ⟨0, g.map_zero⟩

/-- Natural-number form of the exact-pair range identity when the middle
module has finite length. -/
theorem length_toNat_eq_range_add_range_of_exact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (h : Function.Exact f g)
    (hM : Module.length R M ≠ ⊤) :
    (Module.length R M).toNat =
      (Module.length R f.range).toNat +
        (Module.length R g.range).toNat := by
  have hf : Module.length R f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective f.range.subtype
        (Submodule.injective_subtype f.range))
  have hg : Module.length R g.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_surjective g.rangeRestrict
        g.surjective_rangeRestrict)
  rw [length_eq_range_add_range_of_exact R f g h,
    ENat.toNat_add hf hg]

/-- The middle module of an exact pair has finite length when the source of
the first map and target of the second map have finite length. -/
theorem length_ne_top_of_exact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (h : Function.Exact f g)
    (hL : Module.length R L ≠ ⊤)
    (hN : Module.length R N ≠ ⊤) :
    Module.length R M ≠ ⊤ := by
  have hf : Module.length R f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hL
      (Module.length_le_of_surjective f.rangeRestrict
        f.surjective_rangeRestrict)
  have hg : Module.length R g.range ≠ ⊤ :=
    ne_top_of_le_ne_top hN
      (Module.length_le_of_injective g.range.subtype
        (Submodule.injective_subtype g.range))
  rw [length_eq_range_add_range_of_exact R f g h]
  simpa only [ne_eq, ENat.add_eq_top, not_or] using And.intro hf hg

section SixTerm

variable {M₀ M₁ M₂ M₃ M₄ M₅ : Type v}
variable [AddCommGroup M₀] [Module R M₀]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable [AddCommGroup M₃] [Module R M₃]
variable [AddCommGroup M₄] [Module R M₄]
variable [AddCommGroup M₅] [Module R M₅]

/-- Alternating finite-length identity for a six-term exact sequence.  The
first map is required to be injective and the last map surjective, so the
sequence is exact at both endpoints as well as at its four interior terms. -/
theorem alternating_length_six_of_exact
    (f₀ : M₀ →ₗ[R] M₁) (f₁ : M₁ →ₗ[R] M₂)
    (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄)
    (f₄ : M₄ →ₗ[R] M₅)
    (hf₀ : Function.Injective f₀) (hf₄ : Function.Surjective f₄)
    (h₀₁ : Function.Exact f₀ f₁) (h₁₂ : Function.Exact f₁ f₂)
    (h₂₃ : Function.Exact f₂ f₃) (h₃₄ : Function.Exact f₃ f₄)
    (h₁ : Module.length R M₁ ≠ ⊤)
    (h₂ : Module.length R M₂ ≠ ⊤)
    (h₃ : Module.length R M₃ ≠ ⊤)
    (h₄ : Module.length R M₄ ≠ ⊤) :
    ((Module.length R M₀).toNat : ℤ) -
        (Module.length R M₁).toNat +
        (Module.length R M₂).toNat -
        (Module.length R M₃).toNat +
        (Module.length R M₄).toNat -
        (Module.length R M₅).toNat = 0 := by
  let e₀ : M₀ ≃ₗ[R] f₀.range :=
    LinearEquiv.ofBijective f₀.rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff f₀).mpr hf₀,
        f₀.surjective_rangeRestrict⟩
  have h₀range : (Module.length R M₀).toNat =
      (Module.length R f₀.range).toNat :=
    congrArg ENat.toNat e₀.length_eq
  have h₁range := length_toNat_eq_range_add_range_of_exact
    R f₀ f₁ h₀₁ h₁
  have h₂range := length_toNat_eq_range_add_range_of_exact
    R f₁ f₂ h₁₂ h₂
  have h₃range := length_toNat_eq_range_add_range_of_exact
    R f₂ f₃ h₂₃ h₃
  have h₄range := length_toNat_eq_range_add_range_of_exact
    R f₃ f₄ h₃₄ h₄
  have h₅range : (Module.length R f₄.range).toNat =
      (Module.length R M₅).toNat := by
    rw [LinearMap.range_eq_top.mpr hf₄, Module.length_top]
  omega

end SixTerm

end Module
