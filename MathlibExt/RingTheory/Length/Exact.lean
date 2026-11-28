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
public import MathlibExt.RingTheory.Length.ExactEulerChain

/-!
# Module length identities from exact linear maps

Let R be commutative and L →ᶠ M →ᵍ N an exact pair of R-linear maps, meaning Im(f) = Ker(g).
The middle module is an extension of Im(g) by Im(f), so ℓ_R(M) = ℓ_R(Im f) + ℓ_R(Im g) in ℕ∞.
If ℓ_R(M) is finite, taking natural values preserves this sum. Finite lengths of L and N also
imply finite length of M through its two ranges.

For a six-term sequence 0 → M₀ → M₁ → M₂ → M₃ → M₄ → M₅ → 0, assume exactness at the four
interior terms, injectivity of the first map, surjectivity of the last, and finite lengths of
M₁ through M₄. Then ℓ(M₀)−ℓ(M₁)+ℓ(M₂)−ℓ(M₃)+ℓ(M₄)−ℓ(M₅) = 0 in ℤ, using natural values of the
lengths. The exact-pair statements allow independent scalar and module carrier universes.
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

/-- Length of regular modules under a ring equivalence.

For a ring equivalence e : R ≃+* S between commutative rings, the regular-module lengths
satisfy ℓ_R(R) = ℓ_S(S). The equivalence transports the module structure and the scalar
action. -/
theorem length_self_eq_of_ringEquiv
    {S : Type v} [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let eAlg : R ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv fun _ => rfl
  exact eAlg.toLinearEquiv.length_eq.trans
    (Module.length_eq_of_surjective e.surjective)

/-- Finite middle length from finite ends of an exact pair.

For an exact R-linear pair L → M → N, if ℓ_R(L) and ℓ_R(N) are finite, then ℓ_R(M) is finite.
The two ranges have lengths bounded by those of L and N, and their sum is the middle length. -/
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

/-- Alternating length identity for a six-term exact sequence.

For R-linear maps M₀ → M₁ → M₂ → M₃ → M₄ → M₅, assume the first map injective, the last
surjective and all four interior pairs exact. If M₁,M₂,M₃,M₄ have finite length, the natural
values satisfy ℓ(M₀)−ℓ(M₁)+ℓ(M₂)−ℓ(M₃)+ℓ(M₄)−ℓ(M₅) = 0 in ℤ. The endpoint lengths are
controlled by the injective and surjective endpoint maps. -/
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
  have h₁range := exactPair_length_toNat
    R f₀ f₁ h₀₁ h₁
  have h₂range := exactPair_length_toNat
    R f₁ f₂ h₁₂ h₂
  have h₃range := exactPair_length_toNat
    R f₂ f₃ h₂₃ h₃
  have h₄range := exactPair_length_toNat
    R f₃ f₄ h₃₄ h₄
  have h₅range : (Module.length R f₄.range).toNat =
      (Module.length R M₅).toNat := by
    rw [LinearMap.range_eq_top.mpr hf₄, Module.length_top]
  omega

end SixTerm

end Module
