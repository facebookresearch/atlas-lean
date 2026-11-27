/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.Nilpotent
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Tests for the nilpotence of the monodromy operator

A two-dimensional `(φ, N)`-module over `ℚ_[p]`, with `σ` the identity and the scalar `p`: on
`ℚ_[p] × ℚ_[p]`, with `e₁ = (1, 0)` and `e₂ = (0, 1)`, `φ e₁ = e₁`, `φ e₂ = p • e₂`, `N e₁ = 0`
and `N e₂ = e₁`. The `p`-adic valuation `v` of `ℚ_[p]` has `v p = 1 ≠ 0`, so the results of
`MathlibExt.RingTheory.PhiNModule.Nilpotent` apply.
-/

namespace MathlibExtTest.RingTheory.PhiNModule.Nilpotent

variable {p : ℕ} [hp : Fact p.Prime]

/-- The prime `p` is nonzero in `ℚ_[p]`. -/
theorem cast_p_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

/-- The `p`-adic valuation of `p` is nonzero. -/
theorem addValuation_cast_p_ne_zero : Padic.addValuation (p : ℚ_[p]) ≠ 0 := by
  rw [Padic.addValuation.apply cast_p_ne_zero, Padic.valuation_p]
  simp

/-- The two-dimensional `(φ, N)`-module: `φ (x, y) = (x, p • y)` and `N (x, y) = (y, 0)`. -/
noncomputable def model : PhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) (ℚ_[p] × ℚ_[p]) where
  φ := (LinearEquiv.refl ℚ_[p] ℚ_[p]).prodCongr
    (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] p cast_p_ne_zero)
  N := LinearMap.inl ℚ_[p] ℚ_[p] ℚ_[p] ∘ₗ LinearMap.snd ℚ_[p] ℚ_[p] ℚ_[p]
  N_φ x := by
    ext <;> simp

/-- `φ e₁ = e₁`. -/
example : (model (p := p)).φ (1, 0) = (1, 0) := by
  simp [model]

/-- `φ e₂ = p • e₂`. -/
example : (model (p := p)).φ (0, 1) = (p : ℚ_[p]) • (0, 1) := by
  simp [model]

/-- `N e₁ = 0`. -/
example : (model (p := p)).N (1, 0) = 0 := by
  simp [model]

/-- `N e₂ = e₁`; in particular `N ≠ 0`. -/
example : (model (p := p)).N (0, 1) = (1, 0) := by
  simp [model]

/-- `N ^ k (φ x) = p ^ k • φ (N ^ k x)`, here for `k = 2`. -/
example (x : ℚ_[p] × ℚ_[p]) :
    ((model (p := p)).N ^ 2) (model.φ x) = (p : ℚ_[p]) ^ 2 • model.φ ((model.N ^ 2) x) :=
  model.N_pow_φ 2 x

/-- The stable image of `N` is a stable subspace. -/
example : (model (p := p)).IsStable (⨅ k, LinearMap.range (model.N ^ k)) :=
  model.isStable_iInf_range_N_pow

/-- `N` restricts to a bijection of its stable image. -/
example : Function.Bijective
    ((model (p := p)).restrict _ model.isStable_iInf_range_N_pow).N :=
  model.bijective_restrict_N_iInf_range_N_pow

/-- The determinant identity `det N = p ^ d * σ (det N)`, with `σ` the identity. -/
example : LinearMap.det (model (p := p)).N =
    (p : ℚ_[p]) ^ Module.finrank ℚ_[p] (ℚ_[p] × ℚ_[p]) * LinearMap.det (model (p := p)).N :=
  model.det_N_eq_pow_mul

/-- The stable image of `N` is zero. -/
example : ⨅ k, LinearMap.range ((model (p := p)).N ^ k) = ⊥ :=
  model.iInf_range_N_pow_eq_bot Padic.addValuation (fun _ => rfl) addValuation_cast_p_ne_zero

/-- The monodromy operator of the model is nilpotent. -/
example : IsNilpotent (model (p := p)).N :=
  PhiNModule.isNilpotent_N model Padic.addValuation (fun _ => rfl) addValuation_cast_p_ne_zero

/-- Every finite-dimensional `(φ, N)`-module over `ℚ_[p]` (with `σ` the identity and the scalar
`p`) whose monodromy operator is bijective is zero. -/
example {D : Type*} [AddCommGroup D] [Module ℚ_[p] D] [FiniteDimensional ℚ_[p] D]
    (M : PhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) D) (hN : Function.Bijective M.N) :
    Subsingleton D :=
  M.subsingleton_of_bijective_N Padic.addValuation (fun _ => rfl) addValuation_cast_p_ne_zero hN

/-- With the scalar `p = 0`, the monodromy operator vanishes. -/
example {D : Type*} [AddCommGroup D] [Module ℚ D] (M : PhiNModule (RingHom.id ℚ) 0 D) :
    M.N = 0 :=
  M.N_eq_zero_of_p_eq_zero rfl

end MathlibExtTest.RingTheory.PhiNModule.Nilpotent
