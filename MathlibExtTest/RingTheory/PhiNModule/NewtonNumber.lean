/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.NewtonNumber
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Tests for the Newton number of a `(φ, N)`-module

We test the API on `φ`-modules over `ℚ_[p] = W(𝔽_p)[1/p]`, whose absolute Frobenius is the
identity, with the `p`-adic valuation `Padic.addValuation`: the rank-one modules `ℚ_[p]` with
`φ x = c * x`, whose Newton number is `v_p(c)`, and the rank-two modules `ℚ_[p] × ℚ_[p]` with
`φ (x, y) = (c₁ * x, c₂ * y)`, whose Newton number is `v_p(c₁) + v_p(c₂)`.
-/

open Module PhiNModule

namespace MathlibExtTest.RingTheory.PhiNModule.NewtonNumber

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic valuation is invariant under the absolute Frobenius `RingHom.id ℚ_[p]`. -/
theorem padic_hv (x : ℚ_[p]) : Padic.addValuation (RingHom.id ℚ_[p] x) = Padic.addValuation x :=
  rfl

/-- The prime `p` is nonzero in `ℚ_[p]`. -/
theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The rank-one `φ`-module `ℚ_[p]` with `φ x = c * x`, for `c ≠ 0`. -/
noncomputable abbrev rankOne (c : ℚ_[p]) (hc : c ≠ 0) :
    PhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) ℚ_[p] :=
  ofPhi (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] c hc)

/-- The Newton number of `rankOne c hc`, computed in the basis `{1}`, is `v_p(c)`. -/
theorem coe_newtonNumber_rankOne (c : ℚ_[p]) (hc : c ≠ 0) :
    ((rankOne c hc).newtonNumber Padic.addValuation : WithTop ℤ) = Padic.addValuation c := by
  rw [coe_newtonNumber _ padic_hv _ (Basis.singleton (Fin 1) ℚ_[p]), Basis.det_apply,
    Matrix.det_unique]
  simp [Basis.toMatrix_apply]

/-- The Newton number of `rankOne c hc` is the `p`-adic valuation of `c`. -/
theorem newtonNumber_rankOne (c : ℚ_[p]) (hc : c ≠ 0) :
    (rankOne c hc).newtonNumber Padic.addValuation = c.valuation := by
  have h := coe_newtonNumber_rankOne c hc
  rw [Padic.addValuation.apply hc] at h
  exact_mod_cast h

/-- `φ = p ^ m • id` on `ℚ_[p]` has Newton number `m`. -/
example (m : ℕ) :
    (rankOne ((p : ℚ_[p]) ^ m) (pow_ne_zero m p_ne_zero)).newtonNumber Padic.addValuation = m := by
  rw [newtonNumber_rankOne, Padic.valuation_pow, Padic.valuation_p, mul_one]

/-- The basis-independence statement, for bases indexed by different types. -/
example (f : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p]) :
    Padic.addValuation ((Basis.singleton (Fin 1) ℚ_[p]).det (f ∘ Basis.singleton (Fin 1) ℚ_[p])) =
      Padic.addValuation ((Basis.singleton Unit ℚ_[p]).det (f ∘ Basis.singleton Unit ℚ_[p])) :=
  Basis.addValuation_det_compₛₗ_eq _ padic_hv _ _ f

/-- The determinant of the matrix of `φ` in a basis is nonzero. -/
example (c : ℚ_[p]) (hc : c ≠ 0) :
    (Basis.singleton Unit ℚ_[p]).det ((rankOne c hc).φ ∘ Basis.singleton Unit ℚ_[p]) ≠ 0 :=
  det_comp_φ_ne_zero _ _

/-- The rank-two `φ`-module `ℚ_[p] × ℚ_[p]` with `φ (x, y) = (c₁ * x, c₂ * y)`, for `c₁ ≠ 0` and
`c₂ ≠ 0`. -/
noncomputable abbrev rankTwo (c₁ c₂ : ℚ_[p]) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    PhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) (ℚ_[p] × ℚ_[p]) :=
  ofPhi ((LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] c₁ h₁).prodCongr
    (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] c₂ h₂))

/-- Additivity along the exact sequence `0 → ℚ_[p] → ℚ_[p] × ℚ_[p] → ℚ_[p] → 0`: the Newton
number of `rankTwo c₁ c₂ h₁ h₂` is the sum of those of `rankOne c₁ h₁` and `rankOne c₂ h₂`. -/
theorem newtonNumber_rankTwo (c₁ c₂ : ℚ_[p]) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (rankTwo c₁ c₂ h₁ h₂).newtonNumber Padic.addValuation =
      (rankOne c₁ h₁).newtonNumber Padic.addValuation +
        (rankOne c₂ h₂).newtonNumber Padic.addValuation :=
  newtonNumber_eq_add_of_exact _ padic_hv (f := LinearMap.inl ℚ_[p] ℚ_[p] ℚ_[p])
    (g := LinearMap.snd ℚ_[p] ℚ_[p] ℚ_[p]) LinearMap.inl_injective LinearMap.snd_surjective
    Function.Exact.inl_snd (fun x => by simp) (fun x => by simp)

/-- The rank-two module with slopes `1` and `0` has Newton number `1`. -/
example : (rankTwo (p : ℚ_[p]) 1 p_ne_zero one_ne_zero).newtonNumber Padic.addValuation = 1 := by
  rw [newtonNumber_rankTwo, newtonNumber_rankOne, newtonNumber_rankOne, Padic.valuation_p,
    Padic.valuation_one, add_zero]

/-- A direct computation in the basis `(1, 0), (0, 1)`: the Newton number of
`rankTwo c₁ c₂ h₁ h₂` is `v_p(c₁ * c₂)`. -/
example (c₁ c₂ : ℚ_[p]) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    ((rankTwo c₁ c₂ h₁ h₂).newtonNumber Padic.addValuation : WithTop ℤ) =
      Padic.addValuation (c₁ * c₂) := by
  rw [coe_newtonNumber _ padic_hv _ (Basis.finTwoProd ℚ_[p]), Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]

/-- Invariance under the isomorphism swapping the factors of `ℚ_[p] × ℚ_[p]`. -/
example (c₁ c₂ : ℚ_[p]) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (rankTwo c₁ c₂ h₁ h₂).newtonNumber Padic.addValuation =
      (rankTwo c₂ c₁ h₂ h₁).newtonNumber Padic.addValuation :=
  newtonNumber_eq_of_linearEquiv _ padic_hv _ _ (LinearEquiv.prodComm ℚ_[p] ℚ_[p] ℚ_[p])
    fun x => by simp

/-- Additivity for a stable subspace, here the whole space. -/
example (M : PhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) (ℚ_[p] × ℚ_[p])) :
    M.newtonNumber Padic.addValuation =
      (M.restrict ⊤ isStable_top).newtonNumber Padic.addValuation +
        (M.quotient ⊤ isStable_top).newtonNumber Padic.addValuation :=
  newtonNumber_eq_restrict_add_quotient _ padic_hv M ⊤ isStable_top

/-- On the top exterior power of `rankOne c hc`, `φ` multiplies the wedge of a basis by `c`. -/
example (c : ℚ_[p]) (hc : c ≠ 0) (b : Basis (Fin (finrank ℚ_[p] ℚ_[p])) ℚ_[p] ℚ_[p]) :
    ExteriorAlgebra.powMapₛₗ (finrank ℚ_[p] ℚ_[p]) (RingHom.id ℚ_[p])
        ((rankOne c hc).φ : ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p]) (exteriorPower.ιMulti ℚ_[p] _ b) =
      c • exteriorPower.ιMulti ℚ_[p] _ b := by
  rw [powMapₛₗ_ιMulti]
  congr 1
  have h : ((rankOne c hc).φ ∘ b) = fun i => c • b i := rfl
  rw [h, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, finrank_self, pow_one]

/-- The map induced by `φ` on the top exterior power has an eigenvector. -/
example (c : ℚ_[p]) (hc : c ≠ 0) :
    ∃ e : ⋀[ℚ_[p]]^(finrank ℚ_[p] ℚ_[p]) ℚ_[p], e ≠ 0 ∧ ∃ d : ℚ_[p],
      ExteriorAlgebra.powMapₛₗ (finrank ℚ_[p] ℚ_[p]) (RingHom.id ℚ_[p])
        ((rankOne c hc).φ : ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p]) e = d • e :=
  exists_powMapₛₗ_eq_smul _

/-- Every eigenvalue of `φ` on the top exterior power of `rankOne c hc` has valuation `v_p(c)`. -/
example (c : ℚ_[p]) (hc : c ≠ 0) {e : ⋀[ℚ_[p]]^(finrank ℚ_[p] ℚ_[p]) ℚ_[p]} (he : e ≠ 0)
    {d : ℚ_[p]}
    (hd : ExteriorAlgebra.powMapₛₗ (finrank ℚ_[p] ℚ_[p]) (RingHom.id ℚ_[p])
      ((rankOne c hc).φ : ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p]) e = d • e) :
    Padic.addValuation d = Padic.addValuation c := by
  rw [← coe_newtonNumber_eq_of_powMapₛₗ _ padic_hv _ he hd, coe_newtonNumber_rankOne]

/-- A zero-dimensional `(φ, N)`-module has Newton number `0`. -/
example :
    (ofPhi (p := (p : ℚ_[p])) (LinearEquiv.refl ℚ_[p] (Fin 0 → ℚ_[p]))).newtonNumber
      Padic.addValuation = 0 :=
  newtonNumber_eq_zero_of_finrank_eq_zero _ _ (Module.finrank_fin_fun ℚ_[p])

end MathlibExtTest.RingTheory.PhiNModule.NewtonNumber
