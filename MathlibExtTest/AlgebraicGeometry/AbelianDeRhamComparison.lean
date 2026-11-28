/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison
import MathlibExt.RingTheory.AdicCompletion.Localization

/-!
# Tests for the filtration of `B_dR^+` and `Fil^j D_dR` of `H¹`

The filtration starts at `Fil^0 = B_dR^+` and decreases; `σ ∈ Gal(\bar{ℚ}_p/F)` acts on `H¹` by
inverse image along `id_A × Spec σ`, so the identity element acts by inverse image along the
identity morphism; and `Fil^j D_dR` is the whole fixed submodule of `B_dR^+ ⊗ H¹` for `j = 0` and
decreases.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
open MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

section Completion

/-- `Fil^0 B_dR^+ = B_dR^+`. -/
example : fil p 0 = ⊤ := by
  have : Subsingleton (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸ thetaKer p ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
  exact eq_top_iff.2 fun x _ => (RingHom.mem_ker).2 (Subsingleton.elim _ _)

/-- The filtration decreases: `Fil^{j + 1} B_dR^+ ⊆ Fil^j B_dR^+`. -/
example (j : ℕ) : fil p (j + 1) ≤ fil p j := fun x hx => by
  rw [fil, RingHom.mem_ker] at hx ⊢
  change AdicCompletion.evalₐ (thetaKer p) j x = 0
  rw [← AdicCompletion.factorPow_evalₐ (thetaKer p) j.le_succ x]
  change Ideal.Quotient.factorPow _ j.le_succ (evalBdR p (j + 1) x) = 0
  rw [hx, map_zero]

end Completion

section Cohomology

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (A : Over (Spec (CommRingCat.of F)))

/-- `σ ∈ Gal(\bar{ℚ}_p/F)` acts on `H¹` by inverse image along `id_A × Spec σ`, and the identity
acts by inverse image along the identity of `A_{\bar{ℚ}_p}`. -/
example (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) (a : H1 p F A) :
    h1Galois p F A σ a = galoisCohomologyOperator A (PadicAlgCl p) p σ 1 a := rfl

example : h1Galois p F A 1 =
    continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p)
      (𝟙 (geometricFibre A (PadicAlgCl p))) 1 := by
  rw [h1Galois, galoisSchemeOperator_one]

/-- `Fil^0 D_dR` is the whole fixed submodule of `B_dR^+ ⊗ H¹`, as `Fil^0 B_dR^+ = B_dR^+`. -/
example : filDeRham p F A 0 = ⨅ σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p,
    LinearMap.eqLocus (TensorProduct.map
      (PadicComplexInt.galoisBDeRhamPlus p (σ.restrictScalars ℚ_[p])).toLinearMap
      (h1Galois p F A σ)) LinearMap.id := by
  have hfil : fil p 0 = ⊤ := by
    have : Subsingleton
        (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸ thetaKer p ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    exact eq_top_iff.2 fun x _ => (RingHom.mem_ker).2 (Subsingleton.elim _ _)
  have hsurj : Function.Surjective ((fil p 0).restrictScalars ℚ_[p]).subtype := fun b =>
    ⟨⟨b, by rw [Submodule.restrictScalars_mem, hfil]; trivial⟩, rfl⟩
  refine le_antisymm inf_le_right (le_inf (fun x _ => ?_) le_rfl)
  exact LinearMap.mem_range.2 (TensorProduct.map_surjective hsurj Function.surjective_id x)

/-- `Fil^j D_dR` decreases: `Fil^{j + 1} D_dR ⊆ Fil^j D_dR`. -/
example (j : ℕ) : filDeRham p F A (j + 1) ≤ filDeRham p F A j := by
  have hfil : (fil p (j + 1)).restrictScalars ℚ_[p] ≤ (fil p j).restrictScalars ℚ_[p] :=
    fun x hx => by
      rw [Submodule.restrictScalars_mem, fil, RingHom.mem_ker] at hx ⊢
      change AdicCompletion.evalₐ (thetaKer p) j x = 0
      rw [← AdicCompletion.factorPow_evalₐ (thetaKer p) j.le_succ x]
      change Ideal.Quotient.factorPow _ j.le_succ (evalBdR p (j + 1) x) = 0
      rw [hx, map_zero]
  refine inf_le_inf_right _ ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨TensorProduct.map (Submodule.inclusion hfil) LinearMap.id y, by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, Submodule.subtype_comp_inclusion,
      LinearMap.id_comp]⟩

end Cohomology
