/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

/-!
# Tests for the Galois action on the de Rham period ring of `ℂ_p`

`p` is not a unit of `𝓞_ℂ_p`, by instance; the action on `𝓞_ℂ_p` is the completed action on `ℂ_p`
and preserves the norm; the action on `W(𝓞_ℂ_p^♭)[1/p]` fixes `ℚ_p`; `𝓞_ℂ_p` is `p`-adically
complete, by instance, as `B_dR^+` needs; the filtration starts at `Fil^0 = B_dR^+` and
decreases; the action on `B_dR^+` extends the action on `W(𝓞_ℂ_p^♭)[1/p]`; `σ ∈ Gal(\bar{ℚ}_p/F)`
acts on `H¹` by inverse image along `id_A × Spec σ`, so the identity element acts by inverse image
along the identity morphism; and `Fil^j D_dR` is the whole fixed submodule of `B_dR^+ ⊗ H¹` for
`j = 0` and decreases.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison
open MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
open MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- `p` is not a unit of `𝓞_ℂ_p`; instance search finds this. -/
example : ¬IsUnit (p : 𝓞_ℂ_[p]) := Fact.out

/-- The elements of `𝓞_ℂ_p` are those of norm at most one: `p` is one of them, `p⁻¹` is not. -/
example : (p : PadicComplex p) ∈ 𝓞_ℂ_[p] := (p : 𝓞_ℂ_[p]).2

example : (p : PadicComplex p)⁻¹ ∉ 𝓞_ℂ_[p] := by
  rw [mem_padicComplexInt_iff, norm_inv, ← map_natCast (algebraMap ℚ_[p] (PadicComplex p)),
    norm_algebraMap', Padic.norm_p, inv_inv, not_le]
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- The action on `𝓞_ℂ_p` is the completed action on `ℂ_p`, and it preserves the norm. -/
example (σ : Galois p) (x : 𝓞_ℂ_[p]) :
    ((integralGalois p σ x : 𝓞_ℂ_[p]) : PadicComplex p) = completionGalois p σ x := rfl

example (σ : Galois p) (x : PadicComplex p) : ‖completionGalois p σ x‖ = ‖x‖ :=
  norm_completionGalois p σ x

/-- The action on `W(𝓞_ℂ_p^♭)[1/p]` fixes `ℚ_p`. -/
example (σ : Galois p) (c : ℚ_[p]) :
    preDeRhamGalois p σ (padicToPreDeRham p c) = padicToPreDeRham p c := by
  rw [← RingHom.comp_apply, preDeRhamGalois_comp_padicToPreDeRham]

/-- The ring of integers of `C = ℂ_p` and `𝓞_ℂ_p` have the same elements. -/
example (x : integers p (padicComplexFieldTest p)) :
    ((integersEquivPadicComplexInt p x : 𝓞_ℂ_[p]) : PadicComplex p) = x.1 := rfl

/-- `𝓞_ℂ_p` is `p`-adically complete; instance search finds this, so `B_dR^+` needs no
completeness hypothesis. -/
example : IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := inferInstance

example : ofPreDeRham p 1 = 1 := map_one _

/-- The completeness of `𝓞_C` for `C = ℂ_p` gives that of `𝓞_ℂ_p`. -/
example (h : IsAdicComplete (Ideal.span {(p : integers p (padicComplexFieldTest p))})
    (integers p (padicComplexFieldTest p))) :
    IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  isAdicComplete_padicComplexInt p h

section Completion

/-- `Fil^0 B_dR^+ = B_dR^+`. -/
example : fil p 0 = ⊤ := by
  have : Subsingleton (PreDeRham p ⧸ thetaKer p ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
  exact eq_top_iff.2 fun x _ => (RingHom.mem_ker).2 (Subsingleton.elim _ _)

/-- The filtration decreases: `Fil^{j + 1} B_dR^+ ⊆ Fil^j B_dR^+`. -/
example (j : ℕ) : fil p (j + 1) ≤ fil p j := fun x hx => by
  rw [fil, RingHom.mem_ker] at hx ⊢
  change AdicCompletion.evalₐ (thetaKer p) j x = 0
  rw [← AdicCompletion.factorPow_evalₐ (thetaKer p) j.le_succ x]
  change Ideal.Quotient.factorPow _ j.le_succ (evalBdR p (j + 1) x) = 0
  rw [hx, map_zero]

/-- The action on `B_dR^+` extends the action on `W(𝓞_ℂ_p^♭)[1/p]` and fixes `ℚ_p`. -/
example (σ : Galois p) (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ))
    (x : PreDeRham p) :
    bdRPlusGaloisLinear p σ h (ofPreDeRham p x) = ofPreDeRham p (preDeRhamGalois p σ x) :=
  bdRPlusGalois_ofPreDeRham p σ h x

example (σ : Galois p) (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) (c : ℚ_[p]) :
    bdRPlusGaloisLinear p σ h (algebraMap ℚ_[p] (BdRPlus p) c) =
      algebraMap ℚ_[p] (BdRPlus p) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  congr 1
  exact map_one (bdRPlusGalois p σ h)

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

variable (h : ∀ τ : Galois p, thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p τ))

/-- `Fil^0 D_dR` is the whole fixed submodule of `B_dR^+ ⊗ H¹`, as `Fil^0 B_dR^+ = B_dR^+`. -/
example : filDeRham p F A h 0 = ⨅ σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p,
    LinearMap.eqLocus (TensorProduct.map (bdRPlusGaloisLinear p (σ.restrictScalars ℚ_[p]) (h _))
      (h1Galois p F A σ)) LinearMap.id := by
  have hfil : fil p 0 = ⊤ := by
    have : Subsingleton (PreDeRham p ⧸ thetaKer p ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    exact eq_top_iff.2 fun x _ => (RingHom.mem_ker).2 (Subsingleton.elim _ _)
  have hsurj : Function.Surjective ((fil p 0).restrictScalars ℚ_[p]).subtype := fun b =>
    ⟨⟨b, by rw [Submodule.restrictScalars_mem, hfil]; trivial⟩, rfl⟩
  refine le_antisymm inf_le_right (le_inf (fun x _ => ?_) le_rfl)
  exact LinearMap.mem_range.2 (TensorProduct.map_surjective hsurj Function.surjective_id x)

/-- `Fil^j D_dR` decreases: `Fil^{j + 1} D_dR ⊆ Fil^j D_dR`. -/
example (j : ℕ) : filDeRham p F A h (j + 1) ≤ filDeRham p F A h j := by
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
