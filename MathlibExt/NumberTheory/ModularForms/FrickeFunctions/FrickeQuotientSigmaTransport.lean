/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean`
and
`P2M/Sol/S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeModularity
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeQuotientMonicRel
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.LevelFractionQExpansionCoeff
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.MDifferentiableDivMonicRel
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.QExpansionSigmaTransport

/-!
# Galois transport of holomorphic Fricke quotients

This file transports holomorphic Fricke quotients along an embedding of `ℚ(ζ_N)`. Throughout,
`j = E₄³ / Δ` and, for `v : Fin 2 → ZMod N`, the Fricke function is `f_v τ = -(E₄ τ E₆ τ / Δ τ)
/ 2592 · (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the Weierstrass function of the lattice
`ℤτ + ℤ`.

## Main statement

* `ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient`
-/
namespace FrickeFunctions.FrickeQuotientSigmaTransport

set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology Polynomial Real.Polynomial

namespace FrickeTransport

local notation "Δ" => ModularForm.discriminant

section Analytic

private theorem differentiableAt_comp_ofComplex {u : ℍ →
    ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) :=
      (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

private theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

end Analytic

section Params

variable {N : ℕ} [NeZero N]
variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)

private abbrev Idx (N : ℕ) : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke (t v.1)

private def genSet : Set (ℍ → ℂ) :=
    insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf t) (MvPolynomial.map ψ R)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

private theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 →
    ZMod N} (hv : v ≠ 0) : ds s v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa [ds] using congrFun h 0
  have h1 : (s : ZMod N) * v 1 = 0 := by simpa [ds] using congrFun h 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : v 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  funext i; fin_cases i <;> simp [h0, h1']

private theorem ev_id_eq (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K id ψ R = MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke v.1)
      (MvPolynomial.map ψ R) := rfl

private theorem ev_ds_eq (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K (ds s) ψ R = MvPolynomial.aeval (fun o : Idx N =>
      o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (MvPolynomial.map ψ R) := rfl

private theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R * S) = ev fricke jf K t ψ R * ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_pow (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) (n : ℕ) :
    ev fricke jf K t ψ (R ^ n) = ev fricke jf K t ψ R ^ n := by
  simp [ev]

private theorem ev_add (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R + S) = ev fricke jf K t ψ R + ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_sum {ι : Type*} (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (S : Finset ι)
    (R : ι → MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (∑ i ∈ S, R i) = ∑ i ∈ S, ev fricke jf K t ψ (R i) := by
  simp [ev, map_sum]

include hL hW hfricke in
private theorem mdifferentiable_fricke {v : Fin 2 →
    ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) :=
  ModularForm.mdifferentiable_frickeFunction N L hL W hW fricke hfricke hv

include hL hW hfricke in
private theorem isBoundedAtImInfty_fricke {v : Fin 2 →
    ZMod N} (hv : v ≠ 0) : IsBoundedAtImInfty (fricke v * Δ) :=
  ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant N L hL W hW fricke hfricke hv

include hL hW hfricke hK in
private theorem periodic_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    Periodic ((fricke v * Δ) ∘ ofComplex) N ∧ ∀ n : ℕ, (qExpansion N (fricke v * Δ)).coeff n ∈ K :=
        by
  subst hK
  exact ⟨ModularForm.periodic_frickeFunction_mul_discriminant N L hL W hW fricke hfricke hv,
    ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem N L hL W hW fricke hfricke
      hv⟩

include hL hW hfricke hK hs hφ in
private theorem coeff_fricke_ds {v : Fin 2 → ZMod N} (hv : v ≠ 0) (n : ℕ) (z : K)
    (hz : (z : ℂ) = (qExpansion N (fricke v * Δ)).coeff n) :
    (qExpansion N (fricke (ds s v) * Δ)).coeff n = φ z := by
  subst hK
  exact ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_sigmaTransport N L hL W hW
    fricke hfricke hs φ hφ hv n z hz

include hjf in
private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ := funext hjf
  rw [this]
  intro τ
  exact ((E₄.holo' τ).pow 3).div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

include hL hW hfricke hjf in
private theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v,
    v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf t o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke (ht v.1 v.2)

include hL hW hfricke hjf in
private theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v,
    v ≠ 0 → t v ≠ 0)
    (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ev fricke jf K t ψ
        R) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (mdifferentiable_gen L hL W hW fricke hfricke jf hjf t ht o)

private theorem gen_mem_genSet (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v,
    v ≠ 0 → t v ≠ 0) (o : Idx N) :
    gen fricke jf t o ∈ genSet (N := N) fricke jf := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨t v.1, ht v.1 v.2, rfl⟩

private theorem ev_mem_adjoin (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ R ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_mem_genSet fricke jf t ht o))

include hK hφ in
private theorem phi_mem (z : K) : φ z ∈ K := by
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hζK : ζ ∈ K := by rw [hK]; exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hzmem : (z : ℂ) ∈ (Polynomial.aeval ζ : ℚ[X] →ₐ[ℚ] ℂ).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
        ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      IntermediateField.mem_toSubalgebra, ← hK]
    exact z.2
  obtain ⟨p, hp⟩ := hzmem
  let ζK : K := ⟨ζ, hζK⟩
  have hz : z = Polynomial.aeval ζK p := by
    apply Subtype.ext
    change (z : ℂ) = (IntermediateField.val K) (Polynomial.aeval ζK p)
    rw [← Polynomial.aeval_algHom_apply]
    exact hp.symm
  have hφz : φ z = Polynomial.aeval (ζ ^ s) p := by
    rw [hz, ← RingHom.toRatAlgHom_apply φ, ← Polynomial.aeval_algHom_apply,
        RingHom.toRatAlgHom_apply,
      hφ ζK rfl]
  rw [hφz]
  have hle : Algebra.adjoin ℚ {ζ ^ s} ≤ K.toSubalgebra := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact pow_mem hζK s
  exact hle (Polynomial.aeval_mem_adjoin_singleton ℚ _)

include hK hφ in
private theorem exists_phiK : ∃ φK : K →+* K, (algebraMap K ℂ).comp φK = φ := by
  refine ⟨{ toFun := fun z => ⟨φ z, phi_mem K hK s φ hφ z⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun x y => Subtype.ext (by simp)
            map_zero' := Subtype.ext (by simp)
            map_add' := fun x y => Subtype.ext (by simp) }, ?_⟩
  ext z
  rfl

private def dsIdx (hs : s.Coprime N) : Idx N → Idx N :=
    fun o => o.map fun v => ⟨ds s v.1, ds_ne_zero hs v.2⟩

private theorem gen_comp_dsIdx : gen fricke jf id ∘ dsIdx s hs = gen fricke jf (ds s) := by
  funext o; cases o <;> rfl

private theorem ev_ds_eq_ev_id {φK : K →+* K} (hφK : (algebraMap K ℂ).comp φK
    = φ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K (ds s) φ R =
      ev fricke jf K id (algebraMap K ℂ) (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK
          R)) := by
  rw [ev, ev, MvPolynomial.map_rename, MvPolynomial.aeval_rename, gen_comp_dsIdx,
      MvPolynomial.map_map, hφK]

section Width

variable (N)

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ,
    (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  have h4 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩
  have h6 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩
  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using h4
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using h6
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

private theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ,
    (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc n]
  split_ifs with h
  · exact qExpansion_disc_rat_one _
  · exact ⟨0, by simp⟩

private theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

private theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ →
    ℂ} (h : RatAt N K m g) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

private theorem RatAt.analyticAt {m : ℕ} {g : ℍ →
    ℂ} (h : RatAt N K m g) : AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

private theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

private theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem K r

private theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ →
    ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

private theorem RatAt.exists_map {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m) := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h.mem n⟩, ?_⟩
  ext n
  rw [PowerSeries.coeff_map]
  erw [PowerSeries.coeff_mk]
  rw [IntermediateField.algebraMap_apply]

private theorem RatAt.qExpansion_ne_zero {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) (hg : g ≠ 0) :
    qExpansion N (g * Δ ^ m) ≠ 0 := by
  rw [Ne, qExpansion_eq_zero_iff (natCast_pos N) h.periodic h.mdiff_mul h.bdd]
  intro h0
  apply hg
  funext τ
  have := congrFun h0 τ
  simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (disc_pow_ne_zero m τ)

private theorem exists_discSeries : ∃ δ : PowerSeries K,
    δ.map (algebraMap K ℂ) = qExpansion N (Δ : ℍ → ℂ) ∧
    δ.map φ = qExpansion N (Δ : ℍ → ℂ) := by
  choose r hr using qExpansion_disc_rat N
  refine ⟨PowerSeries.mk fun n => ⟨(r n : ℂ), ratCast_mem K (r n)⟩, ?_, ?_⟩
  · ext n; simp [hr n]
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hr n]
    have : (⟨(r n : ℂ), ratCast_mem K (r n)⟩ : K) = algebraMap ℚ K (r n) := by
      apply Subtype.ext; rfl
    rw [this, ← RingHom.comp_apply, eq_ratCast]

end Width

section TRel

private def TRel (g g' : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
    ∃ m : ℕ,
      (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
      (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
      ∀ (n : ℕ) (z : K),
        (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
        (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z

include hK hφ in
private theorem transportPkg :
    (∀ {ι : Type} (g g' : ι → ℍ → ℂ), (∀ i : ι, TRel (N := N) K φ (g i) (g' i)) →
      ∀ R : MvPolynomial ι K,
        TRel (N := N) K φ (MvPolynomial.aeval g (MvPolynomial.map (algebraMap K ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map φ R))) ∧
    (∀ g g' : ℍ → ℂ, TRel (N := N) K φ g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf' : ℍ → ℂ, (∀ τ : ℍ, jf' τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) →
      TRel (N := N) K φ jf' jf' :=
  ModularForm.qExpansion_sigmaTransport_package N K φ (phi_mem K hK s φ hφ) (TRel (N := N) K φ)
    (fun g g' => Iff.rfl)

include hL hW hfricke hK hs hφ in
private theorem tRel_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : TRel (N :=
    N) K φ (fricke v) (fricke (ds s v)) := by
  have hv' : ds s v ≠ 0 := ds_ne_zero hs hv
  obtain ⟨hp, hm⟩ := periodic_fricke L hL W hW fricke hfricke K hK hv
  obtain ⟨hp', hm'⟩ := periodic_fricke L hL W hW fricke hfricke K hK hv'
  refine ⟨mdifferentiable_fricke L hL W hW fricke hfricke hv,
      mdifferentiable_fricke L hL W hW fricke hfricke hv',
    1, ?_, ?_, ?_⟩
  · rw [pow_one]; exact ⟨hp, isBoundedAtImInfty_fricke L hL W hW fricke hfricke hv, hm⟩
  · rw [pow_one]; exact ⟨hp', isBoundedAtImInfty_fricke L hL W hW fricke hfricke hv', hm'⟩
  · intro n z hz
    rw [pow_one] at hz ⊢
    exact coeff_fricke_ds L hL W hW fricke hfricke K hK s hs φ hφ hv n z hz

include hL hW hfricke hjf hK hs hφ in
private theorem tRel_gen (o : Idx N) : TRel (N :=
    N) K φ (gen fricke jf id o) (gen fricke jf (ds s) o) := by
  cases o with
  | none => exact (transportPkg K hK s φ hφ).2.2 jf hjf
  | some v => exact tRel_fricke L hL W hW fricke hfricke K hK s hs φ hφ v.2

include hL hW hfricke hjf hK hs hφ in
private theorem tRel_ev (R : MvPolynomial (Idx N) K) :
    TRel (N := N) K φ (ev fricke jf K id (algebraMap K ℂ) R) (ev fricke jf K (ds s) φ R) :=
  (transportPkg K hK s φ hφ).1 _ _ (tRel_gen L hL W hW fricke hfricke jf hjf K hK s hs φ hφ) R

include hK hφ in
private theorem tRel_zero_iff {g g' : ℍ → ℂ} (h : TRel (N := N) K φ g g') : g = 0 ↔ g' = 0 :=
  (transportPkg K hK s φ hφ).2.1 g g' h

private theorem TRel.lift {g g' : ℍ → ℂ} (h : TRel (N := N) K φ g g') :
    ∃ m : ℕ, RatAt N K m g ∧ RatAt N K m g' ∧ ∀ M : ℕ, m ≤ M →
      ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ M) ∧
        p.map φ = qExpansion N (g' * Δ ^ M) := by
  obtain ⟨hg, hg', m, ⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, h4⟩ := h
  have hR : RatAt N K m g := ⟨hg, h1, h2, h3⟩
  have hR' : RatAt N K m g' := ⟨hg', h1', h2', h3'⟩
  refine ⟨m, hR, hR', ?_⟩
  intro M hM
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  obtain ⟨p₀, hp₀⟩ := hR.exists_map
  have hp₀' : p₀.map φ = qExpansion N (g' * Δ ^ m) := by
    ext n
    rw [PowerSeries.coeff_map]
    symm
    apply h4
    rw [← hp₀, PowerSeries.coeff_map]
    rfl
  obtain ⟨δ, hδ, hδ'⟩ := exists_discSeries (N := N) (K := K) φ
  refine ⟨p₀ * δ ^ d, ?_, ?_⟩
  · induction d with
    | zero => simpa using hp₀
    | succ d ih =>
        have hRd : RatAt N K (m + d) g := hR.of_le (Nat.le_add_right _ _)
        rw [pow_succ, ← mul_assoc, map_mul, ih (Nat.le_add_right _ _), hδ, ← add_assoc, pow_succ,
          ← mul_assoc, qExpansion_mul hRd.analyticAt analyticAt_disc]
  · induction d with
    | zero => simpa using hp₀'
    | succ d ih =>
        have hRd : RatAt N K (m + d) g' := hR'.of_le (Nat.le_add_right _ _)
        rw [pow_succ, ← mul_assoc, map_mul, ih (Nat.le_add_right _ _), hδ', ← add_assoc, pow_succ,
          ← mul_assoc, qExpansion_mul hRd.analyticAt analyticAt_disc]

end TRel

section Construction

variable {L hL W hW fricke hfricke jf hjf K hK s hs φ hφ}
variable (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (P Q : MvPolynomial (Idx N) K)
    (hQ0 : ev fricke jf K id (algebraMap K ℂ) Q ≠ 0)
    (hGQ : G * ev fricke jf K id (algebraMap K ℂ) Q = ev fricke jf K id (algebraMap K ℂ) P)

local notation "𝔢" => ev fricke jf K id (algebraMap K ℂ)
local notation "𝔢'" => ev fricke jf K (ds s) φ

private def toIdxPoly (p : ℂ[X]) (hp : ∀ n, p.coeff n ∈ K) : MvPolynomial (Idx N) K :=
  ∑ n ∈ p.support, MvPolynomial.C (⟨p.coeff n, hp n⟩ : K) * MvPolynomial.X none ^ n

private theorem ev_toIdxPoly (p : ℂ[X]) (hp : ∀ n, p.coeff n ∈ K) :
    𝔢 (toIdxPoly p hp) = fun τ => p.eval (jf τ) := by
  funext τ
  rw [toIdxPoly, ev_sum, Finset.sum_apply, Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ev_mul, ev_pow]
  simp only [ev, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Pi.mul_apply, Pi.pow_apply]
  rfl

include hL hW hfricke hjf hK hs hφ hG hQ0 hGQ in
private theorem exists_transport : 𝔢' Q ≠ 0 ∧ ∃ G' : ℍ → ℂ,
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧ G' * 𝔢' Q = 𝔢' P := by
  classical
  have hQ'0 : 𝔢' Q ≠ 0 := fun h0 =>
    hQ0 ((tRel_zero_iff K hK s φ hφ (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ Q)).2
        h0)
  refine ⟨hQ'0, ?_⟩
  obtain ⟨d, p, hpK, hrel⟩ :=
      ModularForm.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke
    hfricke jf hjf K hK G hG P Q hQ0 hGQ
  let a : Fin d → MvPolynomial (Idx N) K := fun i => toIdxPoly (p i) (hpK i)
  let Rrel : MvPolynomial (Idx N) K := P ^ d + ∑ i : Fin d, a i * Q ^ (d - (i : ℕ)) * P ^ (i : ℕ)
  have hRrel : 𝔢 Rrel = 0 := by
    funext τ
    have h1 := hrel τ
    have hGQτ : G τ * 𝔢 Q τ = 𝔢 P τ := by
      have := congrFun hGQ τ; simpa only [Pi.mul_apply] using this
    have hev : 𝔢 Rrel τ = 𝔢 P τ ^ d + ∑ i : Fin d,
        (p i).eval (jf τ) * 𝔢 Q τ ^ (d - (i : ℕ)) * 𝔢 P τ ^ (i : ℕ) := by
      simp only [Rrel, ev_add, ev_pow, ev_sum, ev_mul, Pi.add_apply, Pi.pow_apply, Finset.sum_apply,
        Pi.mul_apply, a, ev_toIdxPoly]
    rw [hev, Pi.zero_apply, ← hGQτ]
    have key : (G τ * 𝔢 Q τ) ^ d + ∑ i : Fin d,
        (p i).eval (jf τ) * 𝔢 Q τ ^ (d - (i : ℕ)) * (G τ * 𝔢 Q τ) ^ (i : ℕ)
        = (G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ)) * 𝔢 Q τ ^ d := by
      rw [add_mul, Finset.sum_mul, mul_pow]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (i : ℕ) ≤ d := i.2.le
      rw [mul_pow, show 𝔢 Q τ ^ d = 𝔢 Q τ ^ (i : ℕ) * 𝔢 Q τ ^ (d - (i : ℕ)) by
        rw [← pow_add, Nat.add_sub_cancel' hi]]
      ring
    rw [key, h1, zero_mul]
  have hRrel' : 𝔢' Rrel = 0 :=
    (tRel_zero_iff K hK s φ hφ (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ Rrel)).1
        hRrel
  let c : ℕ → ℍ → ℂ := fun n => if h : n < d then 𝔢' (a ⟨n, h⟩) else 0
  have hc : ∀ n < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c n) := by
    intro n hn
    simp only [c, dite_eq_left hn]
    exact mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv =>
        ds_ne_zero hs hv) φ _
  have hmonic : 𝔢' P ^ d + ∑ n ∈ Finset.range d, c n * 𝔢' Q ^ (d - n) * 𝔢' P ^ n = 0 := by
    have hev : 𝔢' Rrel = 𝔢' P ^ d + ∑ i : Fin d,
        𝔢' (a i) * 𝔢' Q ^ (d - (i : ℕ)) * 𝔢' P ^ (i : ℕ) := by
      simp only [Rrel, ev_add, ev_pow, ev_sum, ev_mul]
    rw [hev] at hRrel'
    rw [← hRrel', Finset.sum_range (fun n => c n * 𝔢' Q ^ (d - n) * 𝔢' P ^ n)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c, dite_eq_left i.2]
  exact UpperHalfPlane.exists_mdifferentiable_div_of_monicRel
    (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ P)
    (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ Q)
    hQ'0 hc hmonic

include hL hW hfricke hjf hK in
private theorem exists_ratAt_of_quotient {u : ℍ →
    ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (P₁ Q₁ : MvPolynomial (Idx N) K)
    (hQ₁ : 𝔢 Q₁ ≠ 0) (huQ : u * 𝔢 Q₁ = 𝔢 P₁) : ∃ m, RatAt N K m u := by
  have hint :=
      ModularForm.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke hfricke
      jf hjf
    K hK u hu P₁ Q₁ hQ₁ huQ
  have hcoef : ∀ (R : MvPolynomial (Idx N) K) (mo : Idx N →₀ ℕ),
      (MvPolynomial.map (algebraMap K ℂ) R).coeff mo ∈ K := by
    intro R mo; rw [MvPolynomial.coeff_map]; exact (R.coeff mo).2
  obtain ⟨m, hper, hbdd, hmem⟩ :=
      ModularForm.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N L hL
    W hW fricke hfricke jf hjf K hK hu (MvPolynomial.map (algebraMap K ℂ) P₁)
    (MvPolynomial.map (algebraMap K ℂ) Q₁) (hcoef P₁) (hcoef Q₁) hQ₁ huQ hint
  exact ⟨m, ⟨hu, hper, hbdd, hmem⟩⟩

include hL hW hfricke hjf hK hs hφ hG hQ0 hGQ in
private theorem tRel_of_transport {G' : ℍ →
    ℂ} (hG' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G') (hG'Q : G' * 𝔢' Q = 𝔢' P) :
    TRel (N := N) K φ G G' := by
  classical
  obtain ⟨hQ'0, -⟩ := exists_transport (hL := hL) (hW := hW) (hfricke := hfricke) (hjf :=
      hjf) (hK := hK)
    (hs := hs) (hφ := hφ) G hG P Q hQ0 hGQ
  obtain ⟨mG, hRG⟩ := exists_ratAt_of_quotient (hL := hL) (hW := hW) (hfricke := hfricke) (hjf :=
      hjf)
    (hK := hK) hG P Q hQ0 hGQ
  obtain ⟨φK, hφK⟩ := exists_phiK K hK s φ hφ
  have hQ₁ : 𝔢 (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK Q)) ≠ 0 := by
    rw [← ev_ds_eq_ev_id fricke jf K s hs φ hφK]; exact hQ'0
  have hG'Q₁ : G' * 𝔢 (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK Q)) =
      𝔢 (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK P)) := by
    rw [← ev_ds_eq_ev_id fricke jf K s hs φ hφK,
        ← ev_ds_eq_ev_id fricke jf K s hs φ hφK]; exact hG'Q
  obtain ⟨mG', hRG'⟩ := exists_ratAt_of_quotient (hL := hL) (hW := hW) (hfricke := hfricke) (hjf :=
      hjf)
    (hK := hK) hG' _ _ hQ₁ hG'Q₁
  obtain ⟨mQ, hRQ, hRQ', hQlift⟩ := (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ Q).lift
  obtain ⟨mP, -, -, hPlift⟩ := (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ P).lift
  set M : ℕ := mG + mG' + mQ + mP with hM
  have hRGM : RatAt N K M G := hRG.of_le (by omega)
  have hRG'M : RatAt N K M G' := hRG'.of_le (by omega)
  have hRQM : RatAt N K M (𝔢 Q) := hRQ.of_le (by omega)
  have hRQ'M : RatAt N K M (𝔢' Q) := hRQ'.of_le (by omega)
  obtain ⟨pQ, hpQ, hpQ'⟩ := hQlift M (by omega)
  obtain ⟨pP, hpP, hpP'⟩ := hPlift (M + M) (by omega)
  obtain ⟨pG, hpG⟩ := hRGM.exists_map
  have hsplit : ∀ u w : ℍ → ℂ, u * w * Δ ^ (M + M) = (u * Δ ^ M) * (w * Δ ^ M) := by
    intro u w; rw [pow_add]; ring
  have hprod : pG * pQ = pP := by
    apply PowerSeries.map_injective (algebraMap K ℂ) Subtype.val_injective
    rw [map_mul, hpG, hpQ, hpP, ← hGQ, hsplit, qExpansion_mul hRGM.analyticAt hRQM.analyticAt]
  have hG'exp : qExpansion N (G' * Δ ^ M) = pG.map φ := by
    have h1 : qExpansion N (G' * Δ ^ M) * qExpansion N (𝔢' Q * Δ ^ M) = pG.map φ
        * qExpansion N (𝔢' Q * Δ ^ M) := by
      rw [← qExpansion_mul hRG'M.analyticAt hRQ'M.analyticAt, ← hsplit, hG'Q, ← hpP', ← hprod,
          map_mul, hpQ']
    have hne : qExpansion N (𝔢' Q * Δ ^ M) ≠ 0 := hRQ'M.qExpansion_ne_zero hQ'0
    exact mul_right_cancel₀ hne h1
  refine ⟨hG, hG', M, ⟨hRGM.periodic, hRGM.bdd, hRGM.mem⟩, ⟨hRG'M.periodic, hRG'M.bdd, hRG'M.mem⟩,
      ?_⟩
  intro n z hz
  have hz' : z = PowerSeries.coeff n pG := by
    apply Subtype.val_injective
    change (z : ℂ) = ((PowerSeries.coeff n pG : K) : ℂ)
    rw [hz, ← hpG, PowerSeries.coeff_map]
    rfl
  rw [hG'exp, PowerSeries.coeff_map, hz']

end Construction

end Params

end FrickeTransport

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/-- Let `K = ℚ(ζ_N)`, `s` coprime to `N`, and `φ : K →+* ℂ` with `φ ζ_N = ζ_N ^ s`. Let `G` be
holomorphic with `G Q = P` after evaluating polynomials `P`, `Q` over `K` at `j` and the Fricke
functions, `Q ≠ 0`. Evaluate `Q.map φ` and `P.map φ` at `j` and the transported Fricke
functions `f_{(v₀, s v₁)}`. Then the first is nonzero, and there is a holomorphic `G'` with `G'
(Q.map φ) = P.map φ`; moreover, for all large `M`, `G Δ ^ M` and `G' Δ ^ M` are `N`-periodic,
bounded at `i∞` and `K`-rational, and `φ` maps the q-coefficients of `G Δ ^ M` to those of `G'
Δ ^ M`. -/
public theorem _root_.ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ))) :
    MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      G' * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) =
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) ∧
      ∃ m : ℕ, ∀ M : ℕ, m ≤ M →
        (Function.Periodic ((G * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
          IsBoundedAtImInfty (G * ModularForm.discriminant ^ M) ∧
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
        (Function.Periodic ((G' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
          IsBoundedAtImInfty (G' * ModularForm.discriminant ^ M) ∧
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G' * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
        ∀ (n : ℕ) (z : ↥K),
          (z : ℂ) = (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ M)).coeff n →
          (UpperHalfPlane.qExpansion N (G' * ModularForm.discriminant ^ M)).coeff n = φ z := by
  obtain ⟨hQ'0, G', hG', hG'Q⟩ := FrickeTransport.exists_transport (hL := hL) (hW :=
      hW) (hfricke := hfricke)
    (hjf := hjf) (hK := hK) (hs := hs) (hφ := hφ) G hG P Q hQ0 hGQ
  have hT := FrickeTransport.tRel_of_transport (hL := hL) (hW := hW) (hfricke := hfricke) (hjf :=
      hjf)
    (hK := hK) (hs := hs) (hφ := hφ) G hG P Q hQ0 hGQ hG' hG'Q
  obtain ⟨m, hR, hR', hlift⟩ := hT.lift
  refine ⟨hQ'0, G', hG', hG'Q, m, fun M hM => ?_⟩
  have hRM := hR.of_le hM
  have hRM' := hR'.of_le hM
  obtain ⟨p, hp, hp'⟩ := hlift M hM
  refine ⟨⟨hRM.periodic, hRM.bdd, hRM.mem⟩, ⟨hRM'.periodic, hRM'.bdd, hRM'.mem⟩, fun n z hz => ?_⟩
  have hz' : z = PowerSeries.coeff n p := by
    apply Subtype.val_injective
    change (z : ℂ) = ((PowerSeries.coeff n p : K) : ℂ)
    rw [hz, ← hp, PowerSeries.coeff_map]
    rfl
  rw [← hp', PowerSeries.coeff_map, hz']

end FrickeQuotientSigmaTransport

end FrickeFunctions
