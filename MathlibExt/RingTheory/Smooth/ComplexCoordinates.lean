/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential.lean`,
`P2M/Sol/S_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential.lean`,
`Theorems/Thm_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean`,
`P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean`,
`Theorems/Thm_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial.lean`,
`P2M/Sol/S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial.lean`,
`Theorems/Thm_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi.lean`
and
`P2M/Sol/S_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi.lean`
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Complex-analytic coordinates on a smooth algebra

Let `S` be a smooth `ℂ`-algebra that is a domain, `σ₀ : S →ₐ[ℂ] ℂ` a point, and `n` the
rank of `Ω[S⁄ℂ]`. If the differentials of `n` elements span the cotangent space at `σ₀`, so
that they form a basis of it, then `σ₀` has a neighbourhood on which evaluation at those
elements is a bijection onto a ball, and every element of `S` is given by a differentiable
function of those evaluations. The count matters: for `S = ℂ[X]`, the differentials of
`(X, X)` span the cotangent space, but evaluation at `(X, X)` lands in the diagonal of `ℂ²`,
which contains no ball.
-/

@[expose] public section

open Topology Polynomial TensorProduct

namespace SmoothComplexCoordinatesAux

universe u

variable {S : Type u} [CommRing S]

private theorem rankAtStalk_eq [IsDomain S] {M : Type u} [AddCommGroup M] [Module S M]
  [Module.FinitePresentation S M]
    [Module.Flat S M] {n : ℕ} (hrank : Module.rank S M = n) (p : PrimeSpectrum S) :
      Module.rankAtStalk M p = n := by
  rw [(Module.isLocallyConstant_rankAtStalk (R := S) (M := M)).apply_eq_of_preconnectedSpace p ⟨⊥,
    Ideal.isPrime_bot⟩]
  have hle : (⊥ : Ideal S).primeCompl ≤ nonZeroDivisors S := by
    intro x hx
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hx (h0 ▸ (Submodule.zero_mem ⊥ : (0 : S) ∈ (⊥ :
      Ideal S))))
  have hr : Module.rank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal
    S).primeCompl M) = n := by
    rw [IsLocalization.rank_eq (S := Localization.AtPrime (⊥ : Ideal S)) (p := (⊥ : Ideal
      S).primeCompl) (hp := hle),
      IsLocalizedModule.rank_eq (p := (⊥ : Ideal S).primeCompl) (f := LocalizedModule.mkLinearMap (⊥
        : Ideal S).primeCompl M)
        (hp := hle), hrank]
  change Module.finrank (Localization.AtPrime (⊥ : Ideal S))
    (LocalizedModule (⊥ : Ideal S).primeCompl M) = n
  exact Module.finrank_eq_of_rank_eq (by rw [hr])

private theorem exists_smul_mem_of_mk_mem {M : Type u} [AddCommGroup M] [Module S M] (𝔭 : Ideal S)
  [𝔭.IsPrime]
    (N : Submodule S M) (x : M)
    (h : LocalizedModule.mk x (1 : 𝔭.primeCompl) ∈
      N.localized' (Localization.AtPrime 𝔭) 𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl
        M)) :
    ∃ r : S, r ∉ 𝔭 ∧ r • x ∈ N := by
  rw [Submodule.mem_localized', IsLocalizedModule.mk_eq_mk'] at h
  obtain ⟨m, hm, s, hms⟩ := h
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hms
  obtain ⟨c, hc⟩ := hms
  have hcx : ((c : S) * (s : S)) • x = (c : S) • m := by
    have := hc
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    exact this
  exact ⟨(c : S) * (s : S), ‹𝔭.IsPrime›.mul_notMem c.2 s.2, by rw [hcx]; exact N.smul_mem _ hm⟩

private theorem localized'_sup {M N : Type u} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module
  S N]
    (p : Submonoid S) (T : Type u) [CommRing T] [Algebra S T] [IsLocalization p T] [Module T N]
    [IsScalarTower S T N] (f : M →ₗ[S] N) [IsLocalizedModule p f] (A B : Submodule S M) :
    (A ⊔ B).localized' T p f = A.localized' T p f ⊔ B.localized' T p f :=
  (Submodule.localized'gi T p f).gc.l_sup

attribute [local instance] Module.free_of_flat_of_isLocalRing in
private theorem bijective_linearCombination {M : Type u} [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module.Flat S M]
    (𝔪 : Ideal S) [𝔪.IsMaximal] {n : ℕ} (hn : Module.rankAtStalk M ⟨𝔪, inferInstance⟩ = n)
    (x : Fin n → M) (hx : 𝔪 • (⊤ : Submodule S M) ⊔ Submodule.span S (Set.range x) = ⊤) :
    Function.Bijective (Fintype.linearCombination (Localization.AtPrime 𝔪)
      (fun i => LocalizedModule.mk (x i) (1 : 𝔪.primeCompl))) := by
  set ω : Fin n → LocalizedModule 𝔪.primeCompl M := fun i => LocalizedModule.mk (x i) (1 :
    𝔪.primeCompl) with hω
  set ψ := Fintype.linearCombination (Localization.AtPrime 𝔪) ω with hψ
  have hn' : Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) = n := hn
  have hloc := congrArg (Submodule.localized' (Localization.AtPrime 𝔪) 𝔪.primeCompl
    (LocalizedModule.mkLinearMap 𝔪.primeCompl M)) hx
  rw [localized'_sup, Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
    Localization.AtPrime.map_eq_maximalIdeal, Submodule.localized'_span, ← Set.range_comp] at hloc
  have hrange : (LocalizedModule.mkLinearMap 𝔪.primeCompl M) ∘ x = ω := by
    funext i; rfl
  rw [hrange] at hloc
  have hspan : Submodule.span (Localization.AtPrime 𝔪) (Set.range ω) = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson (N' := ⊤) Module.Finite.fg_top
      (IsLocalRing.ringJacobson_eq_maximalIdeal _).ge ?_)
    rw [sup_comm, hloc]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, hψ, Fintype.range_linearCombination, hspan]
  let b := Module.finBasisOfFinrankEq (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) hn'
  have hcomp : Function.Surjective (b.equivFun.toLinearMap.comp ψ) :=
    b.equivFun.surjective.comp hsurj
  have hinj : Function.Injective (b.equivFun.toLinearMap.comp ψ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hcomp
  have hinj' : Function.Injective (⇑b.equivFun ∘ ⇑ψ) := by
    rw [LinearMap.coe_comp, LinearEquiv.coe_coe] at hinj
    exact hinj
  exact ⟨Function.Injective.of_comp hinj', hsurj⟩

private theorem notMem_support_kaehlerDifferential {R : Type*} [CommRing R] [Algebra ℂ R] [Algebra ℂ
  S] [Algebra R S]
    [IsScalarTower ℂ R S] {n : ℕ} (t : Fin n → S) (ht : ∀ i, ∃ r : R, algebraMap R S r = t i)
    (𝔪 : Ideal S) [𝔪.IsMaximal]
    (hspan : Submodule.span (Localization.AtPrime 𝔪)
      (Set.range fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)) =
        ⊤) :
    (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S (Ω[S⁄R]) := by
  rw [Module.notMem_support_iff']
  intro m
  obtain ⟨ω₁, rfl⟩ := KaehlerDifferential.map_surjective ℂ R S m
  have hmem : LocalizedModule.mk ω₁ (1 : 𝔪.primeCompl) ∈
      (Submodule.span S (Set.range fun i => KaehlerDifferential.D ℂ S (t i))).localized'
        (Localization.AtPrime 𝔪)
        𝔪.primeCompl (LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ])) := by
    rw [Submodule.localized'_span, ← Set.range_comp]
    have : (LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ])) ∘ (fun i => KaehlerDifferential.D ℂ S
      (t i)) =
        fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl) := by
      funext i; rfl
    rw [this, hspan]
    trivial
  obtain ⟨r, hr, hrω⟩ := exists_smul_mem_of_mk_mem 𝔪 _ ω₁ hmem
  refine ⟨r, hr, ?_⟩
  rw [← LinearMap.map_smul]
  have hle : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℂ S (t i)) ≤
      LinearMap.ker (KaehlerDifferential.map ℂ R S S) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨ri, hri⟩ := ht i
    change KaehlerDifferential.D ℂ S (t i) ∈ LinearMap.ker (KaehlerDifferential.map ℂ R S S)
    rw [LinearMap.mem_ker, KaehlerDifferential.map_D, Algebra.algebraMap_self_apply, ← hri,
      Derivation.map_algebraMap]
  exact hle hrω

private theorem notMem_support_h1Cotangent [Algebra ℂ S] [Algebra.FormallySmooth ℂ S] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S]
    (t : Fin n → S) (hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X i) = t i)
    (𝔪 : Ideal S) [𝔪.IsMaximal]
    (hψ : Function.Injective (Fintype.linearCombination (Localization.AtPrime 𝔪)
      (fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)))) :
    (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉
      Module.support S (Algebra.H1Cotangent (MvPolynomial (Fin n) ℂ) S) := by
  classical
  set R := MvPolynomial (Fin n) ℂ with hR
  rw [Module.notMem_support_iff']
  intro h
  have hinj : Function.Injective (Algebra.H1Cotangent.δ ℂ R S) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ (R := ℂ) (S := R) (T := S) z).1 hz
    rw [Subsingleton.elim w 0, LinearMap.map_zero]
  have hδ0 : KaehlerDifferential.mapBaseChange ℂ R S (Algebra.H1Cotangent.δ ℂ R S h) = 0 :=
    (Algebra.H1Cotangent.exact_δ_mapBaseChange (R := ℂ) (S := R) (T := S) _).2 ⟨h, rfl⟩
  let B : Module.Basis (Fin n) S (S ⊗[R] Ω[R⁄ℂ]) :=
    Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n))
  have hB : ∀ i, B i = (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (MvPolynomial.X i) := by
    intro i
    rw [show B i = Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n)) i
      from rfl,
      Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  set a : Fin n → S := fun i => B.repr (Algebra.H1Cotangent.δ ℂ R S h) i with ha
  have hsum : Algebra.H1Cotangent.δ ℂ R S h = ∑ i, a i • B i := (B.sum_repr _).symm
  have hmap : ∀ i, KaehlerDifferential.mapBaseChange ℂ R S (B i) = KaehlerDifferential.D ℂ S (t i)
    := by
    intro i
    rw [hB, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hX, one_smul]
  have hzero : ∑ i, a i • KaehlerDifferential.D ℂ S (t i) = 0 := by
    have := hδ0
    rw [hsum, map_sum] at this
    simp only [map_smul, hmap] at this
    exact this
  have hloc : Fintype.linearCombination (Localization.AtPrime 𝔪)
      (fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl))
      (fun i => algebraMap S (Localization.AtPrime 𝔪) (a i)) = 0 := by
    rw [Fintype.linearCombination_apply]
    have : ∀ i, algebraMap S (Localization.AtPrime 𝔪) (a i) •
        LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl) =
        LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ]) (a i • KaehlerDifferential.D ℂ S (t i)) :=
          by
      intro i
      rw [algebraMap_smul, LinearMap.map_smul]
      rfl
    simp only [this, ← map_sum, hzero, map_zero]
  have hai : ∀ i, algebraMap S (Localization.AtPrime 𝔪) (a i) = 0 := by
    intro i
    have := hψ (hloc.trans (map_zero _).symm)
    exact congrFun this i
  choose c hc using fun i => (IsLocalization.map_eq_zero_iff 𝔪.primeCompl (Localization.AtPrime 𝔪)
    (a i)).1 (hai i)
  set C : 𝔪.primeCompl := ∏ i, c i with hC
  have hCa : ∀ i, (C : S) * a i = 0 := by
    intro i
    rw [hC, Submonoid.coe_finsetProd, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc,
      hc i, mul_zero]
  refine ⟨C, C.2, hinj ?_⟩
  rw [LinearMap.map_smul, map_zero, hsum, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_smul, hCa i, zero_smul]

private theorem
  exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
(S : Type*) [CommRing S] [IsDomain S] [Algebra ℂ S] (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ g : S, σ₀ g ≠ 0 ∧
      letI : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by
  classical
  have := hsm
  let algX : Algebra (MvPolynomial (Fin n) ℂ) S := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have halg : ∀ p : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) S p =
    MvPolynomial.aeval t p :=
    fun _ => rfl
  have : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C])
  have hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X i) = t i := fun i => by
    rw [halg, MvPolynomial.aeval_X]
  have : Algebra.FiniteType (MvPolynomial (Fin n) ℂ) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (MvPolynomial (Fin n) ℂ) S
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) ℂ) S :=
    (Algebra.FinitePresentation.of_finiteType (R := MvPolynomial (Fin n) ℂ) (A := S)).mp ‹_›
  set 𝔪 : Ideal S := RingHom.ker σ₀.toRingHom with h𝔪
  have h𝔪max : 𝔪.IsMaximal := by
    rw [h𝔪]; exact RingHom.ker_isMaximal_of_surjective σ₀.toRingHom (fun c => ⟨algebraMap ℂ S c,
      σ₀.commutes c⟩)
  have hn : Module.rankAtStalk (Ω[S⁄ℂ]) ⟨𝔪, inferInstance⟩ = n := rankAtStalk_eq hrank _
  have hψ := bijective_linearCombination 𝔪 hn (fun i => KaehlerDifferential.D ℂ S (t i))
    (by rw [h𝔪]; exact hdt)
  have hspan : Submodule.span (Localization.AtPrime 𝔪)
      (Set.range fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)) =
        ⊤ := by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hψ.2
  have hEt : Algebra.IsEtaleAt (MvPolynomial (Fin n) ℂ) 𝔪 := by
    have : (⟨𝔪, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus (MvPolynomial (Fin n) ℂ) S :=
      by
      rw [Algebra.etaleLocus_eq_compl_support]
      exact ⟨notMem_support_kaehlerDifferential t (fun i => ⟨MvPolynomial.X i, hX i⟩) 𝔪 hspan,
        notMem_support_h1Cotangent t hX 𝔪 hψ.1⟩
    exact Algebra.mem_etaleLocus_iff.1 this
  have := hEt
  obtain ⟨g, hg𝔪, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := MvPolynomial (Fin n) ℂ) 𝔪
  refine ⟨g, fun h0 => hg𝔪 (by rw [h𝔪, RingHom.mem_ker]; exact h0), ?_⟩
  have hinst : (((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval
    t).toRingHom).toAlgebra :
      Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g)) =
      (inferInstance : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g)) := by
    refine Algebra.algebra_ext _ _ (fun p => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) S (Localization.Away g), halg]
    rfl
  rw [hinst]
  exact hSE

private theorem isStandardEtale_exists_algHom_data
(k : Type*) [Field k] {n : ℕ} (A : Type*) [CommRing A] [Algebra k A] [Algebra (MvPolynomial (Fin n)
  k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] [Algebra.IsStandardEtale (MvPolynomial (Fin n) k)
      A] :
    ∃ (x : A) (F G : Polynomial (MvPolynomial (Fin n) k)),
      (∀ τ : A →ₐ[k] k,
        (F.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A
          (MvPolynomial.X i)))).eval (τ x) = 0 ∧
        (G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A
          (MvPolynomial.X i)))).eval (τ x) ≠ 0 ∧
        ((Polynomial.derivative F).map (MvPolynomial.eval fun i : Fin n => τ (algebraMap
          (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k,
        (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) =
          τ' (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))) → τ x = τ' x → τ = τ') ∧
      (∀ (z : Fin n → k) (w : k), (F.map (MvPolynomial.eval z)).eval w = 0 → (G.map
        (MvPolynomial.eval z)).eval w ≠ 0 →
        ∃ τ : A →ₐ[k] k, (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))
          = z i) ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : Polynomial (MvPolynomial (Fin n) k)) (N : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * ((G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A
          (MvPolynomial.X i)))).eval (τ x)) ^ N =
          (h.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A
            (MvPolynomial.X i)))).eval (τ x)) := by
  classical
  set R := MvPolynomial (Fin n) k with hR
  obtain ⟨P⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
    Nonempty (StandardEtalePresentation R A))
  have hring : ∀ τ : A →ₐ[k] k, (τ : A →+* k).comp (algebraMap R A) =
      MvPolynomial.eval (fun i : Fin n => τ (algebraMap R A (MvPolynomial.X i))) := by
    intro τ
    apply MvPolynomial.ringHom_ext
    · intro a
      change τ (algebraMap R A (MvPolynomial.C a)) = MvPolynomial.eval _ (MvPolynomial.C a)
      rw [MvPolynomial.eval_C, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply]
    · intro i
      change τ (algebraMap R A (MvPolynomial.X i)) = MvPolynomial.eval _ (MvPolynomial.X i)
      rw [MvPolynomial.eval_X]
  have hev : ∀ (τ : A →ₐ[k] k) (q : Polynomial R),
      τ (aeval P.x q) = (q.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap R A (MvPolynomial.X
        i)))).eval (τ P.x) := by
    intro τ q
    rw [aeval_def, show τ (eval₂ (algebraMap R A) P.x q) = (τ : A →+* k) (eval₂ (algebraMap R A) P.x
      q) from rfl,
      hom_eval₂, hring τ, eval₂_eq_eval_map]
    rfl
  obtain ⟨hf0, hgU⟩ := P.hasMap
  refine ⟨P.x, P.f, P.g, ?_, ?_, ?_, ?_⟩
  · intro τ
    refine ⟨?_, ?_, ?_⟩
    · rw [← hev, hf0, map_zero]
    · rw [← hev]; exact (hgU.map τ).ne_zero
    · rw [← hev]; exact (P.hasMap.isUnit_derivative_f.map τ).ne_zero
  · intro τ τ' hX hx
    let instk : Algebra R k := (MvPolynomial.eval fun i : Fin n => τ (algebraMap R A
      (MvPolynomial.X i))).toAlgebra
    have hv : (fun i : Fin n => τ' (algebraMap R A (MvPolynomial.X i)))
        = fun i : Fin n => τ (algebraMap R A (MvPolynomial.X i)) := funext fun i => (hX i).symm
    let τR : A →ₐ[R] k :=
      { toRingHom := (τ : A →+* k)
        commutes' := fun p => by
          change ((τ : A →+* k).comp (algebraMap R A)) p = _
          rw [hring τ]; rfl }
    let τR' : A →ₐ[R] k :=
      { toRingHom := (τ' : A →+* k)
        commutes' := fun p => by
          change ((τ' : A →+* k).comp (algebraMap R A)) p = _
          rw [hring τ', hv]; rfl }
    have hcomp : τR.comp (P.equivRing.symm : P.Ring →ₐ[R] A) = τR'.comp (P.equivRing.symm : P.Ring
      →ₐ[R] A) := by
      apply StandardEtalePair.hom_ext
      change τ (P.equivRing.symm P.X) = τ' (P.equivRing.symm P.X)
      rw [P.equivRing_symm_X]; exact hx
    apply AlgHom.ext
    intro s
    have := congrArg (fun φ : P.Ring →ₐ[R] k => φ (P.equivRing s)) hcomp
    simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
      AlgEquiv.symm_apply_apply] at this
    exact this
  · intro z w hF hG
    let instk : Algebra R k := (MvPolynomial.eval z).toAlgebra
    have haev : ∀ q : Polynomial R, aeval (R := R) w q = (q.map (MvPolynomial.eval z)).eval w := by
      intro q
      rw [aeval_def, show algebraMap R k = MvPolynomial.eval z from rfl, eval₂_eq_eval_map]
    have hmap : P.HasMap (S := k) w :=
      ⟨by rw [haev]; exact hF, isUnit_iff_ne_zero.2 (by rw [haev]; exact hG)⟩
    let ψ : P.Ring →ₐ[R] k := P.lift w hmap
    let θ : A →ₐ[R] k := ψ.comp (P.equivRing : A ≃ₐ[R] P.Ring).toAlgHom
    let τ : A →ₐ[k] k :=
      { toRingHom := (θ : A →+* k)
        commutes' := fun c => by
          change θ (algebraMap k A c) = c
          rw [IsScalarTower.algebraMap_apply k R A, AlgHom.commutes]
          change MvPolynomial.eval z (algebraMap k R c) = c
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.eval_C] }
    refine ⟨τ, ?_, ?_⟩
    · intro i
      change θ (algebraMap R A (MvPolynomial.X i)) = z i
      rw [AlgHom.commutes]
      change MvPolynomial.eval z (MvPolynomial.X i) = z i
      rw [MvPolynomial.eval_X]
    · change ψ (P.equivRing P.x) = w
      rw [P.equivRing_x]
      exact P.lift_X w hmap
  · intro s
    obtain ⟨p, N, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
    refine ⟨p, N, fun τ => ?_⟩
    have := congrArg τ hp
    rw [map_mul, map_pow, hev, hev] at this
    exact this

private theorem contDiff_eval {n : ℕ} (a : MvPolynomial (Fin n) ℂ) : ContDiff ℂ ⊤ (fun z : Fin n → ℂ
  => MvPolynomial.eval z a) :=
  (AnalyticOnNhd.eval_mvPolynomial a).contDiff

private theorem contDiff_mapEval {n : ℕ} (q : Polynomial (MvPolynomial (Fin n) ℂ)) :
    ContDiff ℂ ⊤ (fun p : (Fin n → ℂ) × ℂ => (q.map (MvPolynomial.eval p.1)).eval p.2) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun v : (Fin n → ℂ) × ℂ => ((p + q).map (MvPolynomial.eval v.1)).eval v.2) =
        (fun v : (Fin n → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) +
          fun v : (Fin n → ℂ) × ℂ => (q.map (MvPolynomial.eval v.1)).eval v.2 := by
      funext v; simp [Polynomial.map_add]
    rw [this]; exact hp.add hq
  | monomial m a =>
    have : (fun v : (Fin n → ℂ) × ℂ => ((monomial m a).map (MvPolynomial.eval v.1)).eval v.2) =
        fun v : (Fin n → ℂ) × ℂ => MvPolynomial.eval v.1 a * v.2 ^ m := by
      funext v
      rw [Polynomial.map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C, eval_X]
    rw [this]
    exact ((contDiff_eval a).comp contDiff_fst).mul (contDiff_snd.pow m)

private theorem
  complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
{n : ℕ} (F : Polynomial (MvPolynomial (Fin n) ℂ)) (z₀ : Fin n → ℂ) (w₀ : ℂ)
    (h₀ : (F.map (MvPolynomial.eval z₀)).eval w₀ = 0)
    (hd : ((Polynomial.derivative F).map (MvPolynomial.eval z₀)).eval w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : (Fin n → ℂ) → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧ ContDiffOn ℂ ⊤ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ (F.map (MvPolynomial.eval z)).eval (φ z) =
        0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, (F.map (MvPolynomial.eval z)).eval w = 0 → w
        = φ z) := by
  classical
  set f : (Fin n → ℂ) × ℂ → ℂ := fun p => (F.map (MvPolynomial.eval p.1)).eval p.2 with hf
  have hcd : ContDiffAt ℂ ⊤ f (z₀, w₀) := (contDiff_mapEval F).contDiffAt
  have f00 : f (z₀, w₀) = 0 := h₀
  set c : ℂ := ((Polynomial.derivative F).map (MvPolynomial.eval z₀)).eval w₀ with hc
  have hderw : HasDerivAt (fun w : ℂ => f (z₀, w)) c w₀ := by
    have h := (F.map (MvPolynomial.eval z₀)).hasDerivAt w₀
    rw [derivative_map] at h
    exact h
  have hcomp : HasFDerivAt (fun w : ℂ => f (z₀, w))
      ((fderiv ℂ f (z₀, w₀)).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ)) w₀ :=
    (hcd.differentiableAt (by simp)).hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_right z₀ w₀)
  have heq : (fderiv ℂ f (z₀, w₀)).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c := hcomp.unique hderw.hasFDerivAt
  have hinv : ((fderiv ℂ f (z₀, w₀)).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ)).IsInvertible :=
    by
    rw [heq]
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := ContinuousLinearMap.smulRight (1 : ℂ
      →L[ℂ] ℂ) c⁻¹) ?_ ?_
    · ext; simp [hd]
    · ext; simp [hd]
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set ψ : (Fin n → ℂ) → ℂ := hcd.implicitFunction htop hinv with hψ
  have hψ0 : ψ z₀ = w₀ := hcd.implicitFunction_apply_self htop hinv
  have hzero : ∀ᶠ z in 𝓝 z₀, f (z, ψ z) = f (z₀, w₀) := hcd.eventually_apply_implicitFunction htop
    hinv
  have huniq : ∀ᶠ v in 𝓝 (z₀, w₀), f v = f (z₀, w₀) ↔ ψ v.1 = v.2 :=
    hcd.eventually_apply_eq_iff_implicitFunction htop hinv
  have hψcd : ContDiffAt ℂ ⊤ ψ z₀ := hcd.contDiffAt_implicitFunction htop hinv
  obtain ⟨U, hU, hψU⟩ := hψcd.contDiffOn (m := ⊤) le_rfl (by simp)
  have hdiffU : DifferentiableOn ℂ ψ U := hψU.differentiableOn (by simp)
  have hψcont : ContinuousAt ψ z₀ := hψcd.continuousAt
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 huniq
  have hball : ∀ᶠ z in 𝓝 z₀, ψ z ∈ Metric.ball w₀ ε := by
    have : Metric.ball w₀ ε ∈ 𝓝 (ψ z₀) := by rw [hψ0]; exact Metric.ball_mem_nhds _ hε
    exact hψcont.preimage_mem_nhds this
  have hall : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ f (z, ψ z) = f (z₀, w₀) ∧ ψ z ∈ Metric.ball w₀ ε ∧ z ∈
    Metric.ball z₀ ε :=
    (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU).and (hzero.and (hball.and (Metric.ball_mem_nhds z₀ hε)))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hall
  refine ⟨r, ε, ψ, hr, hε, hψ0, hdiffU.mono (fun z hz => (hrsub hz).1), hψU.mono (fun z hz => (hrsub
    hz).1), ?_, ?_⟩
  · intro z hz
    obtain ⟨-, h1, h2, -⟩ := hrsub hz
    rw [f00] at h1
    exact ⟨h2, h1⟩
  · intro z hz w hw hw'
    obtain ⟨-, -, -, h4⟩ := hrsub hz
    have hv : (z, w) ∈ Metric.ball (z₀, w₀) ε := by
      rw [← ball_prod_same]; exact ⟨h4, hw⟩
    have h5 := hεsub hv
    simp only [Set.mem_ofPred_eq] at h5
    rw [f00] at h5
    exact (h5.1 hw').symm

private theorem differentiableOn_mapEval_comp {n : ℕ} (q : Polynomial (MvPolynomial (Fin n) ℂ)) {φ :
  (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hφ : DifferentiableOn ℂ φ U) :
    DifferentiableOn ℂ (fun z => (q.map (MvPolynomial.eval z)).eval (φ z)) U := by
  have h1 : Differentiable ℂ (fun p : (Fin n → ℂ) × ℂ => (q.map (MvPolynomial.eval p.1)).eval p.2)
    :=
    (contDiff_mapEval q).differentiable (by simp)
  exact h1.comp_differentiableOn (differentiableOn_id.prodMk hφ)

end SmoothComplexCoordinatesAux

open SmoothComplexCoordinatesAux

/-- A smooth finite-type `ℂ`-algebra domain with a differential basis
at a point admits local complex-analytic coordinates given by evaluation
at the basis elements. -/
public theorem Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
(S : Type*) [CommRing S] [IsDomain S] [Algebra ℂ S] (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => fun i : Fin n => σ (t i)) 𝒰
        (Metric.ball (fun i : Fin n => σ₀ (t i)) r) ∧
      (∀ s : S, ∃ F : (Fin n → ℂ) → ℂ,
        DifferentiableOn ℂ F (Metric.ball (fun i : Fin n => σ₀ (t i)) r) ∧
        ∀ σ ∈ 𝒰, σ s = F (fun i : Fin n => σ (t i))) ∧
      (∀ σ ∈ 𝒰, ∃ (fs : Finset S) (ε : ℝ), 0 < ε ∧
        ∀ σ' : S →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖σ' s - σ s‖ < ε) → σ' ∈ 𝒰) := by
  classical
  obtain ⟨g, hg, hSE⟩ :=
    exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential S
      hsm hrank σ₀ t hdt
  let instA : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
    ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  have : Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := hSE
  have halg : ∀ p : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away
    g) p =
      algebraMap S (Localization.Away g) (MvPolynomial.aeval t p) := fun p => rfl
  have : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
  obtain ⟨x, F, G, hpt, hinjc, hsurjc, hrepr⟩ :=
    isStandardEtale_exists_algHom_data ℂ (n := n) (Localization.Away g)
  have hXt : ∀ i : Fin n, algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away g) (MvPolynomial.X
    i) =
      algebraMap S (Localization.Away g) (t i) := by
    intro i; rw [halg, MvPolynomial.aeval_X]
  simp only [hXt] at hpt hinjc hsurjc hrepr
  let ι : S →ₐ[ℂ] (Localization.Away g) := IsScalarTower.toAlgHom ℂ S (Localization.Away g)
  have hι : ∀ s : S, ι s = algebraMap S (Localization.Away g) s := fun s => rfl
  have hunit : ∀ (σ : S →ₐ[ℂ] ℂ), σ g ≠ 0 → ∀ y : Submonoid.powers g, IsUnit (σ y) := by
    rintro σ hσ ⟨y, m, rfl⟩
    rw [map_pow]; exact (isUnit_iff_ne_zero.2 hσ).pow m
  let L : ∀ (σ : S →ₐ[ℂ] ℂ), σ g ≠ 0 → ((Localization.Away g) →ₐ[ℂ] ℂ) := fun σ hσ =>
    IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := σ) (hunit σ hσ)
  have hL : ∀ (σ : S →ₐ[ℂ] ℂ) (hσ : σ g ≠ 0) (s : S), L σ hσ (algebraMap S (Localization.Away g) s)
    = σ s := fun σ hσ s => by
    change IsLocalization.liftAlgHom _ _ = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl
  have hLcomp : ∀ (σ : S →ₐ[ℂ] ℂ) (hσ : σ g ≠ 0), (L σ hσ).comp ι = σ := fun σ hσ =>
    AlgHom.ext fun s => hL σ hσ s
  have hτg : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, (τ.comp ι) g ≠ 0 := by
    intro τ
    change τ (algebraMap S (Localization.Away g) g) ≠ 0
    exact ((IsLocalization.Away.algebraMap_isUnit g).map τ).ne_zero
  have hcompL : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, L (τ.comp ι) (hτg τ) = τ := by
    intro τ
    apply AlgHom.toRingHom_injective
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    ext s
    exact hL (τ.comp ι) (hτg τ) s
  obtain ⟨⟨a, ⟨gm, m, rfl⟩⟩, hax⟩ := IsLocalization.surj (Submonoid.powers g) x
  have hxval : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, τ x = (τ.comp ι) a / ((τ.comp ι) g) ^ m := by
    intro τ
    have h1 := congrArg τ hax
    rw [map_mul, map_pow (algebraMap S (Localization.Away g)), map_pow] at h1
    rw [eq_div_iff (pow_ne_zero _ (hτg τ))]
    exact h1
  have hcoord : ∀ τ : (Localization.Away g) →ₐ[ℂ] ℂ, (fun i : Fin n => τ (algebraMap S
    (Localization.Away g) (t i))) =
      fun i : Fin n => (τ.comp ι) (t i) := fun τ => rfl
  let τ₀ : (Localization.Away g) →ₐ[ℂ] ℂ := L σ₀ hg
  have hτ₀ : ∀ s : S, τ₀ (algebraMap S (Localization.Away g) s) = σ₀ s := hL σ₀ hg
  obtain ⟨hF0, hG0, hD0⟩ := hpt τ₀
  simp only [hτ₀] at hF0 hG0 hD0
  obtain ⟨r, ρ, φ, hr, hρ, hφ0, hφd, -, hφF, hφuniq⟩ :=
    complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi F
      (fun i : Fin n => σ₀ (t i)) (τ₀ x) hF0 hD0
  have hGcont : ContinuousAt (fun z : Fin n → ℂ => (G.map (MvPolynomial.eval z)).eval (φ z)) (fun i
    : Fin n => σ₀ (t i)) := by
    have hφc : ContinuousAt φ (fun i : Fin n => σ₀ (t i)) := (hφd.differentiableAt
      (Metric.ball_mem_nhds _ hr)).continuousAt
    exact ((contDiff_mapEval G).continuous.continuousAt).comp
      (continuousAt_id.prodMk hφc)
  have hGnbhd : ∀ᶠ z in 𝓝 (fun i : Fin n => σ₀ (t i)), (G.map (MvPolynomial.eval z)).eval (φ z) ≠ 0
    := by
    refine hGcont.eventually_ne ?_
    rw [hφ0]; exact hG0
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.1 hGnbhd
  set r' := min r r₁ with hr'
  have hr'pos : 0 < r' := lt_min hr hr₁
  have hb1 : ∀ z ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r', z ∈ Metric.ball (fun i : Fin n => σ₀
    (t i)) r := fun z hz =>
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hb2 : ∀ z ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r', (G.map (MvPolynomial.eval z)).eval (φ
    z) ≠ 0 := fun z hz =>
    hr₁sub (Metric.ball_subset_ball (min_le_right _ _) hz)
  set 𝒱 : Set ((Localization.Away g) →ₐ[ℂ] ℂ) :=
    {τ | (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) ∈ Metric.ball (fun i : Fin
      n => σ₀ (t i)) r' ∧
      τ x ∈ Metric.ball (τ₀ x) ρ} with h𝒱
  set 𝒰 : Set (S →ₐ[ℂ] ℂ) := (fun τ : (Localization.Away g) →ₐ[ℂ] ℂ => τ.comp ι) '' 𝒱 with h𝒰
  have hφτ : ∀ τ ∈ 𝒱, τ x = φ (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) := by
    intro τ hτ
    exact hφuniq _ (hb1 _ hτ.1) _ hτ.2 (hpt τ).1
  refine ⟨r', 𝒰, hr'pos, ?_, ?_, ?_, ?_⟩
  · refine ⟨τ₀, ⟨?_, ?_⟩, hLcomp σ₀ hg⟩
    · simp only [hτ₀]; exact Metric.mem_ball_self hr'pos
    · exact Metric.mem_ball_self hρ
  · refine ⟨?_, ?_, ?_⟩
    · rintro σ ⟨τ, hτ, rfl⟩
      exact hτ.1
    · rintro σ ⟨τ, hτ, rfl⟩ σ' ⟨τ', hτ', rfl⟩ heq
      change (fun i : Fin n => τ (ι (t i))) = fun i : Fin n => τ' (ι (t i)) at heq
      have hx' : τ x = τ' x := by
        rw [hφτ τ hτ, hφτ τ' hτ']
        exact congrArg φ heq
      rw [hinjc τ τ' (fun i => congrFun heq i) hx']
    · intro z hz
      obtain ⟨hw, hFz⟩ := hφF z (hb1 z hz)
      obtain ⟨τ, hτt, hτx⟩ := hsurjc z (φ z) hFz (hb2 z hz)
      have hzt : (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))) = z := funext hτt
      refine ⟨τ.comp ι, ⟨τ, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · rw [hzt]; exact hz
      · rw [hτx]; exact hw
      · exact hzt
  · intro s
    obtain ⟨h, k, hk⟩ := hrepr (algebraMap S (Localization.Away g) s)
    refine ⟨fun z => (h.map (MvPolynomial.eval z)).eval (φ z) / ((G.map (MvPolynomial.eval z)).eval
      (φ z)) ^ k, ?_, ?_⟩
    · have hφ' : DifferentiableOn ℂ φ (Metric.ball (fun i : Fin n => σ₀ (t i)) r') := hφd.mono fun z
      hz => hb1 z hz
      have hden : DifferentiableOn ℂ (fun z : Fin n → ℂ => ((G.map (MvPolynomial.eval z)).eval (φ
        z)) ^ k)
          (Metric.ball (fun i : Fin n => σ₀ (t i)) r') := by
        have := (differentiableOn_mapEval_comp G hφ').pow k
        simpa only [Pi.pow_def] using this
      have hfun : (fun z : Fin n → ℂ => (h.map (MvPolynomial.eval z)).eval (φ z) / ((G.map
        (MvPolynomial.eval z)).eval (φ z)) ^ k) =
          fun z => (h.map (MvPolynomial.eval z)).eval (φ z) * (((G.map (MvPolynomial.eval z)).eval
            (φ z)) ^ k)⁻¹ := by
        funext z; rw [div_eq_mul_inv]
      rw [hfun]
      exact (differentiableOn_mapEval_comp h hφ').mul (hden.inv fun
        z hz => pow_ne_zero _ (hb2
        z hz))
    · rintro σ ⟨τ, hτ, rfl⟩
      change τ (algebraMap S (Localization.Away g) s) =
        (h.map (MvPolynomial.eval (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t
          i))))).eval
            (φ (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i)))) /
          ((G.map (MvPolynomial.eval (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t
            i))))).eval
            (φ (fun i : Fin n => τ (algebraMap S (Localization.Away g) (t i))))) ^ k
      rw [← hφτ τ hτ, eq_div_iff (pow_ne_zero _ ?_)]
      · exact hk τ
      · rw [hφτ τ hτ]; exact hb2 _ hτ.1
  · rintro σ ⟨τ, hτ, rfl⟩
    set V : Set (ℂ × (Fin n → ℂ) × ℂ) :=
      {p | p.1 ≠ 0 ∧ p.2.1 ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r' ∧ p.2.2 / p.1 ^ m ∈
        Metric.ball (τ₀ x) ρ} with hV
    have hVopen : IsOpen V := by
      have h1 : IsOpen {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0} := isOpen_ne_fun continuous_fst
        continuous_const
      have hc : ContinuousOn (fun p : ℂ × (Fin n → ℂ) × ℂ => p.2.2 / p.1 ^ m) {p : ℂ × (Fin n → ℂ) ×
        ℂ | p.1 ≠ 0} :=
        (continuous_snd.comp continuous_snd).continuousOn.div ((continuous_fst.pow m).continuousOn)
          fun p hp => pow_ne_zero _ hp
      have h3 : IsOpen {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0 ∧ p.2.2 / p.1 ^ m ∈ Metric.ball (τ₀ x) ρ}
        :=
        hc.isOpen_inter_preimage h1 Metric.isOpen_ball
      have h2 : IsOpen {p : ℂ × (Fin n → ℂ) × ℂ | p.2.1 ∈ Metric.ball (fun i : Fin n => σ₀ (t i))
        r'} :=
        Metric.isOpen_ball.preimage (continuous_fst.comp continuous_snd)
      have : V = {p : ℂ × (Fin n → ℂ) × ℂ | p.1 ≠ 0 ∧ p.2.2 / p.1 ^ m ∈ Metric.ball (τ₀ x) ρ} ∩
          {p | p.2.1 ∈ Metric.ball (fun i : Fin n => σ₀ (t i)) r'} := by
        ext p; simp only [hV, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
      rw [this]; exact h3.inter h2
    have hPV : ((τ.comp ι) g, (fun i : Fin n => (τ.comp ι) (t i)), (τ.comp ι) a) ∈ V := by
      refine ⟨hτg τ, ?_, ?_⟩
      · exact hτ.1
      · change (τ.comp ι) a / (τ.comp ι) g ^ m ∈ _
        rw [← hxval τ]; exact hτ.2
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hVopen _ hPV
    refine ⟨insert g (insert a (Finset.univ.image t)), ε, hε, fun σ' hσ' => ?_⟩
    have hg' := hσ' g (by simp)
    have ha' := hσ' a (by simp)
    have ht' : ∀ i : Fin n, ‖σ' (t i) - (τ.comp ι) (t i)‖ < ε := fun i => hσ' (t i) (by simp)
    have hmem : (σ' g, (fun i : Fin n => σ' (t i)), σ' a) ∈ V := by
      apply hεsub
      rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
      refine ⟨by rwa [dist_eq_norm], ?_, by rwa [dist_eq_norm]⟩
      rw [dist_pi_lt_iff hε]
      intro i; rw [dist_eq_norm]; exact ht' i
    obtain ⟨hg0, ht0, ha0⟩ := hmem
    dsimp only at hg0 ht0 ha0
    refine ⟨L σ' hg0, ⟨?_, ?_⟩, hLcomp σ' hg0⟩
    · simp only [hL σ' hg0]; exact ht0
    · rw [hxval (L σ' hg0), hLcomp σ' hg0]; exact ha0
