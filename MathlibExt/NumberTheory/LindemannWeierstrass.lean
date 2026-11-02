/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IsGaloisGroup.Defs
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Topology.Algebra.Order.Floor

@[expose] public section

section
namespace MathlibExt.NumberTheory.LindemannWeierstrassWanted

/-!
# Lindemann–Weierstrass theorem
This file proves the Lindemann–Weierstrass theorem: exponentials of distinct algebraic numbers
are linearly independent over the algebraic numbers.
-/

/-- Galois splitting field inside `ℂ` containing all the data. -/
private theorem lw_exists_splitting_field {ι : Type*} [Finite ι]
    (α β : ι → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i))
    (hβ : ∀ i, IsAlgebraic ℚ (β i)) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
      ∀ i, α i ∈ K ∧ β i ∈ K := by
  classical
  have := Fintype.ofFinite ι
  set P : Polynomial ℚ := ∏ i, minpoly ℚ (α i) * minpoly ℚ (β i) with hPdef
  have hP0 : P ≠ 0 := by
    rw [hPdef, Finset.prod_ne_zero_iff]
    intro i _
    exact mul_ne_zero (minpoly.ne_zero (hα i).isIntegral)
      (minpoly.ne_zero (hβ i).isIntegral)
  have hαroot : ∀ i, Polynomial.aeval (α i) P = 0 := by
    intro i
    rw [hPdef, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_mul, minpoly.aeval, zero_mul]
  have hβroot : ∀ i, Polynomial.aeval (β i) P = 0 := by
    intro i
    rw [hPdef, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_mul, minpoly.aeval, mul_zero]
  have hmap0 : P.map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mpr hP0
  have hmem : ∀ i, α i ∈ P.rootSet ℂ ∧ β i ∈ P.rootSet ℂ := by
    intro i
    exact ⟨Polynomial.mem_rootSet'.mpr ⟨hmap0, hαroot i⟩,
      Polynomial.mem_rootSet'.mpr ⟨hmap0, hβroot i⟩⟩
  have hsplit : (P.map (algebraMap ℚ ℂ)).Splits := Complex.isAlgClosed.splits _
  have hSF : Polynomial.IsSplittingField ℚ
      (IntermediateField.adjoin ℚ (P.rootSet ℂ)) P :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (P.rootSet ℂ)) :=
    Polynomial.IsSplittingField.finiteDimensional _ P
  have hnorm : Normal ℚ (IntermediateField.adjoin ℚ (P.rootSet ℂ)) :=
    Normal.of_isSplittingField P
  have hsep : Algebra.IsSeparable ℚ (IntermediateField.adjoin ℚ (P.rootSet ℂ)) :=
    inferInstance
  refine ⟨IntermediateField.adjoin ℚ (P.rootSet ℂ), hfin, IsGalois.mk, fun i => ?_⟩
  exact ⟨IntermediateField.subset_adjoin ℚ _ (hmem i).1,
    IntermediateField.subset_adjoin ℚ _ (hmem i).2⟩

/-- Galois-fixed elements of `K` are rational. -/
private theorem lw_exists_rat_of_forall_aut_eq {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (y : K)
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ y = y) :
    ∃ q : ℚ, algebraMap ℚ K q = y := by
  have hmem : y ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[ℚ] K)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f _
    exact h f
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq⟩

/-- Integral rational elements of `K` are integers. -/
private theorem lw_exists_int_of_isIntegral_rat {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (q : ℚ)
    (h : IsIntegral ℤ (algebraMap ℚ K q)) :
    ∃ z : ℤ, (z : ℚ) = q := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ ℚ K) :=
    RingHom.injective (IsScalarTower.toAlgHom ℤ ℚ K).toRingHom
  have h' : IsIntegral ℤ q :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K) hinj (x := q)).mp h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨z, by exact_mod_cast hz⟩

/-- The exponential character `K → ℂ`. -/
private noncomputable def lw_expHom {K : IntermediateField ℚ ℂ} : Multiplicative K →* ℂ :=
  Complex.expMonoidHom.comp (AddMonoidHom.toMultiplicative K.val.toAddMonoidHom)

/-- Evaluation of `K`-coefficient exponential polynomials. -/
private noncomputable def lw_evK {K : IntermediateField ℚ ℂ} :
    AddMonoidAlgebra K K →ₐ[K] ℂ :=
  AddMonoidAlgebra.lift K ℂ K lw_expHom

/-- Evaluation of `ℚ`-coefficient exponential polynomials. -/
private noncomputable def lw_evQ {K : IntermediateField ℚ ℂ} :
    AddMonoidAlgebra ℚ K →ₐ[ℚ] ℂ :=
  AddMonoidAlgebra.lift ℚ ℂ K lw_expHom

/-- The character sends `x` to `exp x`. -/
private theorem lw_expHom_apply {K : IntermediateField ℚ ℂ} (x : K) :
    lw_expHom (Multiplicative.ofAdd x) = Complex.exp (x : ℂ) := by
  simp [lw_expHom, Complex.expMonoidHom_apply]

/-- Evaluation on single terms, `K` coefficients. -/
private theorem lw_evK_single {K : IntermediateField ℚ ℂ} (x c : K) :
    lw_evK (AddMonoidAlgebra.single x c) = (c : ℂ) * Complex.exp (x : ℂ) := by
  simp only [lw_evK, AddMonoidAlgebra.lift_single, lw_expHom_apply, Algebra.smul_def,
    IntermediateField.algebraMap_apply]

/-- Evaluation on single terms, `ℚ` coefficients. -/
private theorem lw_evQ_single {K : IntermediateField ℚ ℂ} (x : K) (c : ℚ) :
    lw_evQ (AddMonoidAlgebra.single x c) = (c : ℂ) * Complex.exp (x : ℂ) := by
  simp only [lw_evQ, AddMonoidAlgebra.lift_single, lw_expHom_apply, Algebra.smul_def,
    eq_ratCast]

/-- Evaluation as a sum over the support. -/
private theorem lw_evQ_sum {K : IntermediateField ℚ ℂ} (E : AddMonoidAlgebra ℚ K) :
    lw_evQ E = ∑ x ∈ E.coeff.support, (E.coeff x : ℂ) * Complex.exp (x : ℂ) := by
  rw [lw_evQ, AddMonoidAlgebra.lift_apply']
  change E.coeff.support.sum _ = _
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [lw_expHom_apply, eq_ratCast]

/-- Evaluation commutes with pushing coefficients `ℚ → K`. -/
private theorem lw_evK_mapRingHom_eq {K : IntermediateField ℚ ℂ}
    (E : AddMonoidAlgebra ℚ K) :
    lw_evK (AddMonoidAlgebra.mapRingHom K (algebraMap ℚ K) E) = lw_evQ E := by
  have h : lw_evK.toRingHom.comp (AddMonoidAlgebra.mapRingHom K (algebraMap ℚ K))
      = lw_evQ.toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      change lw_evK (AddMonoidAlgebra.mapRingHom K (algebraMap ℚ K)
        (AddMonoidAlgebra.single 0 r)) = lw_evQ (AddMonoidAlgebra.single 0 r)
      rw [AddMonoidAlgebra.mapRingHom_single, lw_evK_single, lw_evQ_single]
      simp [eq_ratCast]
    · intro m
      change lw_evK (AddMonoidAlgebra.mapRingHom K (algebraMap ℚ K)
        (AddMonoidAlgebra.single m 1)) = lw_evQ (AddMonoidAlgebra.single m 1)
      rw [AddMonoidAlgebra.mapRingHom_single, map_one, lw_evK_single, lw_evQ_single]
      simp
  exact DFunLike.congr_fun h E

open Classical in
/-- The initial group-ring element and its evaluation. -/
private theorem lw_initial {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {ι : Type*} [Fintype ι] (a b : ι → K)
    (ha : Function.Injective (fun i => ((a i : K) : ℂ)))
    (i₀ : ι) (hb : ((b i₀ : K) : ℂ) ≠ 0) :
    lw_evK (∑ i, AddMonoidAlgebra.single (a i) (b i))
      = ∑ i, ((b i : K) : ℂ) * Complex.exp ((a i : K) : ℂ)
    ∧ (∑ i, AddMonoidAlgebra.single (a i) (b i)) ≠ 0 := by
  constructor
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact lw_evK_single (a i) (b i)
  · intro h0
    have hcoeff : (∑ i, AddMonoidAlgebra.single (a i) (b i)).coeff (a i₀)
        = b i₀ := by
      rw [AddMonoidAlgebra.coeff_sum]
      simp only [Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i₀]
      · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        simp
      · intro j _ hji
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        have hne : a j ≠ a i₀ := fun hcon => hji (ha (congrArg _ hcon))
        exact ite_eq_right hne
      · intro hcon
        exact absurd (Finset.mem_univ i₀) hcon
    rw [h0] at hcoeff
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
    have hcon : ((b i₀ : K) : ℂ) = 0 := by
      rw [← hcoeff]
      simp
    exact hb hcon

open Classical in
/-- Coefficient norm over the Galois group. -/
private noncomputable def lw_coeffNorm {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (E : AddMonoidAlgebra K K) :
    AddMonoidAlgebra K K :=
  ∏ σ : (K ≃ₐ[ℚ] K), AddMonoidAlgebra.mapRingHom K (σ : K →+* K) E

open Classical in
/-- The coefficient norm is nonzero, vanishes under evaluation, and has
Galois-fixed coefficients. -/
private theorem lw_coeffNorm_props {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E : AddMonoidAlgebra K K) (hE0 : E ≠ 0) (hev : lw_evK E = 0) :
    lw_coeffNorm E ≠ 0 ∧ lw_evK (lw_coeffNorm E) = 0 ∧
      ∀ τ : (K ≃ₐ[ℚ] K), ∀ x : K, τ ((lw_coeffNorm E).coeff x)
        = (lw_coeffNorm E).coeff x := by
  have hinj : ∀ σ : (K ≃ₐ[ℚ] K), Function.Injective
      (AddMonoidAlgebra.mapRingHom K (σ : K →+* K)) := by
    intro σ x y hxy
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    have hmc := congrArg (fun z => z.coeff m) hxy
    rw [AddMonoidAlgebra.coeff_mapRingHom,
      AddMonoidAlgebra.coeff_mapRingHom] at hmc
    exact σ.injective hmc
  have hfac : ∀ σ ∈ (Finset.univ : Finset (K ≃ₐ[ℚ] K)),
      (AddMonoidAlgebra.mapRingHom K (σ : K →+* K)) E ≠ 0 := by
    intro σ _ hcon
    apply hE0
    have h2 : (AddMonoidAlgebra.mapRingHom K (σ : K →+* K)) E
        = (AddMonoidAlgebra.mapRingHom K (σ : K →+* K)) 0 := by
      rw [hcon, map_zero]
    exact hinj σ h2
  have hne : lw_coeffNorm E ≠ 0 := by
    simp only [lw_coeffNorm]
    exact Finset.prod_ne_zero_iff.mpr hfac
  have h1E : (AddMonoidAlgebra.mapRingHom K ((1 : K ≃ₐ[ℚ] K) : K →+* K)) E
      = E := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro m
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    exact AlgEquiv.one_apply (E.coeff m)
  have hev1 : lw_evK (lw_coeffNorm E) = 0 := by
    simp only [lw_coeffNorm]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [h1E]; exact hev)
  have hstab : ∀ τ : (K ≃ₐ[ℚ] K),
      AddMonoidAlgebra.mapRingHom K (τ : K →+* K) (lw_coeffNorm E)
        = lw_coeffNorm E := by
    intro τ
    simp only [lw_coeffNorm]
    rw [map_prod]
    have hcomp : ∀ σ : (K ≃ₐ[ℚ] K),
        (AddMonoidAlgebra.mapRingHom K (τ : K →+* K))
          ((AddMonoidAlgebra.mapRingHom K (σ : K →+* K)) E)
        = (AddMonoidAlgebra.mapRingHom K (((τ * σ : K ≃ₐ[ℚ] K)) : K →+* K)) E := by
      intro σ
      apply AddMonoidAlgebra.ext
      apply Finsupp.ext
      intro m
      rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_mapRingHom]
      exact (AlgEquiv.mul_apply τ σ (E.coeff m)).symm
    simp only [hcomp]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  refine ⟨hne, hev1, fun τ x => ?_⟩
  have h2 := congrArg (fun z => z.coeff x) (hstab τ)
  rw [AddMonoidAlgebra.coeff_mapRingHom] at h2
  exact h2

open Classical in
/-- Descend Galois-fixed coefficients to `ℚ`. -/
private theorem lw_descend {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E₁ : AddMonoidAlgebra K K) (hne : E₁ ≠ 0) (hev : lw_evK E₁ = 0)
    (hfix : ∀ τ : (K ≃ₐ[ℚ] K), ∀ x : K, τ (E₁.coeff x) = E₁.coeff x) :
    ∃ E₂ : AddMonoidAlgebra ℚ K,
      AddMonoidAlgebra.mapRingHom K (algebraMap ℚ K) E₂ = E₁ ∧
        E₂ ≠ 0 ∧ lw_evQ E₂ = 0 := by
  have hrat : ∀ x : K, ∃ q : ℚ, algebraMap ℚ K q = E₁.coeff x := by
    intro x
    exact lw_exists_rat_of_forall_aut_eq (E₁.coeff x) (fun σ => hfix σ x)
  choose q hq using hrat
  have hsupp : ∀ a : K, q a ≠ 0 → a ∈ E₁.coeff.support := by
    intro a ha
    rw [Finsupp.mem_support_iff, ← hq a]
    intro hcon
    apply ha
    have h2 : algebraMap ℚ K (q a) = algebraMap ℚ K 0 := by
      rw [hcon, map_zero]
    exact FaithfulSMul.algebraMap_injective ℚ K h2
  have hmap : AddMonoidAlgebra.mapRingHom K (algebraMap ℚ K)
      (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset E₁.coeff.support q hsupp))
      = E₁ := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_ofCoeff,
      Finsupp.onFinset_apply]
    exact hq x
  refine ⟨_, hmap, ?_, ?_⟩
  · intro hcon
    apply hne
    rw [← hmap, hcon, map_zero]
  · rw [← lw_evK_mapRingHom_eq, hmap, hev]

open Classical in
/-- Exponent norm over the Galois group. -/
private noncomputable def lw_expNorm {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (E₂ : AddMonoidAlgebra ℚ K) :
    AddMonoidAlgebra ℚ K :=
  ∏ σ : (K ≃ₐ[ℚ] K),
    AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K) E₂

open Classical in
/-- The exponent norm is nonzero, vanishes under evaluation, and is
Galois-invariant. -/
private theorem lw_expNorm_props {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E₂ : AddMonoidAlgebra ℚ K) (hE0 : E₂ ≠ 0) (hev : lw_evQ E₂ = 0) :
    lw_expNorm E₂ ≠ 0 ∧ lw_evQ (lw_expNorm E₂) = 0 ∧
      ∀ τ : (K ≃ₐ[ℚ] K),
        AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) (lw_expNorm E₂)
          = lw_expNorm E₂ := by
  have hinj : ∀ σ : (K ≃ₐ[ℚ] K), Function.Injective
      (AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K)) :=
    fun σ => AddMonoidAlgebra.mapDomain_injective (R := ℚ) σ.injective
  have hfac : ∀ σ ∈ (Finset.univ : Finset (K ≃ₐ[ℚ] K)),
      AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K) E₂ ≠ 0 := by
    intro σ _ hcon
    apply hE0
    have h2 : AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K) E₂
        = AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K) 0 := by
      rw [hcon, map_zero]
    exact hinj σ h2
  have hne : lw_expNorm E₂ ≠ 0 := by
    simp only [lw_expNorm]
    exact Finset.prod_ne_zero_iff.mpr hfac
  have h1 : ((1 : K ≃ₐ[ℚ] K) : K →+ K) = AddMonoidHom.id K := by
    apply AddMonoidHom.ext
    intro x
    exact AlgEquiv.one_apply x
  have h1E : AddMonoidAlgebra.mapDomainRingHom ℚ ((1 : K ≃ₐ[ℚ] K) : K →+ K)
      E₂ = E₂ := by
    rw [h1, AddMonoidAlgebra.mapDomainRingHom_id, RingHom.id_apply]
  have hev1 : lw_evQ (lw_expNorm E₂) = 0 := by
    simp only [lw_expNorm]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [h1E]; exact hev)
  have hhom : ∀ τ σ : (K ≃ₐ[ℚ] K), (τ : K →+ K).comp (σ : K →+ K)
      = (((τ * σ : K ≃ₐ[ℚ] K)) : K →+ K) := by
    intro τ σ
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply]
    exact (AlgEquiv.mul_apply τ σ x).symm
  have hstab : ∀ τ : (K ≃ₐ[ℚ] K),
      AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) (lw_expNorm E₂)
        = lw_expNorm E₂ := by
    intro τ
    simp only [lw_expNorm]
    rw [map_prod]
    have hcomp : ∀ σ : (K ≃ₐ[ℚ] K),
        AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K)
          (AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K) E₂)
        = AddMonoidAlgebra.mapDomainRingHom ℚ
          (((τ * σ : K ≃ₐ[ℚ] K)) : K →+ K) E₂ := by
      intro σ
      have e := AddMonoidAlgebra.mapDomainRingHom_comp (R := ℚ) (τ : K →+ K)
        (σ : K →+ K)
      rw [hhom τ σ] at e
      have e2 := DFunLike.congr_fun e E₂
      rw [RingHom.comp_apply] at e2
      exact e2.symm
    simp only [hcomp]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  exact ⟨hne, hev1, hstab⟩

open Classical in
/-- Invariant elements have invariant coefficients. -/
private theorem lw_invariant_coeff {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E : AddMonoidAlgebra ℚ K) (τ : (K ≃ₐ[ℚ] K))
    (h : AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) E = E) :
    (∀ x : K, E.coeff (τ x) = E.coeff x)
      ∧ ∀ x : K, (x ∈ E.coeff.support ↔ τ x ∈ E.coeff.support) := by
  have hfun : Finsupp.mapDomain (τ : K →+ K) E.coeff = E.coeff := by
    have h2 := congrArg AddMonoidAlgebra.coeff h
    rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain,
      AddMonoidAlgebra.coeff_ofCoeff] at h2
    exact h2
  have hpt : ∀ x : K, E.coeff x = E.coeff ((τ : K →+ K) x) := by
    intro x
    have h3 := DFunLike.congr_fun hfun ((τ : K →+ K) x)
    rw [Finsupp.mapDomain_apply_of_injective (f := (τ : K →+ K))
      τ.injective] at h3
    exact h3
  refine ⟨fun x => (hpt x).symm, fun x => ?_⟩
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, hpt x]
  exact Iff.rfl

open Classical in
/-- Reflection as a ring hom on the group ring. -/
private noncomputable def lw_refl {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] :
    AddMonoidAlgebra ℚ K →+* AddMonoidAlgebra ℚ K :=
  AddMonoidAlgebra.mapDomainRingHom ℚ (negAddMonoidHom : K →+ K)

open Classical in
/-- Coefficients of the reflection. -/
private theorem lw_refl_coeff {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E : AddMonoidAlgebra ℚ K) (y : K) :
    (lw_refl E).coeff y = E.coeff (-y) := by
  have hy : y = (negAddMonoidHom : K →+ K) (-y) := (neg_neg y).symm
  conv_lhs => rw [hy]
  simp only [lw_refl, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.mapDomain_apply_of_injective (f := (negAddMonoidHom : K →+ K))
      neg_injective]

open Classical in
/-- The constant coefficient of `E * refl E` is a sum of squares. -/
private theorem lw_coeff_zero_mul_refl {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E : AddMonoidAlgebra ℚ K) :
    (E * lw_refl E).coeff 0 = E.coeff.sum (fun _ r => r * r) := by
  rw [AddMonoidAlgebra.coeff_mul]
  apply Finsupp.sum_congr
  intro x hx
  change (lw_refl E).coeff.sum
      (fun m₂ r₂ => if x + m₂ = 0 then E.coeff x * r₂ else 0)
    = E.coeff x * E.coeff x
  have hguard : ∀ m₂ : K, (x + m₂ = 0 ↔ m₂ = -x) := by
    intro m₂
    constructor
    · intro h
      linear_combination h
    · intro h
      rw [h, add_neg_cancel]
  simp only [hguard]
  rw [Finsupp.sum_ite_eq']
  have hmem : -x ∈ (lw_refl E).coeff.support := by
    rw [Finsupp.mem_support_iff, lw_refl_coeff, neg_neg]
    exact Finsupp.mem_support_iff.mp hx
  rw [ite_eq_left hmem]
  simp only [lw_refl_coeff, neg_neg]

open Classical in
/-- Reflection gives vanishing evaluation, invariance and a positive
constant term. -/
private theorem lw_reflect {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E₃ : AddMonoidAlgebra ℚ K) (hE0 : E₃ ≠ 0) (hev : lw_evQ E₃ = 0)
    (hinv : ∀ τ : (K ≃ₐ[ℚ] K),
      AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) E₃ = E₃) :
    lw_evQ (E₃ * lw_refl E₃) = 0 ∧
      (∀ τ : (K ≃ₐ[ℚ] K), AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K)
        (E₃ * lw_refl E₃) = E₃ * lw_refl E₃) ∧
      0 < (E₃ * lw_refl E₃).coeff 0 := by
  have hev1 : lw_evQ (E₃ * lw_refl E₃) = 0 := by
    rw [map_mul, hev, zero_mul]
  have hcomm : ∀ τ : (K ≃ₐ[ℚ] K), (τ : K →+ K).comp
      (negAddMonoidHom : K →+ K)
      = (negAddMonoidHom : K →+ K).comp (τ : K →+ K) := by
    intro τ
    apply AddMonoidHom.ext
    intro x
    change τ (-x) = -(τ x)
    exact map_neg _ _
  have hrefl : ∀ τ : (K ≃ₐ[ℚ] K),
      AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) (lw_refl E₃)
        = lw_refl (AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) E₃) := by
    intro τ
    have e1 := DFunLike.congr_fun
      (AddMonoidAlgebra.mapDomainRingHom_comp (R := ℚ) (τ : K →+ K)
        (negAddMonoidHom : K →+ K)) E₃
    have e2 := DFunLike.congr_fun
      (AddMonoidAlgebra.mapDomainRingHom_comp (R := ℚ)
        (negAddMonoidHom : K →+ K) (τ : K →+ K)) E₃
    rw [RingHom.comp_apply] at e1 e2
    rw [hcomm τ] at e1
    simp only [lw_refl] at e1 e2 ⊢
    exact e1.symm.trans e2
  have hstab : ∀ τ : (K ≃ₐ[ℚ] K), AddMonoidAlgebra.mapDomainRingHom ℚ
      (τ : K →+ K) (E₃ * lw_refl E₃) = E₃ * lw_refl E₃ := by
    intro τ
    rw [map_mul, hrefl, hinv τ]
  have hpos : 0 < (E₃ * lw_refl E₃).coeff 0 := by
    rw [lw_coeff_zero_mul_refl]
    change 0 < E₃.coeff.support.sum (fun x => E₃.coeff x * E₃.coeff x)
    refine Finset.sum_pos (fun x hx => ?_) ?_
    · rw [Finsupp.mem_support_iff] at hx
      exact mul_self_pos.mpr hx
    · by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply hE0
      exact AddMonoidAlgebra.coeff_eq_zero.mp
        (Finsupp.support_eq_empty.mp hcon)
  exact ⟨hev1, hstab, hpos⟩

open Classical in
/-- Integer weights on the support. -/
private theorem lw_weights {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (E₄ : AddMonoidAlgebra ℚ K) (hev : lw_evQ E₄ = 0)
    (hinv : ∀ τ : (K ≃ₐ[ℚ] K),
      AddMonoidAlgebra.mapDomainRingHom ℚ (τ : K →+ K) E₄ = E₄)
    (hpos : 0 < E₄.coeff 0) :
    ∃ (S : Finset K) (w : K → ℤ), 0 ∈ S ∧ 0 < w 0 ∧
      (∀ τ : (K ≃ₐ[ℚ] K), ∀ x : K, w (τ x) = w x ∧ (x ∈ S ↔ τ x ∈ S)) ∧
      ∑ x ∈ S, (w x : ℂ) * Complex.exp (x : ℂ) = 0 := by
  set S : Finset K := E₄.coeff.support with hSdef
  set N : ℕ := ∏ x ∈ S, (E₄.coeff x).den with hNdef
  have hex : ∀ x : K, ∃ m : ℤ, (m : ℚ) = N * E₄.coeff x := by
    intro x
    by_cases hxm : x ∈ S
    · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (E₄.coeff x).den) hxm
      have hk' : N = (E₄.coeff x).den * k := by rw [hNdef]; exact hk
      refine ⟨(E₄.coeff x).num * k, ?_⟩
      have hden : ((E₄.coeff x).den : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Rat.den_nz _)
      have h := Rat.num_div_den (E₄.coeff x)
      rw [div_eq_iff hden] at h
      rw [hk', Int.cast_mul, Nat.cast_mul, Int.cast_natCast, h]
      ring
    · have hx0 : E₄.coeff x = 0 := by
        rw [hSdef] at hxm
        exact Finsupp.notMem_support_iff.mp hxm
      refine ⟨0, ?_⟩
      rw [hx0, mul_zero, Int.cast_zero]
  choose w hw using hex
  have hS0 : (0 : K) ∈ S := by
    rw [hSdef]
    exact Finsupp.mem_support_iff.mpr (ne_of_gt hpos)
  have hNpos : (0 : ℚ) < N := by
    rw [hNdef]
    apply Nat.cast_pos.mpr
    apply Finset.prod_pos
    intro x _
    exact Nat.pos_of_ne_zero (Rat.den_nz _)
  have hw0 : 0 < w 0 := by
    have h0 : (0 : ℚ) < ((w 0 : ℤ) : ℚ) := by
      rw [hw 0]
      exact mul_pos hNpos hpos
    exact_mod_cast h0
  have hwinv : ∀ τ : (K ≃ₐ[ℚ] K), ∀ x : K,
      w (τ x) = w x ∧ (x ∈ S ↔ τ x ∈ S) := by
    intro τ x
    obtain ⟨hcoeffτ, hsuppτ⟩ := lw_invariant_coeff E₄ τ (hinv τ)
    refine ⟨?_, ?_⟩
    · have e1 := hw (τ x)
      have e2 := hw x
      rw [hcoeffτ x] at e1
      exact (Int.cast_injective (e2.trans e1.symm)).symm
    · rw [hSdef]
      exact hsuppτ x
  have hevS : ∑ x ∈ E₄.coeff.support, (E₄.coeff x : ℂ) * Complex.exp (x : ℂ)
      = 0 := by
    have h := lw_evQ_sum E₄
    rw [hev] at h
    exact h.symm
  rw [← hSdef] at hevS
  have hterm : ∀ x ∈ S, (w x : ℂ)
      = (N : ℂ) * (E₄.coeff x : ℂ) := by
    intro x _
    have eC := congrArg (Rat.cast : ℚ → ℂ) (hw x)
    simpa using eC
  have hsum : ∑ x ∈ S, (w x : ℂ) * Complex.exp (x : ℂ) = 0 := by
    have hstep : (∑ x ∈ S, (w x : ℂ) * Complex.exp (x : ℂ))
        = (N : ℂ) * (∑ x ∈ S, (E₄.coeff x : ℂ) * Complex.exp (x : ℂ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x hx => by rw [hterm x hx]; ring)
    rw [hstep, hevS, mul_zero]
  exact ⟨S, w, hS0, hw0, hwinv, hsum⟩

open Classical in
/-- A common integer denominator making all of `S` integral. -/
private theorem lw_common_denom {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (S : Finset K) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ S, IsIntegral ℤ (d • x) := by
  have halg : ∀ x : K, IsAlgebraic ℚ (x : K) := by
    intro x
    rw [isAlgebraic_iff_isIntegral]
    exact IsIntegral.of_finite ℚ x
  have hex : ∀ x : K, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • x) := by
    intro x
    have hZ : IsAlgebraic ℤ (x : K) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (halg x)
    exact IsAlgebraic.exists_integral_multiple hZ
  choose y hy0 hy using hex
  refine ⟨∏ x ∈ S, y x, Finset.prod_ne_zero_iff.mpr (fun x _ => hy0 x), ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem y hx
  have hsm : (∏ x ∈ S, y x) • x = k • ((y x) • x) := by
    rw [hk, mul_comm (y x) k, mul_smul]
  rw [hsm]
  exact IsIntegral.zsmul (hy x) k

/-- Copy: strip powers of `X` from a monic integer polynomial killing
a nonzero integral `x`. -/
private theorem lw_exists_monic_coeff_zero_ne_zero_of_isIntegral (x : ℂ) (hx : x ≠ 0)
    (hint : IsIntegral ℤ x) :
    ∃ q : Polynomial ℤ, q.Monic ∧ q.coeff 0 ≠ 0 ∧ Polynomial.aeval x q = 0 := by
  obtain ⟨p, hpmonic, hpeval⟩ := hint
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hX0 : (Polynomial.X - Polynomial.C (0 : ℤ)) = Polynomial.X := by simp
  rw [hX0] at hq_eq hq_ndvd
  have hXpow_monic : ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p).Monic :=
    Polynomial.monic_X_pow _
  have hq_monic : q.Monic := by
    have hprod_monic :
        ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p
          * q).Monic := by
      rw [← hq_eq]; exact hpmonic
    exact Polynomial.Monic.of_mul_monic_left hXpow_monic hprod_monic
  refine ⟨q, hq_monic, ?_, ?_⟩
  · intro hcoeff
    exact hq_ndvd (Polynomial.X_dvd_iff.mpr hcoeff)
  · have hpeval_a : Polynomial.aeval x p = 0 := hpeval
    have haeval : Polynomial.aeval x p = Polynomial.aeval x
        ((Polynomial.X : Polynomial ℤ) ^ Polynomial.rootMultiplicity 0 p * q) := by
      rw [← hq_eq]
    rw [map_mul, map_pow, Polynomial.aeval_X] at haeval
    rw [hpeval_a] at haeval
    have hxr : x ^ Polynomial.rootMultiplicity 0 p ≠ 0 := pow_ne_zero _ hx
    rcases mul_eq_zero.mp haeval.symm with h1 | h1
    · exact absurd h1 hxr
    · exact h1

open Classical in
/-- Copy: common monic integer polynomial vanishing at all nonzero integral
points, with nonzero constant term. -/
private theorem lw_exists_int_poly_eval_zero_ne_zero_of_isIntegral {ι : Type*}
    [Finite ι] (x : ι → ℂ) (hint : ∀ i, IsIntegral ℤ (x i)) :
    ∃ F : Polynomial ℤ, F.Monic ∧ Polynomial.eval 0 F ≠ 0 ∧
      ∀ i, x i ≠ 0 → Polynomial.aeval (x i) F = 0 := by
  have := Fintype.ofFinite ι
  have hex : ∀ i, ∃ q : Polynomial ℤ,
      q.Monic ∧ (x i ≠ 0 → q.coeff 0 ≠ 0 ∧ Polynomial.aeval (x i) q = 0) := by
    intro i
    by_cases hi : x i ≠ 0
    · obtain ⟨q, hqm, hq0, hqeval⟩ :=
        lw_exists_monic_coeff_zero_ne_zero_of_isIntegral (x i) hi (hint i)
      exact ⟨q, hqm, fun _ => ⟨hq0, hqeval⟩⟩
    · exact ⟨1, Polynomial.monic_one, fun h => absurd h hi⟩
  choose Q hQm hQ using hex
  let s : Finset ι := Finset.univ.filter (fun i => x i ≠ 0)
  refine ⟨s.prod (fun i => Q i), ?_, ?_, ?_⟩
  · exact Polynomial.monic_prod_of_monic s _ (fun i _ => hQm i)
  · rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hne : x i ≠ 0 := (Finset.mem_filter.mp hi).2
    have h := (hQ i hne).1
    rwa [Polynomial.coeff_zero_eq_eval_zero] at h
  · intro i hi
    have himem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hQi : Polynomial.aeval (x i) (Q i) = 0 := (hQ i hi).2
    have hmap : Polynomial.aeval (x i) (s.prod (fun j => Q j))
        = s.prod (fun j => Polynomial.aeval (x i) (Q j)) := by
      rw [map_prod]
    rw [hmap]
    exact Finset.prod_eq_zero himem hQi

/-- Helper: the coercion `K → ℂ` is injective. -/
private theorem lw_coe_injective {K : IntermediateField ℚ ℂ} :
    Function.Injective ((↑) : K → ℂ) :=
  Subtype.coe_injective

open Classical in
/-- Auxiliary integer polynomial vanishing at the nonzero points of `S`
after scaling by `d`, with nonzero constant term. -/
private theorem lw_aux_poly {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (S : Finset K) (d : ℤ) (hd : d ≠ 0)
    (hint : ∀ x ∈ S, IsIntegral ℤ (d • x)) :
    ∃ F : Polynomial ℤ, Polynomial.eval 0 F ≠ 0 ∧
      ∀ x ∈ S, x ≠ 0 → Polynomial.aeval ((x : K) : ℂ) F = 0 := by
  have hpt : ∀ x : K, ((d : ℂ) * (x : ℂ)) = algebraMap K ℂ (d • x) := by
    intro x
    rw [map_zsmul, zsmul_eq_mul, IntermediateField.algebraMap_apply]
  have hintC : ∀ i : ↥S, IsIntegral ℤ ((d : ℂ) * ((i : K) : ℂ)) := by
    intro i
    rw [hpt]
    exact IsIntegral.map (algebraMap K ℂ).toIntAlgHom (hint i.1 i.2)
  obtain ⟨F₀, _, hF₀0, hF₀van⟩ :=
    lw_exists_int_poly_eval_zero_ne_zero_of_isIntegral
      (fun i : ↥S => (d : ℂ) * ((i : K) : ℂ)) hintC
  refine ⟨F₀.comp (Polynomial.C d * Polynomial.X), ?_, ?_⟩
  · have heval : Polynomial.eval 0 (Polynomial.C d * Polynomial.X) = 0 := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero]
    rw [Polynomial.eval_comp, heval]
    exact hF₀0
  · intro x hx hx0
    have hae : Polynomial.aeval ((x : K) : ℂ) (F₀.comp (Polynomial.C d * Polynomial.X))
        = Polynomial.aeval ((d : ℂ) * (x : ℂ)) F₀ := by
      have hq : Polynomial.aeval ((x : K) : ℂ) (Polynomial.C d * Polynomial.X)
          = (d : ℂ) * (x : ℂ) := by
        simp [map_mul, Polynomial.aeval_X, eq_intCast]
      rw [Polynomial.aeval_comp, hq]
    rw [hae]
    have hxC : ((x : K) : ℂ) ≠ 0 := fun h => hx0 (lw_coe_injective h)
    have hne : (d : ℂ) * ((⟨x, hx⟩ : ↥S).val : ℂ) ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hd) hxC
    exact hF₀van ⟨x, hx⟩ hne

open Classical in
/-- Galois-invariant weighted sums are integers. -/
private theorem lw_weight_sum_eq_intCast {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (S : Finset K) (w : K → ℤ) (d : ℤ)
    (hint : ∀ x ∈ S, IsIntegral ℤ (d • x))
    (hstab : ∀ τ : (K ≃ₐ[ℚ] K), ∀ x : K, (x ∈ S ↔ τ x ∈ S) ∧ w (τ x) = w x)
    (g : Polynomial ℤ) :
    ∃ z : ℤ, ∑ x ∈ S, (w x : ℂ) * Polynomial.aeval ((d : ℂ) * (x : ℂ)) g
      = (z : ℂ) := by
  have hT : IsIntegral ℤ
      (∑ x ∈ S, ((w x : ℤ) : K) * Polynomial.aeval (d • x) g) := by
    refine IsIntegral.sum _ fun x hx => ?_
    have hsm : (((w x : ℤ) : K) * Polynomial.aeval (d • x) g)
        = (w x) • Polynomial.aeval (d • x) g := (zsmul_eq_mul _ _).symm
    have hae : Polynomial.aeval (d • x) g
        = ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i • (d • x) ^ i :=
      Polynomial.aeval_eq_sum_range (R := ℤ) (S := K) (d • x)
    rw [hsm]
    refine IsIntegral.zsmul (R := ℤ) (B := K) ?_ (w x)
    rw [hae]
    refine IsIntegral.sum (R := ℤ) (A := K) (fun i => g.coeff i • (d • x) ^ i)
      fun i _ => ?_
    exact IsIntegral.zsmul (R := ℤ) (B := K) (IsIntegral.pow (hint x hx) i) _
  have hcomm : ∀ (τ : (K ≃ₐ[ℚ] K)) (x : K),
      τ (Polynomial.aeval (d • x) g) = Polynomial.aeval (d • τ x) g := by
    intro τ x
    have e := Polynomial.aeval_algHom_apply ((τ : K →+* K).toIntAlgHom) (d • x) g
    have ez : ((τ : K →+* K).toIntAlgHom) (d • x) = d • τ x := by
      have h1 : (τ : K →+* K) (d • x) = d • τ x := map_zsmul _ _ _
      exact h1
    rw [ez] at e
    exact e.symm
  have hinv : ∀ τ : (K ≃ₐ[ℚ] K),
      τ (∑ x ∈ S, ((w x : ℤ) : K) * Polynomial.aeval (d • x) g)
        = ∑ x ∈ S, ((w x : ℤ) : K) * Polynomial.aeval (d • x) g := by
    intro τ
    rw [map_sum]
    refine Finset.sum_nbij' (fun x => τ x) (fun x => τ.symm x) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact (hstab τ a).1.mp ha
    · intro a ha
      have h2 := (hstab τ (τ.symm a)).1
      rw [AlgEquiv.apply_symm_apply] at h2
      exact h2.mpr ha
    · intro a _
      exact AlgEquiv.symm_apply_apply τ a
    · intro a _
      exact AlgEquiv.apply_symm_apply τ a
    · intro a ha
      rw [map_mul, map_intCast, hcomm τ a, ← (hstab τ a).2]
  obtain ⟨q, hq⟩ := lw_exists_rat_of_forall_aut_eq _ hinv
  have hTq : IsIntegral ℤ (algebraMap ℚ K q) := by
    rw [hq]
    exact hT
  obtain ⟨z, hz⟩ := lw_exists_int_of_isIntegral_rat q hTq
  have hterm : ∀ x ∈ S, algebraMap K ℂ (((w x : ℤ) : K) * Polynomial.aeval (d • x) g)
      = (w x : ℂ) * Polynomial.aeval ((d : ℂ) * (x : ℂ)) g := by
    intro x _
    rw [map_mul, map_intCast]
    congr 1
    have e := Polynomial.aeval_algHom_apply (R := ℤ) (A := K) (B := ℂ)
      ((algebraMap K ℂ).toIntAlgHom) (d • x) g
    have ez : ((algebraMap K ℂ).toIntAlgHom) (d • x) = (d : ℂ) * (x : ℂ) := by
      have h1 : algebraMap K ℂ (d • x) = (d : ℂ) * (x : ℂ) := by
        rw [map_zsmul, zsmul_eq_mul, IntermediateField.algebraMap_apply]
      exact h1
    rw [ez] at e
    exact e.symm
  have hsum : (∑ x ∈ S, (w x : ℂ) * Polynomial.aeval ((d : ℂ) * (x : ℂ)) g)
      = algebraMap K ℂ
        (∑ x ∈ S, ((w x : ℤ) : K) * Polynomial.aeval (d • x) g) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun x hx => (hterm x hx).symm)
  refine ⟨z, ?_⟩
  rw [hsum, ← hq, ← IsScalarTower.algebraMap_apply ℚ K ℂ]
  have e1 : algebraMap ℚ ℂ q = ((q : ℚ) : ℂ) := eq_ratCast _ _
  have e2 : (((z : ℤ) : ℚ) : ℂ) = ((z : ℤ) : ℂ) := Rat.cast_intCast z
  rw [e1, ← hz, e2]

/-- Copy: a prime larger than `A` with the factorial estimate below one. -/
private theorem lw_exists_prime_gt_mul_pow_div_factorial_lt_one (C : ℝ) (hC : 0 ≤ C)
    (W : ℝ) (hW : 0 ≤ W) (A : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ A < p ∧ W * C ^ p / ((p - 1).factorial : ℝ) < 1 := by
  have htend : Filter.Tendsto (fun n : ℕ => C ^ n / ((n.factorial : ℝ))) Filter.atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop C
  have htendW : Filter.Tendsto (fun n : ℕ => W * C * (C ^ n / ((n.factorial : ℝ))))
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = W * C * 0 := by ring
    rw [h0]
    exact Filter.Tendsto.const_mul _ htend
  rw [Metric.tendsto_atTop] at htendW
  obtain ⟨N0, hN0⟩ := htendW 1 (by norm_num)
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (max N0 (A + 1) + 1)
  have hAle : A + 1 ≤ p := by
    have h1 : A + 1 ≤ max N0 (A + 1) := Nat.le_max_right _ _
    have h2 : max N0 (A + 1) ≤ p := by omega
    omega
  have hN0le : N0 ≤ p - 1 := by
    have h1 : N0 ≤ max N0 (A + 1) := Nat.le_max_left _ _
    have h2 : max N0 (A + 1) ≤ p - 1 := by omega
    omega
  refine ⟨p, hpprime, by omega, ?_⟩
  have hCeq : C ^ p = C * C ^ (p - 1) := by
    have hpeq : p = (p - 1) + 1 := by omega
    conv_lhs => rw [hpeq, pow_succ']
  have hrewrite : W * C ^ p / (((p - 1).factorial : ℕ) : ℝ)
      = W * C * (C ^ (p - 1) / ((((p - 1).factorial : ℕ)) : ℝ)) := by
    rw [hCeq]; ring
  rw [hrewrite]
  have hnn : 0 ≤ W * C * (C ^ (p - 1) / ((((p - 1).factorial : ℕ)) : ℝ)) := by
    apply mul_nonneg (mul_nonneg hW hC)
    apply div_nonneg (pow_nonneg hC _)
    positivity
  have hmem := hN0 (p - 1) hN0le
  rw [dist_zero_right, Real.norm_of_nonneg hnn] at hmem
  exact hmem

open Classical in
/-- Scaled Hermite identity. -/
private theorem lw_scaled_identity {ι : Type*} [Fintype ι]
    (w : ι → ℤ) (γ : ι → ℂ) (d : ℤ)
    (h1 : ∑ i, (w i : ℂ) * Complex.exp (γ i) = 0)
    (h4 : ∀ g : Polynomial ℤ, ∃ z : ℤ,
      ∑ i, (w i : ℂ) * Polynomial.aeval ((d : ℂ) * γ i) g = (z : ℂ))
    (np : ℤ) (p : ℕ) (gp : Polynomial ℤ) :
    ∃ z : ℤ, ∑ i, (w i : ℂ) * ((d : ℂ) ^ gp.natDegree
        * ((np : ℂ) * Complex.exp (γ i) - (p : ℂ) * Polynomial.aeval (γ i) gp))
      = -((p : ℂ) * (z : ℂ)) := by
  have key : ∀ i, Polynomial.aeval ((d : ℂ) * γ i) (gp.scaleRoots d)
      = (d : ℂ) ^ gp.natDegree * Polynomial.aeval (γ i) gp := by
    intro i
    have e := Polynomial.scaleRoots_aeval_smul (S := ℤ) (R := ℂ) (p := gp)
      (γ i) (d : ℤ)
    simp only [Algebra.smul_def, map_pow, eq_intCast] at e
    exact e
  obtain ⟨z, hz⟩ := h4 (gp.scaleRoots d)
  have hzD : (∑ i, ((w i : ℂ))
        * ((d : ℂ) ^ gp.natDegree * Polynomial.aeval (γ i) gp))
      = ((z : ℤ) : ℂ) := by
    rw [← hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i]
  have hnp_mul : (∑ i, (np : ℂ) * (((w i : ℂ)) * Complex.exp (γ i))) = 0 := by
    rw [← Finset.mul_sum, h1, mul_zero]
  refine ⟨z, ?_⟩
  have hsub : (∑ i, (w i : ℂ) * ((d : ℂ) ^ gp.natDegree
        * ((np : ℂ) * Complex.exp (γ i) - (p : ℂ) * Polynomial.aeval (γ i) gp)))
      = (d : ℂ) ^ gp.natDegree * (∑ i, (np : ℂ) * (((w i : ℂ)) * Complex.exp (γ i)))
        - (d : ℂ) ^ gp.natDegree
          * ((p : ℂ) * (∑ i, ((w i : ℂ)) * Polynomial.aeval (γ i) gp)) := by
    have hfac : (∑ i, (w i : ℂ) * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i) - (p : ℂ) * Polynomial.aeval (γ i) gp)))
        = (d : ℂ) ^ gp.natDegree * (∑ i, ((w i : ℂ)
          * ((np : ℂ) * Complex.exp (γ i) - (p : ℂ) * Polynomial.aeval (γ i) gp))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hsplit : (∑ i, ((w i : ℂ)
          * ((np : ℂ) * Complex.exp (γ i) - (p : ℂ) * Polynomial.aeval (γ i) gp)))
        = (∑ i, (np : ℂ) * (((w i : ℂ)) * Complex.exp (γ i)))
          - (p : ℂ) * (∑ i, ((w i : ℂ)) * Polynomial.aeval (γ i) gp) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfac, hsplit, mul_sub]
  have hzD' : (d : ℂ) ^ gp.natDegree
        * (∑ i, ((w i : ℂ)) * Polynomial.aeval (γ i) gp) = ((z : ℤ) : ℂ) := by
    rw [Finset.mul_sum, ← hzD]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsub, hnp_mul, mul_zero, zero_sub]
  congr 1
  rw [← mul_assoc, mul_comm ((d : ℂ) ^ gp.natDegree) (p : ℂ), mul_assoc, hzD']

open Classical in
/-- Zero part and error bound. -/
private theorem lw_zero_error {ι : Type*} [Fintype ι]
    (w : ι → ℤ) (γ : ι → ℂ) (d : ℤ) (hd : d ≠ 0)
    (F : Polynomial ℤ) (hF0 : Polynomial.eval 0 F ≠ 0)
    (hFvan : ∀ i, γ i ≠ 0 → Polynomial.aeval (γ i) F = 0)
    (c : ℝ) (np : ℤ) (p : ℕ) (gp : Polynomial ℤ)
    (hdeg : gp.natDegree ≤ p * F.natDegree - 1)
    (hb : ∀ r ∈ F.aroots ℂ,
      ‖np • Complex.exp r - (p : ℕ) • Polynomial.aeval r gp‖
        ≤ c ^ p / ((((p - 1).factorial : ℕ)) : ℝ)) :
    (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), (w i : ℂ)
        * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp)))
      = (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * (np - (p : ℤ) * gp.eval 0) : ℤ) : ℂ)
    ∧ ‖∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0), (w i : ℂ)
        * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp))‖
      ≤ (∑ i, |(w i : ℝ)|) * (|c| * |(d : ℝ)| ^ F.natDegree) ^ p
        / ((((p - 1).factorial : ℕ)) : ℝ) := by
  constructor
  · have hterm : ∀ i ∈ Finset.univ.filter (fun i => γ i = 0),
        (w i : ℂ) * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp))
        = ((w i : ℤ) : ℂ) * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) - (p : ℂ) * ((((gp.eval 0 : ℤ))) : ℂ))) := by
      intro i hi
      have hzi : γ i = 0 := (Finset.mem_filter.mp hi).2
      have h1 : Polynomial.aeval (0 : ℂ) gp = ((((gp.eval 0 : ℤ))) : ℂ) := by
        have h := Polynomial.coeff_zero_eq_aeval_zero' (R := ℤ)
          (A := ℂ) gp
        have halg : (algebraMap ℤ ℂ) (gp.coeff 0)
            = ((((gp.coeff 0 : ℤ))) : ℂ) := by
          simp
        rw [halg, Polynomial.coeff_zero_eq_eval_zero] at h
        exact h.symm
      rw [hzi, Complex.exp_zero, mul_one, h1]
    have hstep : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          (w i : ℂ) * ((d : ℂ) ^ gp.natDegree
            * ((np : ℂ) * Complex.exp (γ i)
              - (p : ℂ) * Polynomial.aeval (γ i) gp)))
        = ∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          ((w i : ℤ) : ℂ) * ((d : ℂ) ^ gp.natDegree
            * ((np : ℂ) - (p : ℂ) * ((((gp.eval 0 : ℤ))) : ℂ))) :=
      Finset.sum_congr rfl hterm
    have hcast : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
          ((w i : ℤ) : ℂ))
        = (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i
          : ℤ)) : ℂ) :=
      (Int.cast_sum _ _).symm
    rw [hstep, ← Finset.sum_mul, hcast]
    have hexpand : (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * (np - (p : ℤ) * gp.eval 0) : ℤ) : ℂ)
        = (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i : ℤ)) : ℂ)
          * ((d : ℂ) ^ gp.natDegree
            * ((np : ℂ) - (p : ℂ) * ((((gp.eval 0 : ℤ))) : ℂ))) := by
      push_cast
      ring
    exact hexpand.symm
  · have hFne : F ≠ 0 := fun h => hF0 (by rw [h, Polynomial.eval_zero])
    have hinj : Function.Injective (algebraMap ℤ ℂ) := by
      intro a b hab
      have e1 := eq_intCast (algebraMap ℤ ℂ) a
      have e2 := eq_intCast (algebraMap ℤ ℂ) b
      rw [e1, e2] at hab
      exact Int.cast_injective hab
    have hmapne : F.map (algebraMap ℤ ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinj).mpr hFne
    have hFpos : (0 : ℝ) < ((((p - 1).factorial : ℕ)) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hcp : c ^ p ≤ |c| ^ p := by
      rw [← abs_pow]
      exact le_abs_self _
    have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by
      have h := Int.one_le_abs hd
      have hc : ((1 : ℤ) : ℝ) ≤ ((|d| : ℤ) : ℝ) := by exact_mod_cast h
      rw [Int.cast_one, Int.cast_abs] at hc
      exact hc
    have hdpow : |(d : ℝ)| ^ gp.natDegree ≤ (|(d : ℝ)| ^ F.natDegree) ^ p := by
      have h1 : |(d : ℝ)| ^ gp.natDegree ≤ |(d : ℝ)| ^ (p * F.natDegree) :=
        pow_le_pow_right₀ hd1 (le_trans hdeg (Nat.sub_le _ _))
      rw [mul_comm p (F.natDegree), pow_mul] at h1
      exact h1
    refine (norm_sum_le _ _).trans ?_
    have hper : ∀ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
        ‖((w i : ℤ) : ℂ)
          * ((d : ℂ) ^ gp.natDegree
            * ((np : ℂ) * Complex.exp (γ i)
              - (p : ℂ) * Polynomial.aeval (γ i) gp))‖
        ≤ |(w i : ℝ)|
          * (((|c| * |(d : ℝ)| ^ F.natDegree) ^ p
            / ((((p - 1).factorial : ℕ)) : ℝ))) := by
      intro i hi
      have hmem : γ i ≠ 0 := (Finset.mem_filter.mp hi).2
      have hroot : γ i ∈ F.aroots ℂ := by
        rw [Polynomial.mem_aroots']
        exact ⟨hmapne, hFvan i hmem⟩
      have hb0 := hb (γ i) hroot
      rw [zsmul_eq_mul, nsmul_eq_mul] at hb0
      have hXi : ‖(np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp‖
          ≤ |c| ^ p / ((((p - 1).factorial : ℕ)) : ℝ) := by
        refine hb0.trans ?_
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hcp
          (inv_nonneg.mpr (le_of_lt hFpos))
      have hterm : ‖((w i : ℤ) : ℂ)
            * ((d : ℂ) ^ gp.natDegree
              * ((np : ℂ) * Complex.exp (γ i)
                - (p : ℂ) * Polynomial.aeval (γ i) gp))‖
          = |(w i : ℝ)| * (|(d : ℝ)| ^ gp.natDegree
            * ‖(np : ℂ) * Complex.exp (γ i)
              - (p : ℂ) * Polynomial.aeval (γ i) gp‖) := by
        rw [norm_mul, norm_mul, Complex.norm_intCast, norm_pow,
          Complex.norm_intCast]
      rw [hterm]
      have hle : |(d : ℝ)| ^ gp.natDegree
            * ‖(np : ℂ) * Complex.exp (γ i)
              - (p : ℂ) * Polynomial.aeval (γ i) gp‖
          ≤ (|c| * |(d : ℝ)| ^ F.natDegree) ^ p
            / ((((p - 1).factorial : ℕ)) : ℝ) := by
        calc |(d : ℝ)| ^ gp.natDegree
                * ‖(np : ℂ) * Complex.exp (γ i)
                  - (p : ℂ) * Polynomial.aeval (γ i) gp‖
            ≤ (|(d : ℝ)| ^ F.natDegree) ^ p * (|c| ^ p
              / ((((p - 1).factorial : ℕ)) : ℝ)) :=
              mul_le_mul hdpow hXi (by positivity) (by positivity)
          _ = (|c| * |(d : ℝ)| ^ F.natDegree) ^ p
              / ((((p - 1).factorial : ℕ)) : ℝ) := by
              rw [mul_pow]
              ring
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    refine (Finset.sum_le_sum hper).trans ?_
    have hsub : (∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0),
          |(w i : ℝ)| * (((|c| * |(d : ℝ)| ^ F.natDegree) ^ p
            / ((((p - 1).factorial : ℕ)) : ℝ))))
        ≤ ∑ i, |(w i : ℝ)|
          * (((|c| * |(d : ℝ)| ^ F.natDegree) ^ p
            / ((((p - 1).factorial : ℕ)) : ℝ))) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x _ => Finset.mem_univ x)
        (fun i _ _ => by positivity)
    have hfac : (∑ i, |(w i : ℝ)|
          * (((|c| * |(d : ℝ)| ^ F.natDegree) ^ p
            / ((((p - 1).factorial : ℕ)) : ℝ))))
        = (∑ i, |(w i : ℝ)|) * (|c| * |(d : ℝ)| ^ F.natDegree) ^ p
          / ((((p - 1).factorial : ℕ)) : ℝ) := by
      rw [← Finset.sum_mul, mul_div_assoc]
    exact hsub.trans (le_of_eq hfac)

open Classical in
/-- Arithmetic core with a denominator. -/
private theorem lw_arith_core {ι : Type*} [Fintype ι]
    (w : ι → ℤ) (γ : ι → ℂ) (d : ℤ) (hd : d ≠ 0)
    (h1 : ∑ i, (w i : ℂ) * Complex.exp (γ i) = 0)
    (h2 : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i) ≠ 0)
    (h3 : ∃ F : Polynomial ℤ, Polynomial.eval 0 F ≠ 0 ∧
      ∀ i, γ i ≠ 0 → Polynomial.aeval (γ i) F = 0)
    (h4 : ∀ g : Polynomial ℤ, ∃ z : ℤ,
      ∑ i, (w i : ℂ) * Polynomial.aeval ((d : ℂ) * γ i) g = (z : ℂ)) :
    False := by
  obtain ⟨F, hF0, hFvan⟩ := h3
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx F hF0
  obtain ⟨p, hpprime, hpA, hplt⟩ :=
    lw_exists_prime_gt_mul_pow_div_factorial_lt_one (|c| * |(d : ℝ)| ^ F.natDegree)
      (by positivity)
      (∑ i, |(w i : ℝ)|)
      (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      (max (Polynomial.eval 0 F).natAbs
        (max (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i).natAbs d.natAbs))
  have hpF : (Polynomial.eval 0 F).natAbs < p :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hpA
  have hpq : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i).natAbs < p :=
    lt_of_le_of_lt
      (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hpA
  have hpd : d.natAbs < p :=
    lt_of_le_of_lt
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hpA
  obtain ⟨np, hnp, gp, hgpdeg, hgpbound⟩ := hc p hpF hpprime
  obtain ⟨z, hz⟩ := lw_scaled_identity w γ d h1 h4 np p gp
  obtain ⟨hzero, hbound⟩ := lw_zero_error w γ d hd F hF0 hFvan c np p gp hgpdeg
    (fun r hr => hgpbound hr)
  have hsplit : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), (w i : ℂ)
        * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp)))
      + (∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0), (w i : ℂ)
        * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp)))
      = ∑ i, (w i : ℂ) * ((d : ℂ) ^ gp.natDegree
        * ((np : ℂ) * Complex.exp (γ i)
          - (p : ℂ) * Polynomial.aeval (γ i) gp)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hNS : (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * np
        + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * d ^ gp.natDegree * gp.eval 0) : ℤ) : ℂ)
      + (∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0), (w i : ℂ)
        * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp))) = 0 := by
    have h3 := hsplit
    rw [hz, hzero] at h3
    push_cast at h3
    have hexpand : (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * d ^ gp.natDegree * np
          + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
            * d ^ gp.natDegree * gp.eval 0) : ℤ) : ℂ)
          = (np : ℂ) * (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
              * d ^ gp.natDegree : ℤ) : ℂ)
            + (p : ℂ) * ((z : ℂ)
              - (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
                * d ^ gp.natDegree : ℤ) : ℂ) * (((gp.eval 0 : ℤ))) ) := by
      push_cast
      ring
    rw [hexpand]
    push_cast at h3 ⊢
    linear_combination h3
  have hNeq : (((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * np
        + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * d ^ gp.natDegree * gp.eval 0) : ℤ) : ℂ)
      = -(∑ i ∈ Finset.univ.filter (fun i => ¬γ i = 0), (w i : ℂ)
        * ((d : ℂ) ^ gp.natDegree
          * ((np : ℂ) * Complex.exp (γ i)
            - (p : ℂ) * Polynomial.aeval (γ i) gp))) :=
    eq_neg_of_add_eq_zero_left hNS
  have hnorm_lt : ‖(((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * np
        + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * d ^ gp.natDegree * gp.eval 0) : ℤ) : ℂ)‖ < 1 := by
    rw [hNeq, norm_neg]
    exact lt_of_le_of_lt hbound hplt
  have hpN : ¬ (p : ℤ) ∣ ((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * np
        + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * d ^ gp.natDegree * gp.eval 0)) := by
    intro hdiv
    have hdvd : (p : ℤ) ∣ (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * np := by
      have h1 : (p : ℤ) ∣ ((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
          * d ^ gp.natDegree * np
          + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
            * d ^ gp.natDegree * gp.eval 0)) := hdiv
      have h2 : (p : ℤ) ∣ (p : ℤ)
          * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
            * d ^ gp.natDegree * gp.eval 0) :=
        dvd_mul_right _ _
      have h3 := dvd_sub h1 h2
      have heq : ((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
            * d ^ gp.natDegree * np
            + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
              * d ^ gp.natDegree * gp.eval 0))
            - (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
              * d ^ gp.natDegree * gp.eval 0)
            = (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
              * d ^ gp.natDegree * np := by ring
      rwa [heq] at h3
    have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
    rcases hprime.dvd_mul.mp hdvd with hleft | hnp'
    · rcases hprime.dvd_mul.mp hleft with hq0' | hdvd_pow
      · have hlt : (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
            w i).natAbs < p := hpq
        have hpos : 0 < (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
            w i).natAbs :=
          Int.natAbs_pos.mpr h2
        have hle : p ≤ (∑ i ∈ Finset.univ.filter (fun i => γ i = 0),
            w i).natAbs := by
          have h1 : (p : ℤ).natAbs ∣ (∑ i ∈ Finset.univ.filter
              (fun i => γ i = 0), w i).natAbs :=
            Int.natAbs_dvd_natAbs.mpr hq0'
          rw [Int.natAbs_natCast] at h1
          exact Nat.le_of_dvd hpos h1
        omega
      · have hpdvd : (p : ℤ) ∣ d := hprime.dvd_of_dvd_pow hdvd_pow
        have hlt : d.natAbs < p := hpd
        have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd
        have hle : p ≤ d.natAbs := by
          have h1 : (p : ℤ).natAbs ∣ d.natAbs :=
            Int.natAbs_dvd_natAbs.mpr hpdvd
          rw [Int.natAbs_natCast] at h1
          exact Nat.le_of_dvd hpos h1
        omega
    · exact hnp hnp'
  have hNne : ((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
      * d ^ gp.natDegree * np
      + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * gp.eval 0)) ≠ 0 := by
    intro h0
    apply hpN
    rw [h0]
    exact dvd_zero _
  have hNlt : (((|((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
      * d ^ gp.natDegree * np
      + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * gp.eval 0))| : ℤ)) : ℝ) < 1 := by
    have h1 := hnorm_lt
    rw [Complex.norm_intCast, ← Int.cast_abs] at h1
    exact h1
  have h1le : (1 : ℝ) ≤ (((|((∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
      * d ^ gp.natDegree * np
      + (p : ℤ) * (z - (∑ i ∈ Finset.univ.filter (fun i => γ i = 0), w i)
        * d ^ gp.natDegree * gp.eval 0))| : ℤ)) : ℝ) :=
    by exact_mod_cast Int.one_le_abs hNne
  linarith

open Classical in
/-- Assembly auxiliary: the group-ring data derives `False`. -/
private theorem lw_false_of_data {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {ι : Type*} [Fintype ι] (a b : ι → K)
    (ha : Function.Injective (fun i => ((a i : K) : ℂ)))
    (i₀ : ι) (hb : ((b i₀ : K) : ℂ) ≠ 0)
    (hsum : ∑ i, ((b i : K) : ℂ) * Complex.exp ((a i : K) : ℂ) = 0) :
    False := by
  obtain ⟨hev, hE0⟩ := lw_initial a b ha i₀ hb
  have hev0 : lw_evK (∑ i, AddMonoidAlgebra.single (a i) (b i)) = 0 :=
    hev.trans hsum
  obtain ⟨hE1ne, hE1ev, hE1fix⟩ := lw_coeffNorm_props _ hE0 hev0
  obtain ⟨E₂, _, hE2ne, hE2ev⟩ := lw_descend _ hE1ne hE1ev hE1fix
  obtain ⟨hE3ne, hE3ev, hE3inv⟩ := lw_expNorm_props E₂ hE2ne hE2ev
  obtain ⟨hE4ev, hE4inv, hE4pos⟩ :=
    lw_reflect (lw_expNorm E₂) hE3ne hE3ev hE3inv
  obtain ⟨S, w, hS0, hw0, hwinv, hsumS⟩ :=
    lw_weights (lw_expNorm E₂ * lw_refl (lw_expNorm E₂)) hE4ev hE4inv hE4pos
  obtain ⟨d, hd, hdintegral⟩ := lw_common_denom S
  obtain ⟨F, hF0, hFvan⟩ := lw_aux_poly S d hd hdintegral
  have h4 : ∀ g : Polynomial ℤ, ∃ z : ℤ,
      ∑ x ∈ S, (w x : ℂ) * Polynomial.aeval ((d : ℂ) * (x : ℂ)) g = (z : ℂ) := by
    intro g
    exact lw_weight_sum_eq_intCast S w d hdintegral
      (fun τ x => ⟨(hwinv τ x).2, (hwinv τ x).1⟩) g
  have h1 : ∑ i : ↥S, (((w ((i : K)) : ℤ)) : ℂ)
      * Complex.exp ((((i : K)) : ℂ)) = 0 := by
    rw [Finset.sum_coe_sort (s := S)
      (f := fun x : K => (w x : ℂ) * Complex.exp (x : ℂ))]
    exact hsumS
  have h2 : (∑ i ∈ Finset.univ.filter (fun i : ↥S => ((((i : K)) : ℂ) = 0)),
      w ((i : K))) ≠ 0 := by
    have hfil : Finset.univ.filter (fun i : ↥S => ((((i : K)) : ℂ) = 0))
        = {⟨0, hS0⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hi
        exact Subtype.ext (lw_coe_injective hi)
      · intro hi
        subst hi
        rfl
    rw [hfil, Finset.sum_singleton]
    exact ne_of_gt hw0
  have h3 : ∃ F : Polynomial ℤ, Polynomial.eval 0 F ≠ 0 ∧
      ∀ i : ↥S, ((((i : K)) : ℂ) ≠ 0
        → Polynomial.aeval ((((i : K)) : ℂ)) F = 0) := by
    refine ⟨F, hF0, fun i hi => ?_⟩
    have hxS : (i : K) ∈ S := i.2
    have hx0 : (i : K) ≠ 0 := by
      intro h
      apply hi
      rw [← IntermediateField.algebraMap_apply, h, map_zero]
    exact hFvan _ hxS hx0
  have h4' : ∀ g : Polynomial ℤ, ∃ z : ℤ,
      ∑ i : ↥S, (((w ((i : K)) : ℤ)) : ℂ)
        * Polynomial.aeval ((d : ℂ) * ((((i : K)) : ℂ))) g = (z : ℂ) := by
    intro g
    obtain ⟨z, hz⟩ := h4 g
    refine ⟨z, ?_⟩
    rw [← hz, Finset.sum_coe_sort (s := S)
      (f := fun x : K => (w x : ℂ) * Polynomial.aeval ((d : ℂ) * (x : ℂ)) g)]
  exact lw_arith_core (fun x : ↥S => w (x : K)) (fun x : ↥S => (((x : K)) : ℂ))
    d hd h1 h2 h3 h4'

/-- **Lindemann–Weierstrass theorem (universe-polymorphic form).** Let $\iota$ be a finite index
set, let $\alpha_i$ ($i \in \iota$) be pairwise distinct complex numbers that are algebraic over
$\mathbb{Q}$, and let $\beta_i$ ($i \in \iota$) be complex numbers that are algebraic over
$\mathbb{Q}$ and not all zero. Then $\sum_{i \in \iota} \beta_i e^{\alpha_i} \neq 0$. -/
public theorem lindemann_weierstrass' :
    ∀ {ι : Type*} [Fintype ι] (α : ι → ℂ),
      Function.Injective α → (∀ i, IsAlgebraic ℚ (α i)) →
        ∀ (β : ι → ℂ), (∀ i, IsAlgebraic ℚ (β i)) → (∃ i, β i ≠ 0) →
          ∑ i, β i * Complex.exp (α i) ≠ 0 := by
  intro ι _ α hαinj hαalg β hβalg hβne hsum
  classical
  obtain ⟨i₀, hi₀⟩ := hβne
  obtain ⟨K, hfin, hgal, hmem⟩ := lw_exists_splitting_field α β hαalg hβalg
  refine @lw_false_of_data K hfin hgal ι inferInstance
    (fun i => ⟨α i, (hmem i).1⟩) (fun i => ⟨β i, (hmem i).2⟩) ?_ i₀ ?_ ?_
  · have e : (fun i => (((⟨α i, (hmem i).1⟩ : K)) : ℂ)) = α := rfl
    rw [e]
    exact hαinj
  · exact hi₀
  · exact hsum

/--
**Lindemann–Weierstrass theorem.** Let $\iota$ be a finite index set, let $\alpha_i$
($i \in \iota$) be pairwise distinct complex numbers that are algebraic over $\mathbb{Q}$, and let
$\beta_i$ ($i \in \iota$) be complex numbers that are algebraic over $\mathbb{Q}$ and not all
zero. Then $\sum_{i \in \iota} \beta_i e^{\alpha_i} \neq 0$.

Proves `Wanted` entry `lindemann_weierstrass`.

Source: F.
von Lindemann 1882 and K. Weierstrass, Zu Lindemann's Abhandlung Über die Ludolph'sche Zahl, 1885;
textbook in Baker, Transcendental Number Theory
-/
public theorem lindemann_weierstrass :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (α : ι → ℂ),
      Function.Injective α → (∀ i, IsAlgebraic ℚ (α i)) →
        ∀ (β : ι → ℂ), (∀ i, IsAlgebraic ℚ (β i)) → (∃ i, β i ≠ 0) →
          ∑ i, β i * Complex.exp (α i) ≠ 0 := by
  intro ι _ _ α hαinj hαalg β hβalg hβne hsum
  exact lindemann_weierstrass' α hαinj hαalg β hβalg hβne hsum

end MathlibExt.NumberTheory.LindemannWeierstrassWanted
end
