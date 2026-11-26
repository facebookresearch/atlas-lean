/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation.lean`
and
`P2M/Sol/S_Algebra_FiniteType_of_faithfullyFlat_of_finitePresentation.lean`
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

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteStability
import MathlibExt.RingTheory.Flat.FGSubalgebraTensorProduct

/-!
# Descent of finite type along faithfully flat, finitely presented algebras

In a tower `R → A → B` where `B` is faithfully flat and finitely presented over `A`, if `B` is of
finite type over `R`, then so is `A`. The proof uses Noetherian approximation of flatness
(`Module.Flat.exists_fg_subalgebra_flat_tensorProduct`).

## Main results

* `Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation`

## References

* [Stacks Project, Lemma 35.14.2 (Tag 0367)](https://stacks.math.columbia.edu/tag/0367)
-/

@[expose] public section

universe u v w

open TensorProduct

noncomputable section

namespace FiniteTypeOfFaithfullyFlatAux

section Lift

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {σ : Type*}

private theorem exists_map_eq_of_coeff_mem (E : Subalgebra R A) (g : MvPolynomial σ A)
    (hg : ∀ m, g.coeff m ∈ E) :
    ∃ g₀ : MvPolynomial σ E, MvPolynomial.map (algebraMap E A) g₀ = g := by
  classical
  refine ⟨∑ m ∈ g.support, MvPolynomial.monomial m ⟨g.coeff m, hg m⟩, ?_⟩
  rw [map_sum]
  conv_rhs => rw [g.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial]
  rfl

open scoped Classical in
private def coeffSet (g : MvPolynomial σ A) : Finset A := g.support.image fun m => g.coeff m

private theorem coeff_mem_of_coeffSet_subset (E : Subalgebra R A) (g : MvPolynomial σ A)
    (h : ↑(coeffSet g) ⊆ (E : Set A)) (m : σ →₀ ℕ) : g.coeff m ∈ E := by
  classical
  by_cases hm : m ∈ g.support
  · apply h
    simp only [coeffSet, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨m, hm, rfl⟩
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    exact zero_mem E

end Lift

section Model

variable {R₀ A B : Type*} [CommRing R₀] [CommRing A] [CommRing B]
  [Algebra R₀ A] [Algebra A B] {n : ℕ}
  (J₀ : Ideal (MvPolynomial (Fin n) R₀)) (f : MvPolynomial (Fin n) A →ₐ[A] B)

private theorem algebraTensorAlgEquiv_comp_includeRight :
    ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A : _ ≃ₐ[A] _) :
        A ⊗[R₀] MvPolynomial (Fin n) R₀ →+* MvPolynomial (Fin n) A).comp
      (Algebra.TensorProduct.includeRight (R := R₀) (A := A) (B := MvPolynomial (Fin n) R₀) :
        MvPolynomial (Fin n) R₀ →+* A ⊗[R₀] MvPolynomial (Fin n) R₀)
      = MvPolynomial.map (algebraMap R₀ A) := by
  apply RingHom.ext
  intro p
  simp [Algebra.TensorProduct.includeRight_apply]

private theorem ker_eq_map_map (hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f) :
    RingHom.ker f = (J₀.map (Algebra.TensorProduct.includeRight (R := R₀) (A := A))).map
      ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A : _ ≃ₐ[A] _) :
        A ⊗[R₀] MvPolynomial (Fin n) R₀ →+* MvPolynomial (Fin n) A) := by
  rw [← hJ, ← algebraTensorAlgEquiv_comp_includeRight (R₀ := R₀) (A := A) (n := n),
    ← Ideal.map_map]
  rfl

private def modelEquiv (hf : Function.Surjective f)
    (hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f) :
    A ⊗[R₀] (MvPolynomial (Fin n) R₀ ⧸ J₀) ≃ₐ[A] B :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R₀) A (MvPolynomial (Fin n) R₀) A J₀).trans
    ((Ideal.quotientEquivAlg (J₀.map (Algebra.TensorProduct.includeRight (R := R₀) (A := A)))
        (RingHom.ker f) (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A)
        (ker_eq_map_map J₀ f hJ)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf))

private theorem modelEquiv_tmul_mk (hf : Function.Surjective f)
    (hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f)
    (a : A) (g₀ : MvPolynomial (Fin n) R₀) :
    modelEquiv J₀ f hf hJ (a ⊗ₜ Ideal.Quotient.mk J₀ g₀)
      = algebraMap A B a * f (MvPolynomial.map (algebraMap R₀ A) g₀) := by
  change Ideal.quotientKerAlgEquivOfSurjective hf
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A)
        (ker_eq_map_map J₀ f hJ)
        (Algebra.TensorProduct.tensorQuotientEquiv (R := R₀) A (MvPolynomial (Fin n) R₀) A J₀
          (a ⊗ₜ Ideal.Quotient.mk J₀ g₀))) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.quotientKerAlgEquivOfSurjective hf
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A)
        (ker_eq_map_map J₀ f hJ) (Ideal.Quotient.mk _ (a ⊗ₜ g₀))) = _
  rw [Ideal.quotientEquivAlg_mk, Ideal.quotientKerAlgEquivOfSurjective_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul, Algebra.smul_def]

private theorem modelEquiv_one_tmul_mk (hf : Function.Surjective f)
    (hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f)
    (g₀ : MvPolynomial (Fin n) R₀) :
    modelEquiv J₀ f hf hJ (1 ⊗ₜ Ideal.Quotient.mk J₀ g₀)
      = f (MvPolynomial.map (algebraMap R₀ A) g₀) := by
  rw [modelEquiv_tmul_mk, map_one, one_mul]

end Model

section PrimeLift

variable {R₀ S S' C : Type*} [CommRing R₀] [CommRing S] [CommRing S'] [CommRing C]
  [Algebra R₀ S] [Algebra R₀ S'] [Algebra R₀ C]

private theorem mem_range_comap_of_comap_mem (h : S →ₐ[R₀] S') (𝔮' : PrimeSpectrum S')
    (h𝔮 : PrimeSpectrum.comap (h : S →+* S') 𝔮' ∈
      Set.range (PrimeSpectrum.comap (algebraMap S (S ⊗[R₀] C)))) :
    𝔮' ∈ Set.range (PrimeSpectrum.comap (algebraMap S' (S' ⊗[R₀] C))) := by
  set 𝔮 : PrimeSpectrum S := PrimeSpectrum.comap (h : S →+* S') 𝔮' with h𝔮def
  let κ := 𝔮.asIdeal.ResidueField
  let κ' := 𝔮'.asIdeal.ResidueField
  let algR₀κ : Algebra R₀ κ := ((algebraMap S κ).comp (algebraMap R₀ S)).toAlgebra
  let : Module R₀ κ := Algebra.toModule
  have : IsScalarTower R₀ S κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let algR₀κ' : Algebra R₀ κ' := ((algebraMap S' κ').comp (algebraMap R₀ S')).toAlgebra
  let : Module R₀ κ' := Algebra.toModule
  have : IsScalarTower R₀ S' κ' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ : κ →+* κ' := Ideal.ResidueField.map 𝔮.asIdeal 𝔮'.asIdeal (h : S →+* S') rfl
  let algκκ' : Algebra κ κ' := φ.toAlgebra
  let : Module κ κ' := Algebra.toModule
  have hφ : ∀ x : S, φ (algebraMap S κ x) = algebraMap S' κ' (h x) := fun x =>
    Ideal.ResidueField.map_algebraMap _ _ _ rfl x
  have : IsScalarTower R₀ κ κ' := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change algebraMap S' κ' (algebraMap R₀ S' r) = φ (algebraMap S κ (algebraMap R₀ S r))
    rw [hφ, AlgHom.commutes]
  have h1 : Nontrivial (κ ⊗[S] (S ⊗[R₀] C)) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap 𝔮).mpr h𝔮
  have h2 : Nontrivial (κ ⊗[R₀] C) :=
    (Algebra.TensorProduct.cancelBaseChange R₀ S κ κ C).symm.toEquiv.nontrivial
  have : Module.FaithfullyFlat κ κ' := inferInstance
  have h3 : Nontrivial (κ' ⊗[κ] (κ ⊗[R₀] C)) := inferInstance
  have h4 : Nontrivial (κ' ⊗[R₀] C) :=
    (Algebra.TensorProduct.cancelBaseChange R₀ κ κ' κ' C).symm.toEquiv.nontrivial
  have h5 : Nontrivial (κ' ⊗[S'] (S' ⊗[R₀] C)) :=
    (Algebra.TensorProduct.cancelBaseChange R₀ S' κ' κ' C).toEquiv.nontrivial
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap 𝔮').mp h5

end PrimeLift

section Final

variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]

private theorem eq_top_of_faithfullyFlat_of_surjective (E : Subalgebra R₀ A) (C : Type*)
    [CommRing C] [Algebra E C] [Module.FaithfullyFlat E C]
    (hs : Function.Surjective (fun c : C => (1 : A) ⊗ₜ[E] c)) : E = ⊤ := by
  have hsurj : Function.Surjective ((Algebra.linearMap E A).lTensor C) := by
    intro z
    obtain ⟨c, hc⟩ := hs (TensorProduct.comm E C A z)
    refine ⟨c ⊗ₜ (1 : E), ?_⟩
    apply (TensorProduct.comm E C A).injective
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, TensorProduct.comm_tmul]
    exact hc
  rw [Module.FaithfullyFlat.lTensor_surjective_iff_surjective] at hsurj
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨e, rfl⟩ := hsurj x
  exact e.2

end Final

section Core

variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
  (Bq : Type*) [CommRing Bq] [Algebra R₀ Bq]

private def toTop (E : Subalgebra R₀ A) : E ⊗[R₀] Bq →ₐ[R₀] A ⊗[R₀] Bq :=
  Algebra.TensorProduct.map E.val (AlgHom.id R₀ Bq)

private theorem toTop_tmul (E : Subalgebra R₀ A) (e : E) (b : Bq) :
    toTop Bq E (e ⊗ₜ b) = (e : A) ⊗ₜ b := by
  simp [toTop]

private theorem toTop_comp_algebraMap (E : Subalgebra R₀ A) :
    (toTop Bq E : E ⊗[R₀] Bq →+* A ⊗[R₀] Bq).comp (algebraMap E (E ⊗[R₀] Bq))
      = (algebraMap A (A ⊗[R₀] Bq)).comp (algebraMap E A) := by
  apply RingHom.ext
  intro e
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, toTop_tmul]
  rfl

private theorem toTop_surjective
    (hgen : Function.Surjective
      (Algebra.TensorProduct.includeRight : Bq →ₐ[R₀] A ⊗[R₀] Bq))
    (E : Subalgebra R₀ A) : Function.Surjective (toTop Bq E) := by
  intro z
  obtain ⟨b, rfl⟩ := hgen z
  refine ⟨1 ⊗ₜ b, ?_⟩
  rw [toTop_tmul, Algebra.TensorProduct.includeRight_apply]
  rfl

private theorem one_tmul_surjective
    (hgen : Function.Surjective
      (Algebra.TensorProduct.includeRight : Bq →ₐ[R₀] A ⊗[R₀] Bq))
    (E : Subalgebra R₀ A) :
    Function.Surjective (fun c : E ⊗[R₀] Bq => (1 : A) ⊗ₜ[E] c) := by
  intro z
  let ψ := Algebra.TensorProduct.cancelBaseChange R₀ E E A Bq
  have hψ : ∀ c : E ⊗[R₀] Bq, ψ ((1 : A) ⊗ₜ[E] c) = toTop Bq E c := by
    intro c
    induction c using TensorProduct.inductionOn with
    | tmul e b =>
      rw [toTop_tmul, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]
  obtain ⟨c, hc⟩ := toTop_surjective Bq hgen E (ψ z)
  refine ⟨c, ψ.injective ?_⟩
  change ψ ((1 : A) ⊗ₜ[E] c) = ψ z
  rw [hψ, hc]

variable [Algebra.FinitePresentation R₀ Bq]

private theorem isOpen_range_comap (E : Subalgebra R₀ A) [Module.Flat E (E ⊗[R₀] Bq)] :
    IsOpen (Set.range (PrimeSpectrum.comap (algebraMap E (E ⊗[R₀] Bq)))) :=
  (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range

private theorem fg_top_of_faithfullyFlat [Module.FaithfullyFlat A (A ⊗[R₀] Bq)]
    (hgen : Function.Surjective
      (Algebra.TensorProduct.includeRight : Bq →ₐ[R₀] A ⊗[R₀] Bq)) :
    (⊤ : Subalgebra R₀ A).FG := by
  classical
  obtain ⟨E, hEfg, -, hEflat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_tensorProduct (R₀ := R₀) (R := A) (B₀ := Bq) ∅
  have := hEflat
  set U : Set (PrimeSpectrum E) :=
    Set.range (PrimeSpectrum.comap (algebraMap E (E ⊗[R₀] Bq))) with hUdef
  have hUo : IsOpen U := isOpen_range_comap Bq E
  let J : Ideal E := PrimeSpectrum.vanishingIdeal Uᶜ
  have hZ : PrimeSpectrum.zeroLocus (J : Set E) = Uᶜ := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hUo.isClosed_compl.closure_eq]
  have hland : ∀ 𝔭 : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap E A) 𝔭 ∈ U := by
    intro 𝔭
    obtain ⟨𝔔, h𝔔⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := A ⊗[R₀] Bq) 𝔭
    refine ⟨PrimeSpectrum.comap (toTop Bq E : E ⊗[R₀] Bq →+* A ⊗[R₀] Bq) 𝔔, ?_⟩
    apply PrimeSpectrum.ext
    rw [← h𝔔]
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, toTop_comp_algebraMap]
  have hJA : J.map (algebraMap E A) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmem := hland ⟨𝔪, h𝔪.isPrime⟩
    have hzero : PrimeSpectrum.comap (algebraMap E A) ⟨𝔪, h𝔪.isPrime⟩
        ∈ PrimeSpectrum.zeroLocus (J : Set E) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro j hj
      exact Ideal.map_le_iff_le_comap.mp hle hj
    rw [hZ] at hzero
    exact hzero hmem
  have h1 : (1 : A) ∈ Submodule.span A ((algebraMap E A) '' (J : Set E)) := by
    change (1 : A) ∈ J.map (algebraMap E A)
    rw [hJA]
    exact Submodule.mem_top
  rw [Submodule.mem_span_iff_exists_finset_subset] at h1
  obtain ⟨cf, t, hts, -, hsum⟩ := h1
  obtain ⟨gE, hgE⟩ := hEfg
  obtain ⟨E', hE'fg, hsub, hE'flat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_tensorProduct (R₀ := R₀) (R := A) (B₀ := Bq)
      (gE ∪ t.image cf)
  have := hE'flat
  have hEE' : E ≤ E' := by
    rw [← hgE]
    refine Algebra.adjoin_le fun x hx => hsub ?_
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe]
    exact Or.inl hx
  have hcf : ∀ a ∈ t, cf a ∈ E' := fun a ha => hsub (by
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe]
    exact Or.inr ⟨a, ha, rfl⟩)
  have hU' : ∀ 𝔮' : PrimeSpectrum E',
      PrimeSpectrum.comap (Subalgebra.inclusion hEE' : E →+* E') 𝔮' ∈ U := by
    intro 𝔮'
    by_contra hnot
    have hz : PrimeSpectrum.comap (Subalgebra.inclusion hEE' : E →+* E') 𝔮'
        ∈ PrimeSpectrum.zeroLocus (J : Set E) := by
      rw [hZ]; exact hnot
    rw [PrimeSpectrum.mem_zeroLocus] at hz
    have key : ∀ a ∈ t, ∃ x : E', (x : A) = cf a • a ∧ x ∈ 𝔮'.asIdeal := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := hts ha
      refine ⟨⟨cf _, hcf _ ha⟩ * Subalgebra.inclusion hEE' j, ?_, ?_⟩
      · simp only [Subalgebra.coe_mul, smul_eq_mul]
        rfl
      · exact Ideal.mul_mem_left _ _ (hz hj)
    choose x hx hx' using key
    apply 𝔮'.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have hone : (1 : E') = ∑ a ∈ t.attach, x a.1 a.2 := by
      apply Subtype.ext
      rw [OneMemClass.coe_one, AddSubmonoidClass.coe_finsetSum]
      simp_rw [hx]
      rw [Finset.sum_attach t (fun a => cf a • a), hsum]
    rw [hone]
    exact Ideal.sum_mem _ (fun a _ => hx' a.1 a.2)
  have hsurj' : Function.Surjective (PrimeSpectrum.comap (algebraMap E' (E' ⊗[R₀] Bq))) :=
    fun 𝔮' => mem_range_comap_of_comap_mem (Subalgebra.inclusion hEE') 𝔮' (hU' 𝔮')
  have : Module.FaithfullyFlat E' (E' ⊗[R₀] Bq) :=
    Module.FaithfullyFlat.of_comap_surjective hsurj'
  have htop : E' = ⊤ :=
    eq_top_of_faithfullyFlat_of_surjective E' (E' ⊗[R₀] Bq) (one_tmul_surjective Bq hgen E')
  rw [← htop]
  exact hE'fg

end Core

section Assembly

variable {R : Type*} {R₀ A B : Type*} [CommRing R] [CommRing R₀] [CommRing A] [CommRing B]
  [Algebra R R₀] [Algebra R A] [Algebra R B] [Algebra R₀ A] [Algebra A B]
  [IsScalarTower R R₀ A] [IsScalarTower R A B]

private theorem map_span_range_lift {n : ℕ} (tk : Finset (MvPolynomial (Fin n) A))
    (g₀ : tk → MvPolynomial (Fin n) R₀)
    (hg₀ : ∀ g, MvPolynomial.map (algebraMap R₀ A) (g₀ g) = g) :
    (Ideal.span (Set.range g₀)).map (MvPolynomial.map (algebraMap R₀ A))
      = Ideal.span (↑tk : Set (MvPolynomial (Fin n) A)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, Finset.mem_coe]
  constructor
  · rintro ⟨g', rfl⟩
    rw [hg₀]
    exact g'.2
  · intro hg
    exact ⟨⟨g, hg⟩, hg₀ ⟨g, hg⟩⟩

private theorem finiteType_of_lifts [Module.FaithfullyFlat A B] [Algebra.FiniteType R R₀]
    {n : ℕ} (f : MvPolynomial (Fin n) A →ₐ[A] B) (hf : Function.Surjective f)
    (tk : Finset (MvPolynomial (Fin n) A))
    (htk : Ideal.span (↑tk : Set (MvPolynomial (Fin n) A)) = RingHom.ker f)
    (g₀ : tk → MvPolynomial (Fin n) R₀)
    (hg₀ : ∀ g, MvPolynomial.map (algebraMap R₀ A) (g₀ g) = g)
    (sB : Finset B) (hsB : Algebra.adjoin R (↑sB : Set B) = ⊤)
    (P₀ : sB → MvPolynomial (Fin n) R₀)
    (hP₀ : ∀ b, f (MvPolynomial.map (algebraMap R₀ A) (P₀ b)) = b) :
    Algebra.FiniteType R A := by
  classical
  let J₀ : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g₀)
  have hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f := by
    rw [← htk]
    exact map_span_range_lift tk g₀ hg₀
  have hfp : Algebra.FinitePresentation R₀ (MvPolynomial (Fin n) R₀ ⧸ J₀) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range g₀))
  let Φ : A ⊗[R₀] (MvPolynomial (Fin n) R₀ ⧸ J₀) ≃ₐ[A] B := modelEquiv J₀ f hf hJ
  have hΦ : ∀ p : MvPolynomial (Fin n) R₀,
      Φ ((1 : A) ⊗ₜ Ideal.Quotient.mk J₀ p) = f (MvPolynomial.map (algebraMap R₀ A) p) :=
    modelEquiv_one_tmul_mk J₀ f hf hJ
  have : Module.FaithfullyFlat A (A ⊗[R₀] (MvPolynomial (Fin n) R₀ ⧸ J₀)) :=
    Module.FaithfullyFlat.of_linearEquiv (R := A) (M := B) Φ.toLinearEquiv
  have hgen : Function.Surjective (Algebra.TensorProduct.includeRight :
      (MvPolynomial (Fin n) R₀ ⧸ J₀) →ₐ[R₀] A ⊗[R₀] (MvPolynomial (Fin n) R₀ ⧸ J₀)) := by
    let S := (Algebra.TensorProduct.includeRight :
      (MvPolynomial (Fin n) R₀ ⧸ J₀) →ₐ[R₀] A ⊗[R₀] (MvPolynomial (Fin n) R₀ ⧸ J₀)).range
    have hall : ∀ y : B, Φ.symm y ∈ S := by
      intro y
      have hy : y ∈ Algebra.adjoin R (↑sB : Set B) := by rw [hsB]; exact Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem b hb =>
        refine (AlgHom.mem_range _).mpr ⟨Ideal.Quotient.mk J₀ (P₀ ⟨b, hb⟩), ?_⟩
        apply Φ.injective
        rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.includeRight_apply, hΦ, hP₀]
      | algebraMap r =>
        have h1 : Φ.symm (algebraMap R B r) = algebraMap R₀ A (algebraMap R R₀ r) ⊗ₜ 1 := by
          rw [IsScalarTower.algebraMap_apply R A B, AlgEquiv.commutes,
            Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            ← IsScalarTower.algebraMap_apply R R₀ A]
        have h2 := S.algebraMap_mem (algebraMap R R₀ r)
        rw [Algebra.TensorProduct.algebraMap_apply] at h2
        rwa [h1]
      | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact S.mul_mem hx hy
    intro z
    obtain ⟨b, hb⟩ := (AlgHom.mem_range _).mp (hall (Φ z))
    exact ⟨b, by rw [hb, AlgEquiv.symm_apply_apply]⟩
  have htop : (⊤ : Subalgebra R₀ A).FG :=
    fg_top_of_faithfullyFlat (MvPolynomial (Fin n) R₀ ⧸ J₀) hgen
  have : Algebra.FiniteType R₀ A := ⟨htop⟩
  exact Algebra.FiniteType.trans ‹Algebra.FiniteType R R₀› ‹Algebra.FiniteType R₀ A›

end Assembly

private theorem finiteType_of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FiniteType R B] :
    Algebra.FiniteType R A := by
  classical
  obtain ⟨n, f, hf, hker⟩ := (‹Algebra.FinitePresentation A B›).out
  obtain ⟨tk, htk⟩ := hker
  obtain ⟨sB, hsB⟩ := (‹Algebra.FiniteType R B›).out
  obtain ⟨P, hP⟩ : ∃ P : B → MvPolynomial (Fin n) A, ∀ b, f (P b) = b :=
    ⟨fun b => (hf b).choose, fun b => (hf b).choose_spec⟩
  let c : Finset A := tk.biUnion coeffSet ∪ sB.biUnion fun b => coeffSet (P b)
  let R₀ : Subalgebra R A := Algebra.adjoin R (↑c : Set A)
  have : Algebra.FiniteType R R₀ := ⟨(Subalgebra.fg_top R₀).mpr (Subalgebra.fg_adjoin_finset c)⟩
  have hck : ∀ g ∈ tk, ∀ m, g.coeff m ∈ R₀ := fun g hg =>
    coeff_mem_of_coeffSet_subset R₀ g (fun a ha => Algebra.subset_adjoin (by
      simp only [c, Finset.coe_union, Finset.coe_biUnion, Finset.mem_coe, Set.mem_union,
        Set.mem_iUnion]
      exact Or.inl ⟨g, hg, ha⟩))
  have hcP : ∀ b ∈ sB, ∀ m, (P b).coeff m ∈ R₀ := fun b hb =>
    coeff_mem_of_coeffSet_subset R₀ (P b) (fun a ha => Algebra.subset_adjoin (by
      simp only [c, Finset.coe_union, Finset.coe_biUnion, Finset.mem_coe, Set.mem_union,
        Set.mem_iUnion]
      exact Or.inr ⟨b, hb, ha⟩))
  choose g₀ hg₀ using fun g : tk => exists_map_eq_of_coeff_mem R₀ (g : MvPolynomial (Fin n) A)
    (hck g g.2)
  choose P₀ hP₀ using fun b : sB => exists_map_eq_of_coeff_mem R₀ (P b) (hcP b b.2)
  exact finiteType_of_lifts (R := R) (R₀ := R₀) f hf tk htk g₀ hg₀ sB hsB P₀
    (fun b => by rw [hP₀, hP])

end FiniteTypeOfFaithfullyFlatAux

end

/-- **Finite type descends along faithfully flat, finitely presented algebras.** In a tower
`R → A → B` with `B` faithfully flat and finitely presented over `A`, if `B` is of finite type over
`R`, then so is `A`.

Source: [Stacks Project, Lemma 35.14.2 (Tag 0367)](https://stacks.math.columbia.edu/tag/0367). -/
public theorem Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FiniteType R B] :
    Algebra.FiniteType R A :=
  FiniteTypeOfFaithfullyFlatAux.finiteType_of_faithfullyFlat_of_finitePresentation R A B
