/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean`
and
`P2M/Sol/S_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean`
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

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import MathlibExt.RingTheory.Finiteness.FiniteTypeOfFaithfullyFlat
import MathlibExt.RingTheory.Flat.FGSubalgebraTensorProduct

/-!
# Descent of finite presentation along faithfully flat, finitely presented algebras

In a tower `R → A → B` where `B` is faithfully flat and finitely presented over `A`, if `B` is
finitely presented over `R`, then so is `A`. The proof first shows that `A` is of finite type over
`R` (`Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation`), then that the kernel of a
presentation of `A` is finitely generated, using Noetherian approximation of flatness
(`Module.Flat.exists_fg_subalgebra_flat_tensorProduct`).

## Main results

* `Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation`

## References

* [Stacks Project, Lemma 35.14.1 (Tag 02KK)](https://stacks.math.columbia.edu/tag/02KK)
-/

@[expose] public section

universe u v w

open TensorProduct PrimeSpectrum

namespace Algebra.FinitePresentation.OfFaithfullyFlat

section FF

variable {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]

private lemma exists_ideal_range_comap [Module.Flat A₀ B₀]
    [Algebra.FinitePresentation A₀ B₀] :
    ∃ 𝔞 : Ideal A₀, ∀ p : PrimeSpectrum A₀,
      p ∈ Set.range (comap (algebraMap A₀ B₀)) ↔ ¬ 𝔞 ≤ p.asIdeal := by
  have hopen : IsOpen (Set.range (comap (algebraMap A₀ B₀))) :=
    (isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range
  obtain ⟨𝔞, h𝔞⟩ := (isClosed_iff_zeroLocus_ideal _).mp hopen.isClosed_compl
  refine ⟨𝔞, fun p ↦ ?_⟩
  have : p ∈ (Set.range (comap (algebraMap A₀ B₀)))ᶜ ↔ 𝔞 ≤ p.asIdeal := by
    rw [h𝔞, mem_zeroLocus, SetLike.coe_subset_coe]
  rw [← this, Set.mem_compl_iff, not_not]

private lemma nontrivial_tensor_of_field {k K C : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing C] [Algebra k C] [Nontrivial C] : Nontrivial (K ⊗[k] C) :=
  (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := k) (M := K)
    (N := C)).mpr ‹_›

private lemma faithfullyFlat_baseChange_of_map_eq_top [Module.Flat A₀ B₀] (𝔞 : Ideal A₀)
    (h𝔞 : ∀ p : PrimeSpectrum A₀, ¬ 𝔞 ≤ p.asIdeal →
      p ∈ Set.range (comap (algebraMap A₀ B₀)))
    (A' : Type*) [CommRing A'] [Algebra A₀ A'] (htop : 𝔞.map (algebraMap A₀ A') = ⊤) :
    Module.FaithfullyFlat A' (A' ⊗[A₀] B₀) := by
  refine Module.FaithfullyFlat.of_comap_surjective fun q ↦ ?_
  set p : PrimeSpectrum A₀ := comap (algebraMap A₀ A') q with hpdef
  have hp : p ∈ Set.range (comap (algebraMap A₀ B₀)) := by
    refine h𝔞 p fun hle ↦ q.2.ne_top ?_
    exact top_le_iff.mp (htop ▸ Ideal.map_le_iff_le_comap.mpr hle)
  rw [← nontrivial_iff_mem_rangeComap] at hp
  rw [← Set.mem_range, ← nontrivial_iff_mem_rangeComap]
  let k := p.asIdeal.ResidueField
  let K := q.asIdeal.ResidueField
  let φ : k →ₐ[A₀] K :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId A₀ A') (by simp [hpdef])
  let : Algebra k K := φ.toRingHom.toAlgebra
  have : IsScalarTower A₀ k K := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  let e₁ : K ⊗[A'] (A' ⊗[A₀] B₀) ≃ₗ[K] K ⊗[A₀] B₀ :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ A' K K B₀
  let e₂ : K ⊗[k] (k ⊗[A₀] B₀) ≃ₗ[K] K ⊗[A₀] B₀ :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ k K K B₀
  have : Nontrivial (K ⊗[k] (k ⊗[A₀] B₀)) := nontrivial_tensor_of_field
  exact (e₂.toEquiv.trans e₁.symm.toEquiv).symm.nontrivial

end FF

section EndGame

variable {A' A B' : Type*} [CommRing A'] [CommRing A] [CommRing B'] [Algebra A' A]
  [Algebra A' B']

private lemma includeRight_surjective_of_surjective (h : Function.Surjective (algebraMap A' A)) :
    Function.Surjective (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B') := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨a, rfl⟩ := h a
    exact ⟨a • b, by rw [Algebra.TensorProduct.includeRight_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one]⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy; exact ⟨x + y, map_add _ _ _⟩

private lemma ker_includeRight_le_map (h : Function.Surjective (algebraMap A' A)) :
    RingHom.ker (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom ≤
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' B') := by
  intro b hb
  rw [RingHom.mem_ker] at hb
  change (1 : A) ⊗ₜ[A'] b = 0 at hb
  let g : A' →ₗ[A'] A := Algebra.linearMap A' A
  have hex := rTensor_exact B' (LinearMap.exact_subtype_ker_map g) h
  have h1 : (LinearMap.rTensor B' g) ((1 : A') ⊗ₜ b) = 0 := by
    rw [LinearMap.rTensor_tmul]; simpa [g] using hb
  obtain ⟨y, hy⟩ := (hex ((1 : A') ⊗ₜ b)).mp h1
  have hlid : b = TensorProduct.lid A' B'
      ((LinearMap.rTensor B' (LinearMap.ker g).subtype) y) := by
    rw [hy, TensorProduct.lid_tmul, one_smul]
  rw [hlid]
  clear hlid hy h1 hb
  induction y using TensorProduct.inductionOn with
  | tmul q b' =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Submodule.subtype_apply,
      Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    exact LinearMap.mem_ker.mp q.2
  | add x y hx hy => rw [map_add, map_add]; exact Ideal.add_mem _ hx hy

private lemma exists_fg_le_of_le_map {S : Type*} [CommRing S] (φ : A' →+* S) (I : Ideal A')
    (N : Ideal S) (hN : N.FG) (h : N ≤ I.map φ) :
    ∃ I₀ : Ideal A', I₀ ≤ I ∧ I₀.FG ∧ N ≤ I₀.map φ := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have key : ∀ x ∈ s, ∃ U : Finset A', (↑U : Set A') ⊆ I ∧
      x ∈ (Ideal.span (↑U : Set A')).map φ := by
    intro x hx
    have hx' : x ∈ Submodule.span S (φ '' (I : Set A')) := h (Ideal.subset_span hx)
    obtain ⟨T, hT, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx'
    obtain ⟨U, hU, rfl⟩ := Finset.subset_set_image_iff.mp hT
    refine ⟨U, hU, ?_⟩
    rw [Ideal.map_span, ← Finset.coe_image]
    exact hxT
  choose U hUI hxU using key
  refine ⟨Ideal.span (↑(s.attach.biUnion fun x ↦ U x.1 x.2) : Set A'), ?_, ⟨_, rfl⟩, ?_⟩
  · refine Ideal.span_le.mpr fun a ha ↦ ?_
    simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Set.iUnion_true,
      Set.mem_iUnion] at ha
    obtain ⟨x, hx⟩ := ha
    exact hUI x.1 x.2 hx
  · refine Ideal.span_le.mpr fun x hx ↦ ?_
    refine Ideal.map_mono ?_ (hxU x hx)
    refine Ideal.span_mono fun a ha ↦ ?_
    simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Set.iUnion_true,
      Set.mem_iUnion]
    exact ⟨⟨x, hx⟩, ha⟩

variable (A B') in
private noncomputable def θ (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) :
    (A' ⧸ J) ⊗[A'] B' →ₐ[A'] A ⊗[A'] B' :=
  Algebra.TensorProduct.map (Ideal.Quotient.liftₐ J (Algebra.ofId A' A) fun _ ha ↦ hJ ha)
    (AlgHom.id A' B')

private lemma θ_tmul (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) (a : A')
    (b : B') : θ A B' J hJ (Ideal.Quotient.mk J a ⊗ₜ b) = algebraMap A' A a ⊗ₜ b := by
  simp only [θ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

private lemma θ_includeRight (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) (b : B') :
    θ A B' J hJ (Algebra.TensorProduct.includeRight b) = (1 : A) ⊗ₜ b := by
  rw [Algebra.TensorProduct.includeRight_apply, ← map_one (Ideal.Quotient.mk J), θ_tmul,
    map_one]

private lemma θ_injective (J : Ideal A')
    (hJ : J ≤ RingHom.ker (algebraMap A' A))
    (hker : RingHom.ker (Algebra.TensorProduct.includeRight :
      B' →ₐ[A'] A ⊗[A'] B').toRingHom ≤ J.map (algebraMap A' B')) :
    Function.Injective (θ A B' J hJ) := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨b, rfl⟩ := includeRight_surjective_of_surjective (A := A' ⧸ J) (B' := B')
    Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  change θ A B' J hJ (Algebra.TensorProduct.includeRight b) = 0 at hx
  rw [θ_includeRight] at hx
  have hb : b ∈ J.map (algebraMap A' B') := hker (by rw [RingHom.mem_ker]; exact hx)
  have : J.map (algebraMap A' B') ≤ RingHom.ker
      (Algebra.TensorProduct.includeRight : B' →ₐ[A'] (A' ⧸ J) ⊗[A'] B').toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : A' ⧸ J) ⊗ₜ[A'] (algebraMap A' B' a) = 0
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      TensorProduct.zero_tmul]
  simpa [RingHom.mem_ker] using this hb

private lemma θ_smul_eq_zero (J : Ideal A') (hJ : J ≤ RingHom.ker (algebraMap A' A)) (a : A')
    (ha : algebraMap A' A a = 0) (x : (A' ⧸ J) ⊗[A'] B') :
    θ A B' J hJ (Ideal.Quotient.mk J a • x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul, θ_tmul, map_mul, ha, zero_mul,
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]

private theorem ker_fg_of_faithfullyFlat_baseChange (h : Function.Surjective (algebraMap A' A))
    [Module.Flat A' B'] [Algebra.FinitePresentation A' B']
    [Module.FaithfullyFlat A (A ⊗[A'] B')] [Algebra.FinitePresentation A' (A ⊗[A'] B')] :
    (RingHom.ker (algebraMap A' A)).FG := by
  classical
  set Q := RingHom.ker (algebraMap A' A) with hQdef
  have hkfg : (RingHom.ker
      (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective _ (includeRight_surjective_of_surjective h)
  obtain ⟨J₁, hJ₁Q, hJ₁fg, hkerJ₁⟩ :=
    exists_fg_le_of_le_map (algebraMap A' B') Q _ hkfg (ker_includeRight_le_map h)
  obtain ⟨𝔞, h𝔞⟩ := exists_ideal_range_comap (A₀ := A') (B₀ := B')
  have hland : ∀ 𝔭 : PrimeSpectrum A,
      comap (algebraMap A' A) 𝔭 ∈ Set.range (comap (algebraMap A' B')) := by
    intro 𝔭
    obtain ⟨𝔔, h𝔔⟩ := comap_surjective_of_faithfullyFlat (A := A) (B := A ⊗[A'] B') 𝔭
    refine ⟨comap
      (Algebra.TensorProduct.includeRight : B' →ₐ[A'] A ⊗[A'] B').toRingHom 𝔔, ?_⟩
    apply PrimeSpectrum.ext
    rw [← h𝔔]
    simp only [comap_asIdeal, Ideal.comap_comap]
    congr 1
    ext b
    simp [Algebra.algebraMap_eq_smul_one]
  have h𝔞A : 𝔞.map (algebraMap A' A) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmem := hland ⟨𝔪, h𝔪.isPrime⟩
    rw [h𝔞] at hmem
    exact hmem (Ideal.map_le_iff_le_comap.mp hle)
  obtain ⟨a₀, ha₀𝔞, ha₀⟩ : ∃ a₀ ∈ 𝔞, algebraMap A' A a₀ = 1 :=
    (Ideal.mem_map_iff_of_surjective _ h).mp (h𝔞A ▸ Submodule.mem_top)
  set y := a₀ - 1 with hydef
  have hyQ : y ∈ Q := by rw [hQdef, RingHom.mem_ker, hydef, map_sub, ha₀, map_one, sub_self]
  set J : Ideal A' := J₁ ⊔ Ideal.span {y} with hJdef
  have hJQ : J ≤ Q := sup_le hJ₁Q ((Ideal.span_singleton_le_iff_mem _).mpr hyQ)
  have hJfg : J.FG := Submodule.FG.sup hJ₁fg ⟨{y}, by simp⟩
  have : Module.FaithfullyFlat (A' ⧸ J) ((A' ⧸ J) ⊗[A'] B') := by
    refine faithfullyFlat_baseChange_of_map_eq_top 𝔞 (fun p hp ↦ (h𝔞 p).mpr hp) (A' ⧸ J) ?_
    rw [Ideal.eq_top_iff_one]
    have : Ideal.Quotient.mk J a₀ = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_right (b := Ideal.span {y}) (Ideal.mem_span_singleton_self _)
    rw [← this]
    exact Ideal.mem_map_of_mem _ ha₀𝔞
  have hθ : Function.Injective (θ A B' J hJQ) :=
    θ_injective J hJQ (hkerJ₁.trans (Ideal.map_mono le_sup_left))
  let πJ : (A' ⧸ J) →ₐ[A'] A := Ideal.Quotient.liftₐ J (Algebra.ofId A' A) fun _ ha ↦ hJQ ha
  let QJ : Ideal (A' ⧸ J) := RingHom.ker πJ.toRingHom
  have hQJ : Subsingleton (QJ ⊗[A' ⧸ J] ((A' ⧸ J) ⊗[A'] B')) := by
    refine ⟨fun z₁ z₂ ↦ ?_⟩
    have hinj : Function.Injective
        (LinearMap.rTensor ((A' ⧸ J) ⊗[A'] B') (Submodule.subtype QJ)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    have hzero : ∀ z : QJ ⊗[A' ⧸ J] ((A' ⧸ J) ⊗[A'] B'),
        (TensorProduct.lid _ _ (LinearMap.rTensor _ (Submodule.subtype QJ) z)) = 0 := by
      intro z
      apply hθ
      rw [map_zero (θ A B' J hJQ)]
      induction z using TensorProduct.inductionOn with
      | tmul q x =>
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (q : A' ⧸ J)
        have ha0 : algebraMap A' A a = 0 := by
          have := q.2
          rw [RingHom.mem_ker] at this
          rw [← ha] at this
          exact this
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul, ← ha]
        exact θ_smul_eq_zero J hJQ a ha0 x
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
    apply hinj
    apply (TensorProduct.lid _ _).injective
    rw [hzero, hzero]
  have hQJ0 : Subsingleton QJ :=
    Module.FaithfullyFlat.rTensor_reflects_triviality (A' ⧸ J) ((A' ⧸ J) ⊗[A'] B') QJ
  have hQJ : Q ≤ J := by
    intro q hq
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hmem : Ideal.Quotient.mk J q ∈ QJ := by
      rw [RingHom.mem_ker]
      rw [hQdef, RingHom.mem_ker] at hq
      exact hq
    have := hQJ0.elim ⟨_, hmem⟩ ⟨0, QJ.zero_mem⟩
    exact congrArg Subtype.val this
  rw [le_antisymm hQJ hJQ] at *
  exact hJfg

end EndGame

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
private noncomputable def coeffSet (g : MvPolynomial σ A) : Finset A :=
  g.support.image fun m => g.coeff m

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
      (Algebra.TensorProduct.includeRight (R := R₀) (A := A)
        (B := MvPolynomial (Fin n) R₀) :
        MvPolynomial (Fin n) R₀ →+* A ⊗[R₀] MvPolynomial (Fin n) R₀)
      = MvPolynomial.map (algebraMap R₀ A) := by
  apply RingHom.ext
  intro p
  simp [Algebra.TensorProduct.includeRight_apply]

private theorem ker_eq_map_map
    (hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f) :
    RingHom.ker f = (J₀.map (Algebra.TensorProduct.includeRight (R := R₀) (A := A))).map
      ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A : _ ≃ₐ[A] _) :
        A ⊗[R₀] MvPolynomial (Fin n) R₀ →+* MvPolynomial (Fin n) A) := by
  rw [← hJ, ← algebraTensorAlgEquiv_comp_includeRight (R₀ := R₀) (A := A) (n := n),
    ← Ideal.map_map]
  rfl

private noncomputable def modelEquiv (hf : Function.Surjective f)
    (hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker f) :
    A ⊗[R₀] (MvPolynomial (Fin n) R₀ ⧸ J₀) ≃ₐ[A] B :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R₀) A (MvPolynomial (Fin n) R₀) A J₀).trans
    ((Ideal.quotientEquivAlg (J₀.map (Algebra.TensorProduct.includeRight (R := R₀) (A := A)))
        (RingHom.ker f) (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ A)
        (ker_eq_map_map J₀ f hJ)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf))

end Model

section MapSpan

variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]

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

end MapSpan

section Assembly

private lemma fg_comap_of_surjective {P A' : Type*} [CommRing P] [CommRing A'] (f : P →+* A')
    (hf : Function.Surjective f) (hk : (RingHom.ker f).FG) (Q : Ideal A') (hQ : Q.FG) :
    (Q.comap f).FG := by
  classical
  obtain ⟨T, rfl⟩ := hQ
  have hT : (↑T : Set A') ⊆ f '' Set.univ := by
    rw [Set.image_univ, hf.range_eq]; exact Set.subset_univ _
  obtain ⟨T', -, rfl⟩ := Finset.subset_set_image_iff.mp hT
  have : Ideal.comap f (Ideal.span (↑(T'.image f) : Set A')) =
      Ideal.span (↑T' : Set P) ⊔ RingHom.ker f := by
    rw [Finset.coe_image, ← Ideal.map_span, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot]
  rw [this]
  exact Submodule.FG.sup ⟨T', rfl⟩ hk

private theorem ker_fg_of_descent (P : Type*) (A : Type*) (B : Type*) [CommRing P]
    [CommRing A] [CommRing B] [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation P B]
    (A₁ : Type*) [CommRing A₁] [Algebra A₁ A] (B₁ : Type*) [CommRing B₁] [Algebra A₁ B₁]
    [Module.Flat A₁ B₁] [Algebra.FinitePresentation A₁ B₁]
    (e : A ⊗[A₁] B₁ ≃ₐ[A] B)
    (R₁ : Type*) [CommRing R₁] [Algebra R₁ P] [Algebra R₁ A₁] [IsNoetherianRing R₁]
    (hρ : Function.Surjective (algebraMap R₁ A₁))
    (hcompat : ∀ r : R₁,
      algebraMap A₁ A (algebraMap R₁ A₁ r) = algebraMap P A (algebraMap R₁ P r)) :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  have hK₁ : (RingHom.ker (algebraMap R₁ A₁)).FG := IsNoetherian.noetherian _
  let I₁ : Ideal P := (RingHom.ker (algebraMap R₁ A₁)).map (algebraMap R₁ P)
  have hI₁fg : I₁.FG := hK₁.map _
  have hI₁ : I₁ ≤ RingHom.ker (algebraMap P A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [RingHom.mem_ker] at hr
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcompat, hr, map_zero]
  let A' := P ⧸ I₁
  have hkerσ : RingHom.ker (algebraMap R₁ A₁) ≤
      RingHom.ker ((Ideal.Quotient.mk I₁).comp (algebraMap R₁ P)) := by
    intro r hr
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  let σ : A₁ →+* A' := ((algebraMap R₁ A₁).liftOfSurjective hρ) ⟨_, hkerσ⟩
  have hσ : ∀ r : R₁, σ (algebraMap R₁ A₁ r) = Ideal.Quotient.mk I₁ (algebraMap R₁ P r) :=
    fun r ↦ RingHom.liftOfSurjective_comp_apply (algebraMap R₁ A₁) hρ ⟨_, hkerσ⟩ r
  let algA₁A' : Algebra A₁ A' := σ.toAlgebra
  let τ : A' →ₐ[P] A := Ideal.Quotient.liftₐ I₁ (Algebra.ofId P A) fun _ ha ↦ hI₁ ha
  let algA'A : Algebra A' A := τ.toRingHom.toAlgebra
  have : IsScalarTower P A' A := IsScalarTower.of_algebraMap_eq fun p ↦ (τ.commutes p).symm
  have hτ : Function.Surjective (algebraMap A' A) := fun a ↦ by
    obtain ⟨p, rfl⟩ := hπ a
    exact ⟨Ideal.Quotient.mk I₁ p, τ.commutes p⟩
  have : IsScalarTower A₁ A' A := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨r, rfl⟩ := hρ x
    change algebraMap A₁ A (algebraMap R₁ A₁ r) = τ (σ (algebraMap R₁ A₁ r))
    rw [hσ, hcompat]
    exact (τ.commutes (algebraMap R₁ P r)).symm
  let algA'B : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower P A' B := IsScalarTower.of_algebraMap_eq fun p ↦ by
    change algebraMap P B p = algebraMap A B (algebraMap A' A (algebraMap P A' p))
    rw [← IsScalarTower.algebraMap_apply P A' A, ← IsScalarTower.algebraMap_apply P A B]
  have : Algebra.FiniteType P A' := inferInstance
  have : Algebra.FinitePresentation A' B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation P A' B
  let Ξ : A ⊗[A'] (A' ⊗[A₁] B₁) ≃ₐ[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₁ A' A A B₁).trans e
  have : Module.FaithfullyFlat A (A ⊗[A'] (A' ⊗[A₁] B₁)) :=
    Module.FaithfullyFlat.of_linearEquiv (R := A) (M := B) Ξ.toLinearEquiv
  let Ξ' : B ≃ₐ[A'] A ⊗[A'] (A' ⊗[A₁] B₁) := (Ξ.restrictScalars A').symm
  have : Algebra.FinitePresentation A' (A ⊗[A'] (A' ⊗[A₁] B₁)) :=
    Algebra.FinitePresentation.equiv (R := A') (A := B) (B := A ⊗[A'] (A' ⊗[A₁] B₁)) Ξ'
  have hQ : (RingHom.ker (algebraMap A' A)).FG :=
    ker_fg_of_faithfullyFlat_baseChange (A' := A') (A := A) (B' := A' ⊗[A₁] B₁) hτ
  have hker : RingHom.ker (algebraMap P A) =
      (RingHom.ker (algebraMap A' A)).comap (Ideal.Quotient.mk I₁) := by
    rw [RingHom.comap_ker, IsScalarTower.algebraMap_eq P A' A]; rfl
  rw [hker]
  exact fg_comap_of_surjective _ Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]) _ hQ

private theorem ker_fg_of_model (P : Type*) (A : Type*) (B : Type*) [CommRing P] [CommRing A]
    [CommRing B] [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation P B]
    (R₀ : Type*) [CommRing R₀] [Algebra R₀ P] [Algebra R₀ A] [IsScalarTower R₀ P A]
    [IsNoetherianRing R₀] (Bq : Type*) [CommRing Bq] [Algebra R₀ Bq]
    [Algebra.FinitePresentation R₀ Bq]
    (Φ : A ⊗[R₀] Bq ≃ₐ[A] B) :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  have : Module.Flat A (A ⊗[R₀] Bq) := Module.Flat.of_linearEquiv Φ.toLinearEquiv
  obtain ⟨A₁, hA₁fg, -, hA₁flat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_tensorProduct (R₀ := R₀) (R := A) (B₀ := Bq) ∅
  obtain ⟨s₁, hs₁⟩ := hA₁fg
  have hπ2 : ∀ a : A, ∃ p : P, algebraMap P A p = a := hπ
  choose ℓ hℓ using hπ2
  let R₁ : Subalgebra R₀ P := Algebra.adjoin R₀ (↑(s₁.image ℓ) : Set P)
  let πR₀ : P →ₐ[R₀] A := IsScalarTower.toAlgHom R₀ P A
  have hrange : (πR₀.comp R₁.val).range = A₁ := by
    rw [AlgHom.range_comp, Subalgebra.range_val, AlgHom.map_adjoin, ← hs₁, Finset.coe_image,
      ← Set.image_comp]
    congr 1
    ext a
    simp [πR₀, hℓ]
  let ρ : R₁ →ₐ[R₀] A₁ := (πR₀.comp R₁.val).codRestrict A₁ fun r ↦ hrange.le ⟨r, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨r, hr⟩ := hrange.ge ha
    exact ⟨r, Subtype.ext hr⟩
  let algR₁A₁ : Algebra R₁ A₁ := ρ.toRingHom.toAlgebra
  have : Algebra.FiniteType R₀ R₁ :=
    ⟨(Subalgebra.fg_top R₁).mpr (Subalgebra.fg_adjoin_finset _)⟩
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  exact ker_fg_of_descent P A B hπ A₁ (A₁ ⊗[R₀] Bq)
    ((Algebra.TensorProduct.cancelBaseChange R₀ A₁ A A Bq).trans Φ) R₁ hρ fun _ ↦ rfl

private theorem ker_fg_of_lifts (P : Type*) (A : Type*) (B : Type*) [CommRing P] [CommRing A]
    [CommRing B] [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A))
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation P B]
    (R₀ : Type*) [CommRing R₀] [Algebra R₀ P] [Algebra R₀ A] [IsScalarTower R₀ P A]
    [IsNoetherianRing R₀]
    {k : ℕ} (ψ : MvPolynomial (Fin k) A →ₐ[A] B) (hψ : Function.Surjective ψ)
    (tk : Finset (MvPolynomial (Fin k) A))
    (htk : Ideal.span (↑tk : Set (MvPolynomial (Fin k) A)) = RingHom.ker ψ)
    (g₀ : tk → MvPolynomial (Fin k) R₀)
    (hg₀ : ∀ g, MvPolynomial.map (algebraMap R₀ A) (g₀ g) = g) :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  let J₀ : Ideal (MvPolynomial (Fin k) R₀) := Ideal.span (Set.range g₀)
  have hJ : J₀.map (MvPolynomial.map (algebraMap R₀ A)) = RingHom.ker ψ := by
    rw [← htk]; exact map_span_range_lift tk g₀ hg₀
  have : Algebra.FinitePresentation R₀ (MvPolynomial (Fin k) R₀ ⧸ J₀) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range g₀))
  exact ker_fg_of_model P A B hπ R₀ (MvPolynomial (Fin k) R₀ ⧸ J₀) (modelEquiv J₀ ψ hψ hJ)

private theorem ker_fg_of_surjective (P : Type*) (A : Type*) (B : Type*) [CommRing P]
    [CommRing A] [CommRing B] [Algebra P A] [Algebra A B] [Algebra P B] [IsScalarTower P A B]
    (hπ : Function.Surjective (algebraMap P A)) [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation A B] [Algebra.FinitePresentation P B] :
    (RingHom.ker (algebraMap P A)).FG := by
  classical
  obtain ⟨k, ψ, hψ, hkerψ⟩ := (‹Algebra.FinitePresentation A B›).out
  obtain ⟨tk, htk⟩ := hkerψ
  have htk' : Ideal.span (↑tk : Set (MvPolynomial (Fin k) A)) = RingHom.ker ψ := htk
  choose gl hgl using fun g : tk ↦
    MvPolynomial.map_surjective (algebraMap P A) hπ (g : MvPolynomial (Fin k) A)
  let c : Finset P := Finset.univ.biUnion fun g : tk ↦ coeffSet (gl g)
  let R₀ : Subalgebra ℤ P := Algebra.adjoin ℤ (↑c : Set P)
  have : Algebra.FiniteType ℤ R₀ :=
    ⟨(Subalgebra.fg_top R₀).mpr (Subalgebra.fg_adjoin_finset c)⟩
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hcoef : ∀ g : tk, ∀ m, (gl g).coeff m ∈ R₀ := fun g ↦
    coeff_mem_of_coeffSet_subset R₀ (gl g) fun _ ha ↦ Algebra.subset_adjoin (by
      simp only [c, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Set.mem_iUnion, Finset.mem_coe]
      exact ⟨g, ha⟩)
  choose g₀ hg₀ using fun g : tk ↦ exists_map_eq_of_coeff_mem R₀ (gl g) (hcoef g)
  have hg₀A : ∀ g : tk, MvPolynomial.map (algebraMap R₀ A) (g₀ g) = g := fun g ↦ by
    rw [IsScalarTower.algebraMap_eq R₀ P A, ← MvPolynomial.map_map, hg₀, hgl]
  exact ker_fg_of_lifts P A B hπ R₀ ψ hψ tk htk' g₀ hg₀A

end Assembly

end Algebra.FinitePresentation.OfFaithfullyFlat

/-- **Finite presentation descends along faithfully flat, finitely presented algebras.** In a
tower `R → A → B` with `B` faithfully flat and finitely presented over `A`, if `B` is finitely
presented over `R`, then so is `A`.

Source: [Stacks Project, Lemma 35.14.1 (Tag 02KK)](https://stacks.math.columbia.edu/tag/02KK). -/
public theorem Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation
    (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by
  classical
  have hft : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation R A B
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let algPA : Algebra (MvPolynomial (Fin n) R) A := π.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (π.commutes r).symm
  let algPB : Algebra (MvPolynomial (Fin n) R) B :=
    ((algebraMap A B).comp π.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) R) A B :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R B r = algebraMap A B (π (algebraMap R (MvPolynomial (Fin n) R) r))
    rw [π.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R
      (MvPolynomial (Fin n) R) B
  have hπ' : Function.Surjective (Algebra.ofId (MvPolynomial (Fin n) R) A) := hπ
  have hI : (RingHom.ker (Algebra.ofId (MvPolynomial (Fin n) R) A)).FG :=
    OfFaithfullyFlat.ker_fg_of_surjective (MvPolynomial (Fin n) R) A B hπ
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R ⧸ RingHom.ker (Algebra.ofId (MvPolynomial (Fin n) R) A)) :=
    Algebra.FinitePresentation.quotient hI
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R) A :=
    Algebra.FinitePresentation.equiv (Ideal.quotientKerAlgEquivOfSurjective hπ')
  exact Algebra.FinitePresentation.trans (R := R) (A := MvPolynomial (Fin n) R) (B := A)
