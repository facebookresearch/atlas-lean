/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_isReduced_tensorProduct_of_perfectField.lean` and
`P2M/Sol/S_Algebra_isReduced_tensorProduct_of_perfectField.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Reducedness of tensor products over perfect fields

Tensoring a reduced algebra with a field extension over a perfect field
preserves reducedness: reduce to finite-type algebras, decompose into
domains via minimal primes, and use a transcendence basis to reduce to the
separable case, where formal unramifiedness applies. The same reduction gives
that the tensor product of two reduced algebras over a perfect field is reduced
(`Algebra.isReduced_tensorProduct_of_perfectField_of_isReduced`).
-/

@[expose] public section

open scoped TensorProduct

namespace GredPerfect

section PurelyTranscendental

variable {k : Type*} [Field k] {P E L : Type*} [CommRing P] [Algebra k P] [Field E]
  [Algebra k E] [Algebra P E] [IsScalarTower k P E] [IsFractionRing P E] [Field L]
  [Algebra k L]

private theorem isDomain_tensorProduct_of_isFractionRing [IsDomain (P ⊗[k] L)] :
    IsDomain (E ⊗[k] L) := by
  let f : P ⊗[k] L →ₐ[k] E ⊗[k] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P E) (AlgHom.id k L)
  let _ : Algebra (P ⊗[k] L) (E ⊗[k] L) := f.toRingHom.toAlgebra
  have hf : ∀ x : P ⊗[k] L, algebraMap (P ⊗[k] L) (E ⊗[k] L) x = f x := fun _ => rfl
  have : IsScalarTower P (P ⊗[k] L) (E ⊗[k] L) := by
    refine IsScalarTower.of_algebraMap_eq (R := P) (S := P ⊗[k] L) (A := E ⊗[k] L)
      fun x => ?_
    rw [hf, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    simp [f]
  have H : (algebraMap (P ⊗[k] L) (E ⊗[k] L)).comp
      Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    simp [hf, f]
  have : IsLocalization (Algebra.algebraMapSubmonoid (P ⊗[k] L) (nonZeroDivisors P))
      (E ⊗[k] L) :=
    IsLocalization.tensorProduct_tensorProduct k L (nonZeroDivisors P) E H
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] L) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k L).injective
  have : IsDomain P := hinj.isDomain _
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (E ⊗[k] L)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] L) (nonZeroDivisors P)) ?_
  rintro _ ⟨x, hx, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  intro h
  apply hx0
  apply hinj
  rw [map_zero]
  simpa [Algebra.TensorProduct.algebraMap_apply] using h

end PurelyTranscendental

private theorem isDomain_adjoin_tensorProduct {k K L : Type*} [Field k] [Field K]
    [Algebra k K] [Field L] [Algebra k L] {ι : Type*} {v : ι → K}
    (hv : AlgebraicIndependent k v) :
    IsDomain ((IntermediateField.adjoin k (Set.range v)) ⊗[k] L) := by
  classical
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have : IsDomain ((Algebra.adjoin k (Set.range v)) ⊗[k] L) := by
    let e : (Algebra.adjoin k (Set.range v)) ⊗[k] L ≃ₐ[k] MvPolynomial ι L :=
      (Algebra.TensorProduct.congr hv.aevalEquiv.symm AlgEquiv.refl).trans
        ((Algebra.TensorProduct.comm k _ _).trans
          ((MvPolynomial.scalarRTensorAlgEquiv (R := k) (σ := ι) (N := L)).restrictScalars k))
    exact e.toMulEquiv.isDomain (MvPolynomial ι L)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  exact isDomain_tensorProduct_of_isFractionRing (k := k) (P := Algebra.adjoin k (Set.range v))

private theorem isReduced_tensorProduct_of_formallyUnramified_of_isDomain
    (E K D : Type*) [Field E] [Field K] [Algebra E K] [Algebra.FormallyUnramified E K]
    [Algebra.EssFiniteType E K] [CommRing D] [Algebra E D] [IsDomain D] :
    IsReduced (K ⊗[E] D) := by
  let F := FractionRing D
  have : IsReduced (F ⊗[E] K) := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[E] K)
  have : IsReduced (K ⊗[E] F) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E K F)
      (Algebra.TensorProduct.comm E K F).injective
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id E K) (IsScalarTower.toAlgHom E D F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom E D F).toLinearMap (IsFractionRing.injective D F)
  exact isReduced_of_injective _ hinj

private theorem isReduced_tensorProduct_of_isSeparable_of_isDomain
    (k E K L : Type*) [Field k] [Field E] [Field K] [Field L] [Algebra k E] [Algebra k K]
    [Algebra E K] [IsScalarTower k E K] [Algebra k L] [Algebra.IsSeparable E K]
    [Algebra.EssFiniteType E K] [IsDomain (E ⊗[k] L)] :
    IsReduced (L ⊗[k] K) := by
  have : Algebra.FormallyUnramified E K := .of_isSeparable E K
  have : IsReduced (K ⊗[E] (E ⊗[k] L)) :=
    isReduced_tensorProduct_of_formallyUnramified_of_isDomain E K (E ⊗[k] L)
  let e₁ : K ⊗[E] (E ⊗[k] L) ≃ₐ[E] K ⊗[k] L :=
    Algebra.TensorProduct.cancelBaseChange k E E K L
  let e₂ : K ⊗[k] L ≃ₐ[k] L ⊗[k] K := Algebra.TensorProduct.comm k K L
  have : IsReduced (K ⊗[k] L) := isReduced_of_injective e₁.symm e₁.symm.injective
  exact isReduced_of_injective e₂.symm e₂.symm.injective

private theorem isReduced_tensorProduct_field_of_essFiniteType
    (k K L : Type*) [Field k] [PerfectField k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] [Field L] [Algebra k L] :
    IsReduced (L ⊗[k] K) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hrange : Set.range ((↑) : s → K) = (s : Set K) := by simp
  have : IsDomain ((IntermediateField.adjoin k (s : Set K)) ⊗[k] L) := by
    have hthis := isDomain_adjoin_tensorProduct (L := L) hs.1
    rwa [hrange] at hthis
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K := .of_comp k _ K
  exact isReduced_tensorProduct_of_isSeparable_of_isDomain k
    (IntermediateField.adjoin k (s : Set K)) K L

/-- Let `B` be a reduced `k`-algebra of finite type and `C` a `k`-algebra such that `C ⊗[k] L` is
reduced for every field extension `L` of `k` that is essentially of finite type. Then
`C ⊗[k] B` is reduced: `B` embeds into the product of the fraction fields of its quotients by
its finitely many minimal primes. -/
private theorem isReduced_tensorProduct_of_finiteType_of_forall_field.{u₀}
    (k : Type*) (B : Type u₀) (C : Type*) [Field k] [CommRing B] [Algebra k B] [IsReduced B]
    [Algebra.FiniteType k B] [CommRing C] [Algebra k C]
    (hC : ∀ (L : Type u₀) [Field L] [Algebra k L] [Algebra.EssFiniteType k L],
      IsReduced (C ⊗[k] L)) :
    IsReduced (C ⊗[k] B) := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hfin : (minimalPrimes B).Finite := minimalPrimes.finite_of_isNoetherianRing B
  have : Fintype (minimalPrimes B) := hfin.fintype
  have hprime : ∀ p : minimalPrimes B, (p.1).IsPrime := fun p => p.2.1.1
  let K : minimalPrimes B → Type _ := fun p => FractionRing (B ⧸ p.1)
  let φ : B →ₐ[k] (∀ p, K p) :=
    AlgHom.pi fun p =>
      (IsScalarTower.toAlgHom k (B ⧸ p.1) (K p)).comp (Ideal.Quotient.mkₐ k p.1)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hb' : ∀ p : minimalPrimes B, b ∈ p.1 := by
      intro p
      have h2 : algebraMap (B ⧸ p.1) (K p) (Ideal.Quotient.mk p.1 b) = 0 := congr_fun hb p
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact (IsFractionRing.injective (B ⧸ p.1) (K p)) (by rw [h2, map_zero])
    have hmem : b ∈ sInf (minimalPrimes B) := by
      rw [Submodule.mem_sInf]
      exact fun p hp => hb' ⟨p, hp⟩
    have hsInf : sInf (minimalPrimes B) = (⊥ : Ideal B) := by
      change sInf ((⊥ : Ideal B).minimalPrimes) = ⊥
      rw [Ideal.sInf_minimalPrimes]
      exact nilradical_eq_zero B
    rw [hsInf] at hmem
    exact (Submodule.mem_bot B).mp hmem
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id C C) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := C) φ.toLinearMap hφ
  have : ∀ p, IsReduced (C ⊗[k] K p) := fun p =>
    have : Algebra.EssFiniteType (B ⧸ p.1) (K p) := .of_isLocalization _ (nonZeroDivisors _)
    have : Algebra.EssFiniteType k (K p) := .comp k (B ⧸ p.1) (K p)
    hC (K p)
  have : IsReduced (C ⊗[k] (∀ p, K p)) :=
    isReduced_of_injective (Algebra.TensorProduct.piRight k k C K)
      (Algebra.TensorProduct.piRight k k C K).injective
  exact isReduced_of_injective _ hinj

end GredPerfect

universe u v w

/-- Tensoring a reduced algebra with a field extension over a perfect field
preserves reducedness. -/
theorem Algebra.isReduced_tensorProduct_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A]
    [IsReduced A] (L : Type w) [Field L] [Algebra k L] :
    IsReduced (L ⊗[k] A) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  exact GredPerfect.isReduced_tensorProduct_of_finiteType_of_forall_field k B L fun K _ _ _ =>
    GredPerfect.isReduced_tensorProduct_field_of_essFiniteType k K L

/-- Over a perfect field `k`, the tensor product `A ⊗[k] B` of two reduced `k`-algebras is
reduced.

This is the Stacks project, Algebra, Lemma 10.43.5 (Tag 034N): "Let `k` be a field. Let `S` be a
geometrically reduced `k`-algebra. Let `R` be any reduced `k`-algebra. Then `R ⊗_k S` is
reduced", for a perfect field, where every reduced algebra is geometrically reduced
(`Algebra.isReduced_tensorProduct_of_perfectField`); it gives Varieties, Lemma 33.6.7 (4)
(Tag 035Z) for affine schemes. The proof follows that of Lemma 10.43.5: reduce to `B` of
finite type, which embeds into a finite product of fields. -/
theorem Algebra.isReduced_tensorProduct_of_perfectField_of_isReduced
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A]
    [IsReduced A] (B : Type w) [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B' hB' => ?_
  have : IsReduced B' := isReduced_of_injective B'.val Subtype.val_injective
  have : Algebra.FiniteType k B' := ⟨(Subalgebra.fg_top B').mpr hB'⟩
  refine GredPerfect.isReduced_tensorProduct_of_finiteType_of_forall_field k B' A
    fun L _ _ _ => ?_
  have : IsReduced (L ⊗[k] A) := Algebra.isReduced_tensorProduct_of_perfectField k A L
  exact isReduced_of_injective (Algebra.TensorProduct.comm k A L)
    (Algebra.TensorProduct.comm k A L).injective
