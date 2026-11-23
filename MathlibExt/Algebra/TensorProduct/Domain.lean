/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean`
and
`P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products of domains over an algebraically closed field

Over an algebraically closed field, the tensor product of two domains is a
domain, provided one factor is of finite type (or a field). The proof
evaluates at closed points: a product `x * y = 0` forces one factor to
vanish at every closed point, hence one factor is zero.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace TensorProductDomainAux

/-- The quotient of a finite-type algebra over an algebraically closed field
by a maximal ideal maps bijectively onto the field. -/
private theorem algebraMap_quotient_bijective (K : Type u) [Field K] [IsAlgClosed K]
    {A : Type v} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Bijective (algebraMap K (A ⧸ m)) := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The `K`-point of a finite-type algebra over an algebraically closed field
corresponding to a maximal ideal. -/
private noncomputable def pointOfMaximal (K : Type u) [Field K] [IsAlgClosed K] {A : Type v}
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    A →ₐ[K] K :=
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m)) (algebraMap_quotient_bijective K m)
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      exact e.symm_apply_apply k }

private theorem pointOfMaximal_eq_zero_iff (K : Type u) [Field K] [IsAlgClosed K] {A : Type v}
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] (a : A) :
    pointOfMaximal K m a = 0 ↔ a ∈ m := by
  change (RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective K m)).symm (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

end TensorProductDomainAux

namespace Algebra.TensorProduct

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, the tensor product of a finite-type
domain with a domain is a domain. -/
theorem isDomain_of_isAlgClosed_of_finiteType (A : Type v) (B : Type w)
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsDomain A]
    [CommRing B] [Algebra K B] [IsDomain B] :
    IsDomain (A ⊗[K] B) := by
  classical
  haveI : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective
  let bB := Module.Free.chooseBasis K B
  let 𝔅 := Algebra.TensorProduct.basis A bB
  let I : A ⊗[K] B → Ideal A := fun x => Ideal.span (Set.range (𝔅.repr x))
  have hI : ∀ x, I x = ⊥ → x = 0 := by
    intro x hx
    apply 𝔅.repr.injective
    rw [map_zero]
    ext i
    exact (Ideal.span_eq_bot.mp hx) _ ⟨i, rfl⟩
  have hpt : ∀ (x y : A ⊗[K] B), x * y = 0 →
      ∀ (m : Ideal A) [m.IsMaximal], I x ≤ m ∨ I y ≤ m := by
    intro x y hxy m _
    let φ : A →ₐ[K] K := TensorProductDomainAux.pointOfMaximal K m
    let ψ : A ⊗[K] B →ₐ[K] B :=
      Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B)
        (fun _ _ => Commute.all _ _)
    have hψ : ∀ (z : A ⊗[K] B) (i), bB.repr (ψ z) i = φ (𝔅.repr z i) := by
      intro z i
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [ψ, 𝔅, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
          Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.TensorProduct.basis_repr_tmul,
          Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul,
          Algebra.algebraMap_self, RingHom.id_apply]
      | add z w hz hw => simp [map_add, hz, hw]
    have hker : ∀ z : A ⊗[K] B, ψ z = 0 → I z ≤ m := by
      intro z hz
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, ← TensorProductDomainAux.pointOfMaximal_eq_zero_iff K,
        ← hψ, hz, map_zero, Finsupp.zero_apply]
    have h0 : ψ x * ψ y = 0 := by rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (hker x h)
    · exact Or.inr (hker y h)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K) (B := A)
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  have hle : I x * I y ≤ (⊥ : Ideal A) := by
    rw [← Ideal.radical_bot_of_isReduced, Ideal.radical_eq_jacobson]
    refine le_sInf ?_
    rintro J ⟨-, hJ⟩
    rcases hpt x y hxy J with h | h
    · exact Ideal.mul_le_left.trans h
    · exact Ideal.mul_le_right.trans h
  rcases (Ideal.mul_eq_bot.mp (le_bot_iff.mp hle)) with h | h
  · exact Or.inl (hI x h)
  · exact Or.inr (hI y h)

/-- Over an algebraically closed field, the tensor product of a field with a
domain is a domain. -/
theorem isDomain_of_isAlgClosed_of_field (F : Type v) (B : Type w) [Field F] [Algebra K F]
    [CommRing B] [Algebra K B] [IsDomain B] : IsDomain (F ⊗[K] B) := by
  classical
  haveI : Nontrivial (F ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K F B
      (algebraMap K F).injective (algebraMap K B).injective
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨sx, hx⟩ := TensorProduct.exists_finset x
  obtain ⟨sy, hy⟩ := TensorProduct.exists_finset y
  let A : Subalgebra K F := Algebra.adjoin K ↑(sx.image Prod.fst ∪ sy.image Prod.fst)
  haveI : Algebra.FiniteType K A :=
    A.fg_iff_finiteType.mp ⟨sx.image Prod.fst ∪ sy.image Prod.fst, rfl⟩
  let ι : A ⊗[K] B →ₐ[K] F ⊗[K] B := Algebra.TensorProduct.map A.val (AlgHom.id K B)
  have hι : Function.Injective ι := by
    have h : Function.Injective (A.val.toLinearMap.rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := B) A.val.toLinearMap
        Subtype.val_injective
    intro a b hab
    exact h hab
  have hlift : ∀ s : Finset (F × B), (∀ p ∈ s, p.1 ∈ A) →
      ∃ z : A ⊗[K] B, ι z = ∑ p ∈ s, p.1 ⊗ₜ[K] p.2 := by
    intro s hs
    refine ⟨∑ p ∈ s.attach, (⟨p.1.1, hs p.1 p.2⟩ : A) ⊗ₜ[K] p.1.2, ?_⟩
    rw [map_sum, ← Finset.sum_attach s]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [ι]
  have hxA : ∀ p ∈ sx, p.1 ∈ A := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)))
  have hyA : ∀ p ∈ sy, p.1 ∈ A := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.fst hp)))
  obtain ⟨x', hx'⟩ := hlift sx hxA
  obtain ⟨y', hy'⟩ := hlift sy hyA
  rw [← hx] at hx'
  rw [← hy] at hy'
  subst hx' hy'
  haveI : IsDomain (A ⊗[K] B) := isDomain_of_isAlgClosed_of_finiteType A B
  have hxy' : x' * y' = 0 := hι (by rw [map_mul, hxy, map_zero])
  rcases mul_eq_zero.mp hxy' with h | h
  · exact Or.inl (by rw [h, map_zero])
  · exact Or.inr (by rw [h, map_zero])

end Algebra.TensorProduct
