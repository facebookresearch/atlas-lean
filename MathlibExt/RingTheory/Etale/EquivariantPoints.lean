/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_Etale_existsUnique_algHom_forall_comp_eq_of_equivariant.lean`
and
`P2M/Sol/S_Algebra_Etale_existsUnique_algHom_forall_comp_eq_of_equivariant.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u v w

namespace EtaleEquivariantPoints


section Factorisation

variable {K : Type*} [Field K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {J : Type*} {A : J → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]

private theorem single_mul_single_one [DecidableEq J] {j j' : J} (h : j ≠ j') (a : A j) :
    (Pi.single j a : Π j, A j) * Pi.single j' 1 = 0 := by
  funext k
  simp only [Pi.mul_apply, Pi.zero_apply]
  rcases eq_or_ne k j' with rfl | hk
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]
  · rw [Pi.single_eq_of_ne hk, mul_zero]

private def factorComponent [DecidableEq J] (φ : (Π j, A j) →ₐ[K] Ω) (j : J)
    (h1 : φ (Pi.single j 1) = 1) : A j →ₐ[K] Ω where
  toFun x := φ (Pi.single j x)
  map_one' := h1
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' x y := by rw [Pi.single_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1]
    exact (Algebra.algebraMap_eq_smul_one r).symm

@[scoped simp] private theorem factorComponent_apply [DecidableEq J] (φ : (Π j, A j) →ₐ[K] Ω) (j : J)
    (h1 : φ (Pi.single j 1) = 1) (x : A j) :
    factorComponent φ j h1 x = φ (Pi.single j x) := rfl

private theorem exists_factor_algHom [Finite J] [IsDomain Ω] (φ : (Π j, A j) →ₐ[K] Ω) :
    ∃ (j : J) (φ₀ : A j →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) := by
  cases nonempty_fintype J
  classical

  have hidem : ∀ j, φ (Pi.single j 1) = 0 ∨ φ (Pi.single j 1) = 1 := by
    intro j
    have h2 : φ (Pi.single j 1) * φ (Pi.single j 1) = φ (Pi.single j 1) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    have h3 : φ (Pi.single j 1) * (φ (Pi.single j 1) - 1) = 0 := by
      rw [mul_sub, h2, mul_one, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

  have hsum : (∑ j, φ (Pi.single j 1)) = 1 := by
    rw [← map_sum]
    have h1 : (∑ j, (Pi.single j 1 : Π j, A j)) = 1 := by
      simpa using Finset.univ_sum_single (1 : Π j, A j)
    rw [h1, map_one]
  have hex : ∃ j, φ (Pi.single j 1) = 1 := by
    by_contra hno
    have hall : ∀ j ∈ Finset.univ, φ (Pi.single (M := A) j 1) = 0 :=
      fun j _ => (hidem j).resolve_right fun h1 => hno ⟨j, h1⟩
    rw [Finset.sum_eq_zero hall] at hsum
    exact zero_ne_one hsum
  obtain ⟨j₀, h1⟩ := hex
  refine ⟨j₀, factorComponent φ j₀ h1, AlgHom.ext fun g => ?_⟩
  have hg : φ g = ∑ j, φ (Pi.single j (g j)) := by
    rw [← map_sum, Finset.univ_sum_single]
  have hzero : ∀ j ∈ Finset.univ, j ≠ j₀ → φ (Pi.single j (g j)) = 0 := by
    intro j _ hj
    have horth : φ (Pi.single j (g j)) * φ (Pi.single j₀ 1) = 0 := by
      rw [← map_mul, single_mul_single_one hj, map_zero]
    rwa [h1, mul_one] at horth
  calc φ g = ∑ j, φ (Pi.single j (g j)) := hg
  _ = φ (Pi.single j₀ (g j₀)) :=
      Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h)
  _ = (factorComponent φ j₀ h1).comp (Pi.evalAlgHom K A j₀) g := rfl

private theorem factor_index_unique [Nontrivial Ω] [∀ j, Nontrivial (A j)] {j j' : J}
    {φ₀ : A j →ₐ[K] Ω} {φ₁ : A j' →ₐ[K] Ω}
    (h : φ₀.comp (Pi.evalAlgHom K A j) = φ₁.comp (Pi.evalAlgHom K A j')) : j = j' := by
  classical
  by_contra hne
  have happ := DFunLike.congr_fun h (Pi.single j 1)
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at happ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), map_one, map_zero] at happ
  exact one_ne_zero happ

end Factorisation

section SplitPoints

variable (K : Type*) [Field K] (Ω : Type*) [CommRing Ω] [Algebra K Ω]
variable {ι : Type*}

private def piPoint (i : ι) : (ι → K) →ₐ[K] Ω :=
  (Algebra.ofId K Ω).comp (Pi.evalAlgHom K (fun _ => K) i)

@[scoped simp] private theorem piPoint_apply (i : ι) (g : ι → K) :
    piPoint K Ω i g = algebraMap K Ω (g i) := rfl

private theorem piPoint_injective [Nontrivial Ω] :
    Function.Injective (piPoint K Ω (ι := ι)) := by
  intro i i' h
  by_contra hne
  classical
  have happ := DFunLike.congr_fun h (Pi.single i 1)
  rw [piPoint_apply, piPoint_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hne), map_one, map_zero] at happ
  exact one_ne_zero happ

private theorem algHom_pi_eq_piPoint [Finite ι] [IsDomain Ω] (φ : (ι → K) →ₐ[K] Ω) :
    ∃ i, φ = piPoint K Ω i := by
  obtain ⟨i, φ₀, hφ⟩ := exists_factor_algHom (A := fun _ : ι => K) φ
  refine ⟨i, hφ.trans ?_⟩
  congr 1
  exact AlgHom.ext fun x => φ₀.commutes x

private theorem existsUnique_piPoint_eq [Finite ι] [IsDomain Ω] (φ : (ι → K) →ₐ[K] Ω) :
    ∃! i, φ = piPoint K Ω i := by
  obtain ⟨i, hi⟩ := algHom_pi_eq_piPoint K Ω φ
  exact ⟨i, hi, fun i' hi' => piPoint_injective K Ω (hi'.symm.trans hi)⟩

private noncomputable def splitPointsEquiv [Finite ι] [IsDomain Ω] :
    ι ≃ ((ι → K) →ₐ[K] Ω) :=
  Equiv.ofBijective (piPoint K Ω)
    ⟨piPoint_injective K Ω,
     fun φ => (algHom_pi_eq_piPoint K Ω φ).imp fun _ h => h.symm⟩

end SplitPoints

section Faithfulness

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

private theorem points_separate_of_etale {B : Type u} [CommRing B] [Algebra K B] [Algebra.Etale K B]
    {x y : B} (h : ∀ χ : B →ₐ[K] Ω, χ x = χ y) : x = y := by
  obtain ⟨I, hfin, L, hfield, halg, e, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  haveI := hfin
  letI : ∀ i, Field (L i) := hfield
  letI : ∀ i, Algebra K (L i) := halg
  apply e.injective
  funext i
  haveI : Module.Finite K (L i) := (hL i).1
  have hχ := h (((IsAlgClosed.lift (M := Ω)).comp (Pi.evalAlgHom K L i)).comp e.toAlgHom)
  exact (IsAlgClosed.lift (R := K) (S := L i) (M := Ω)).toRingHom.injective hχ

private theorem algHom_ext_of_points {B : Type*} [Semiring B] [Algebra K B]
    {C : Type u} [CommRing C] [Algebra K C] [Algebra.Etale K C]
    {ψ₁ ψ₂ : B →ₐ[K] C} (h : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ :=
  AlgHom.ext fun b =>
    points_separate_of_etale (fun χ => DFunLike.congr_fun (h χ) b)

end Faithfulness

section RangeRealization

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
variable {L : Type*} [CommRing L] [Algebra K L]
variable {M : Type*} [Field M] [Algebra K M]

private noncomputable def homOfRangeLe (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (h : ∀ x, ∃ y, χ y = β x) : L →ₐ[K] M where
  toFun x := (h x).choose
  map_one' := χ.toRingHom.injective
    (show χ (h 1).choose = χ 1 from
      ((h 1).choose_spec.trans (map_one β)).trans (map_one χ).symm)
  map_mul' x y := χ.toRingHom.injective
    (show χ (h (x * y)).choose = χ ((h x).choose * (h y).choose) from
      (((h (x * y)).choose_spec.trans (map_mul β x y)).trans
        (congrArg₂ (· * ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_mul χ _ _).symm)
  map_zero' := χ.toRingHom.injective
    (show χ (h 0).choose = χ 0 from
      ((h 0).choose_spec.trans (map_zero β)).trans (map_zero χ).symm)
  map_add' x y := χ.toRingHom.injective
    (show χ (h (x + y)).choose = χ ((h x).choose + (h y).choose) from
      (((h (x + y)).choose_spec.trans (map_add β x y)).trans
        (congrArg₂ (· + ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_add χ _ _).symm)
  commutes' r := χ.toRingHom.injective
    (show χ (h (algebraMap K L r)).choose = χ (algebraMap K M r) from
      ((h (algebraMap K L r)).choose_spec.trans (β.commutes r)).trans (χ.commutes r).symm)

private theorem comp_homOfRangeLe (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (h : ∀ x, ∃ y, χ y = β x) :
    χ.comp (homOfRangeLe χ β h) = β :=
  AlgHom.ext fun x => (h x).choose_spec

end RangeRealization

section Conjugacy

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

private theorem exists_algEquiv_comp_eq {M : Type*} [Field M] [Algebra K M]
    (σ τ : M →ₐ[K] Ω) : ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by
  letI : Algebra M Ω := σ.toRingHom.toAlgebra
  haveI : IsScalarTower K M Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := K) (L := M) (M := Ω) (E := Ω) τ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  refine ⟨AlgEquiv.ofBijective φ (AlgHom.normal_bijective K Ω Ω φ),
    AlgHom.ext fun m => ?_⟩
  exact DFunLike.congr_fun hφ m

end Conjugacy

section FixedField

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

private theorem exists_preimage_of_equivariant_fix {M L : Type*} [Field M] [Algebra K M]
    [CommRing L] [Algebra K L] (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (hfix : ∀ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp χ = χ → γ.toAlgHom.comp β = β)
    (x : L) : ∃ y, χ y = β x := by
  have hmem : β x ∈ IntermediateField.fixedField χ.fieldRange.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro γ hγ
    have hχ : γ.toAlgHom.comp χ = χ := AlgHom.ext fun m =>
      ((IntermediateField.mem_fixingSubgroup_iff _ γ).mp hγ) (χ m)
        (AlgHom.mem_fieldRange.mpr ⟨m, rfl⟩)
    exact DFunLike.congr_fun (hfix γ hχ) x
  rw [InfiniteGalois.fixedField_fixingSubgroup χ.fieldRange] at hmem
  exact hmem

end FixedField

section ProductDescent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

private theorem exists_algHom_realizing_equivariant_pointsMap_pi_fields
    {I : Type v} {J : Type w} [Finite I] [Finite J]
    {L : I → Type*} {M : J → Type*}
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ j, Field (M j)] [∀ j, Algebra K (M j)]
    [∀ j, Algebra.IsAlgebraic K (M j)]
    (Φ : ((Π j, M j) →ₐ[K] Ω) → ((Π i, L i) →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : (Π j, M j) →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃ ψ : (Π i, L i) →ₐ[K] (Π j, M j), ∀ χ, χ.comp ψ = Φ χ := by
  classical

  let base : ∀ j, M j →ₐ[K] Ω := fun _ => IsAlgClosed.lift

  have hfac : ∀ j, ∃ (i : I) (β : L i →ₐ[K] Ω),
      Φ ((base j).comp (Pi.evalAlgHom K M j)) = β.comp (Pi.evalAlgHom K L i) :=
    fun _ => exists_factor_algHom _
  choose ix β hβ using hfac

  have hrange : ∀ j (x : L (ix j)), ∃ y, base j y = β j x := by
    intro j
    refine exists_preimage_of_equivariant_fix (base j) (β j) ?_
    intro γ hγ
    have hP : γ.toAlgHom.comp ((base j).comp (Pi.evalAlgHom K M j))
        = (base j).comp (Pi.evalAlgHom K M j) := by
      rw [← AlgHom.comp_assoc, hγ]
    have h2 : (γ.toAlgHom.comp (β j)).comp (Pi.evalAlgHom K L (ix j))
        = (β j).comp (Pi.evalAlgHom K L (ix j)) := by
      rw [AlgHom.comp_assoc, ← hβ j, ← hΦ γ, hP, hβ j]
    refine AlgHom.ext fun x => ?_
    obtain ⟨g, hg⟩ := Function.surjective_eval (β := fun i => L i) (ix j) x
    have hg' : g (ix j) = x := hg
    have happ := DFunLike.congr_fun h2 g
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at happ
    rw [hg'] at happ
    exact happ

  let ψfac : ∀ j, L (ix j) →ₐ[K] M j := fun j => homOfRangeLe (base j) (β j) (hrange j)
  have hψfac : ∀ j, (base j).comp (ψfac j) = β j := fun j => comp_homOfRangeLe _ _ _
  refine ⟨Pi.algHom K M (fun j => (ψfac j).comp (Pi.evalAlgHom K L (ix j))), fun χ => ?_⟩

  obtain ⟨j, χ₀, hχ⟩ := exists_factor_algHom χ
  obtain ⟨γ, hγ⟩ := exists_algEquiv_comp_eq (base j) χ₀
  have heval : (Pi.evalAlgHom K M j).comp
      (Pi.algHom K M fun j' => (ψfac j').comp (Pi.evalAlgHom K L (ix j')))
      = (ψfac j).comp (Pi.evalAlgHom K L (ix j)) :=
    AlgHom.ext fun _ => rfl
  have hcomp : χ.comp
      (Pi.algHom K M fun j' => (ψfac j').comp (Pi.evalAlgHom K L (ix j')))
      = γ.toAlgHom.comp ((β j).comp (Pi.evalAlgHom K L (ix j))) := by
    rw [hχ, AlgHom.comp_assoc, heval, ← hγ,
      AlgHom.comp_assoc γ.toAlgHom (base j) ((ψfac j).comp (Pi.evalAlgHom K L (ix j))),
      ← AlgHom.comp_assoc (base j) (ψfac j) (Pi.evalAlgHom K L (ix j)), hψfac j]
  have hRHS : Φ χ = γ.toAlgHom.comp ((β j).comp (Pi.evalAlgHom K L (ix j))) := by
    rw [hχ, ← hγ, AlgHom.comp_assoc, hΦ, hβ]
  rw [hcomp, hRHS]

end ProductDescent

section EtaleDescent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

private theorem exists_algHom_realizing_equivariant_pointsMap_of_etale
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃ ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ := by
  obtain ⟨I, hIfin, L, hLfield, hLalg, eB, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  obtain ⟨J, hJfin, M, hMfield, hMalg, eC, hM⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K C).mp inferInstance
  haveI := hIfin
  haveI := hJfin
  letI : ∀ i, Field (L i) := hLfield
  letI : ∀ i, Algebra K (L i) := hLalg
  letI : ∀ j, Field (M j) := hMfield
  letI : ∀ j, Algebra K (M j) := hMalg
  haveI : ∀ j, Module.Finite K (M j) := fun j => (hM j).1

  have hΦ' : ∀ (γ : Ω ≃ₐ[K] Ω) (χ' : (Π j, M j) →ₐ[K] Ω),
      (Φ ((γ.toAlgHom.comp χ').comp eC.toAlgHom)).comp eB.symm.toAlgHom
        = γ.toAlgHom.comp ((Φ (χ'.comp eC.toAlgHom)).comp eB.symm.toAlgHom) := by
    intro γ χ'
    rw [AlgHom.comp_assoc, hΦ γ, AlgHom.comp_assoc]
  obtain ⟨ψ', hψ'⟩ := exists_algHom_realizing_equivariant_pointsMap_pi_fields
    (L := L) (M := M)
    (fun χ' => (Φ (χ'.comp eC.toAlgHom)).comp eB.symm.toAlgHom)
    (fun γ χ' => hΦ' γ χ')
  refine ⟨(eC.symm.toAlgHom.comp ψ').comp eB.toAlgHom, fun χ => ?_⟩
  have h1 : (χ.comp eC.symm.toAlgHom).comp ψ'
      = (Φ ((χ.comp eC.symm.toAlgHom).comp eC.toAlgHom)).comp eB.symm.toAlgHom :=
    hψ' (χ.comp eC.symm.toAlgHom)
  have hcancelC : (χ.comp eC.symm.toAlgHom).comp eC.toAlgHom = χ :=
    AlgHom.ext fun c => congrArg χ (eC.symm_apply_apply c)
  have hcancelB : eB.symm.toAlgHom.comp eB.toAlgHom = AlgHom.id K B :=
    AlgHom.ext fun b => eB.symm_apply_apply b
  calc χ.comp ((eC.symm.toAlgHom.comp ψ').comp eB.toAlgHom)
      = ((χ.comp eC.symm.toAlgHom).comp ψ').comp eB.toAlgHom := by
        rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  _ = ((Φ ((χ.comp eC.symm.toAlgHom).comp eC.toAlgHom)).comp
        eB.symm.toAlgHom).comp eB.toAlgHom := by rw [h1]
  _ = Φ χ := by
        rw [hcancelC, AlgHom.comp_assoc, hcancelB, AlgHom.comp_id]

private theorem existsUnique_algHom_realizing_equivariant_pointsMap_of_etale
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_realizing_equivariant_pointsMap_of_etale Φ hΦ
  exact ⟨ψ, hψ, fun ψ' hψ' =>
    algHom_ext_of_points (fun χ => (hψ' χ).trans (hψ χ).symm)⟩

end EtaleDescent



end EtaleEquivariantPoints

/-- Every map between the geometric-point sets of two étale algebras that
commutes with every automorphism of the algebraically closed algebraic Galois
extension is induced by a unique algebra homomorphism in the opposite
direction. -/
public theorem Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ :=
  EtaleEquivariantPoints.existsUnique_algHom_realizing_equivariant_pointsMap_of_etale
    Φ hΦ
