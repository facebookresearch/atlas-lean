/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_
expChar_pow_sub_isNilpotent.lean`
and
`P2M/Sol/S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_
expChar_pow_sub_isNilpotent.lean`
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

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

universe u v w


namespace MaximalEtaleSubalgebraAux


open Algebra

section ProdToDomain

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ι → Type*} [∀ i, CommRing (R i)]
  {S : Type*} [CommRing S] [IsDomain S]

private theorem exists_eq_apply_single (f : (∀ i, R i) →+* S) :
    ∃ i₀ : ι, f (Pi.single i₀ 1) = 1 ∧ ∀ x, f x = f (Pi.single i₀ (x i₀)) := by
  classical

  have hidem : ∀ i, f (Pi.single i 1) = 0 ∨ f (Pi.single i 1) = 1 := fun i => by
    have h : f (Pi.single i 1) * f (Pi.single i 1) = f (Pi.single i 1) := by
      rw [← map_mul, ← Pi.single_mul, mul_one]
    rcases mul_eq_zero.mp (by rw [mul_sub, mul_one, h, sub_self] :
      f (Pi.single i 1) * (f (Pi.single i 1) - 1) = 0) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hsum : ∑ i, f (Pi.single i (1 : R i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : _))]; exact map_one f
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, f (Pi.single i₀ 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ i, f (Pi.single i (1 : R i)) = 0 :=
      Finset.sum_eq_zero fun i _ => (hidem i).resolve_right (h i)
    rw [this] at hsum
    exact zero_ne_one hsum
  refine ⟨i₀, hi₀, fun x => ?_⟩
  have hx : x = Pi.single i₀ (x i₀) + x * (1 - Pi.single i₀ 1) := by
    ext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi₀, sub_self, mul_zero, add_zero]

private noncomputable def factorHom (f : (∀ i, R i) →+* S) :
    R (exists_eq_apply_single f).choose →+* S where
  toFun := fun r => f (Pi.single (exists_eq_apply_single f).choose r)
  map_one' := (exists_eq_apply_single f).choose_spec.1
  map_mul' := fun a b => by rw [← map_mul, ← Pi.single_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' := fun a b => by rw [← map_add, ← Pi.single_add]

private theorem factorHom_apply (f : (∀ i, R i) →+* S) (x : ∀ i, R i) :
    factorHom f (x (exists_eq_apply_single f).choose) = f x :=
  ((exists_eq_apply_single f).choose_spec.2 x).symm

end ProdToDomain

section Separable

variable (k : Type u) [Field k]

private theorem isSeparable_apply_of_etale {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.Etale k S]
    {F : Type w} [Field F] [Algebra k F] (ψ : S →ₐ[k] F) (s : S) : IsSeparable k (ψ s) := by
  classical
  obtain ⟨I, hI, L, hL, hLa, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k S).mp inferInstance
  haveI := hI
  haveI := Fintype.ofFinite I

  let f : (∀ i, L i) →+* F := (ψ.comp (e.symm : (∀ i, L i) →ₐ[k] S)).toRingHom
  let i₀ := (exists_eq_apply_single f).choose
  haveI : Algebra.IsSeparable k (L i₀) := (hsep i₀).2

  let g : L i₀ →ₐ[k] F :=
    { factorHom f with
      commutes' := fun r => by
        have h1 : factorHom f ((algebraMap k (∀ i, L i) r) i₀) = f (algebraMap k _ r) :=
          factorHom_apply f _
        rw [Pi.algebraMap_apply] at h1
        show factorHom f (algebraMap k (L i₀) r) = _
        rw [h1]
        show ψ (e.symm (algebraMap k _ r)) = _
        rw [AlgEquiv.commutes, AlgHom.commutes] }
  have hψ : ψ s = g ((e s) i₀) := by
    show ψ s = factorHom f ((e s) i₀)
    rw [factorHom_apply]
    show ψ s = ψ (e.symm (e s))
    rw [AlgEquiv.symm_apply_apply]
  rw [hψ]
  show (minpoly k (g ((e s) i₀))).Separable
  rw [minpoly.algHom_eq g g.toRingHom.injective]
  exact Algebra.IsSeparable.isSeparable k _

end Separable

section Core

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A]

attribute [local instance] Ideal.Quotient.field

private instance maximalSpectrum_isMaximal {R : Type*} [CommRing R]
    (I : MaximalSpectrum R) : I.asIdeal.IsMaximal := I.isMaximal

private abbrev Ared : Type v := A ⧸ nilradical A

private instance : IsReduced (Ared A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)

private abbrev Fi (I : MaximalSpectrum (Ared A)) : Type v := Ared A ⧸ I.asIdeal

include k in
private theorem isArtinianRing_Ared : IsArtinianRing (Ared A) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  infer_instance

private noncomputable def piEquiv : Ared A ≃ₐ[k] (∀ I : MaximalSpectrum (Ared A), Fi A I) :=
  haveI : IsArtinianRing (Ared A) := isArtinianRing_Ared k A
  (IsArtinianRing.equivPi (Ared A)).restrictScalars k

private noncomputable def Ebar : Subalgebra k (Ared A) :=
  (Subalgebra.pi Set.univ fun I : MaximalSpectrum (Ared A) =>
    (separableClosure k (Fi A I)).toSubalgebra).comap
    (piEquiv k A : Ared A →ₐ[k] ∀ I, Fi A I)

private theorem mem_Ebar {x : Ared A} : x ∈ Ebar k A ↔ ∀ I, IsSeparable k (piEquiv k A x I) := by
  simp [Ebar, Subalgebra.mem_pi, mem_separableClosure_iff]

private noncomputable def EbarEquiv :
    Ebar k A ≃ₐ[k] (∀ I : MaximalSpectrum (Ared A), separableClosure k (Fi A I)) where
  toFun := fun x => fun I =>
    ⟨piEquiv k A x I, (mem_separableClosure_iff).mpr ((mem_Ebar k A).mp x.2 I)⟩
  invFun := fun y => ⟨(piEquiv k A).symm (fun I => (y I : Fi A I)), (mem_Ebar k A).mpr fun I => by
      rw [AlgEquiv.apply_symm_apply]; exact (mem_separableClosure_iff).mp (y I).2⟩
  left_inv := fun x => by ext; simp
  right_inv := fun y => by ext I; simp
  map_mul' := fun x y => by ext I; simp
  map_add' := fun x y => by ext I; simp
  commutes' := fun r => by ext I; simp [Pi.algebraMap_apply]

private theorem etale_Ebar : Algebra.Etale k (Ebar k A) := by
  haveI : IsArtinianRing (Ared A) := isArtinianRing_Ared k A
  refine (Algebra.Etale.iff_exists_algEquiv_prod k (Ebar k A)).mpr
    ⟨MaximalSpectrum (Ared A), inferInstance,
      fun I => separableClosure k (Fi A I), inferInstance, inferInstance,
      EbarEquiv k A, fun I => ⟨inferInstance, inferInstance⟩⟩

end Core

section Main

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A]

attribute [local instance] Ideal.Quotient.field

private noncomputable abbrev red : A →ₐ[k] Ared A := Ideal.Quotient.mkₐ k (nilradical A)

private theorem red_surjective : Function.Surjective (red k A) := Ideal.Quotient.mkₐ_surjective k _

include k in
private theorem isNilpotent_nilradical_aux : IsNilpotent (nilradical A) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact IsArtinianRing.isNilpotent_nilradical A

private theorem isNilpotent_ker_red : IsNilpotent (RingHom.ker (red k A : A →+* Ared A)) := by
  have : RingHom.ker (red k A : A →+* Ared A) = nilradical A := Ideal.Quotient.mkₐ_ker k _
  rw [this]; exact isNilpotent_nilradical_aux k A

private noncomputable def lift : Ebar k A →ₐ[k] A :=
  haveI := etale_Ebar k A
  Algebra.FormallySmooth.liftOfSurjective (Ebar k A).val (red k A) (red_surjective k A)
    (isNilpotent_ker_red k A)

private theorem red_lift (x : Ebar k A) : red k A (lift k A x) = (x : Ared A) := by
  haveI := etale_Ebar k A
  exact Algebra.FormallySmooth.liftOfSurjective_apply (Ebar k A).val (red k A) (red_surjective k A)
    (isNilpotent_ker_red k A) x

private theorem lift_injective : Function.Injective (lift k A) := fun x y h => by
  apply Subtype.ext
  rw [← red_lift k A x, ← red_lift k A y, h]

private noncomputable def P : Subalgebra k A := (lift k A).range

private theorem etale_P : Algebra.Etale k (P k A) := by
  haveI : IsArtinianRing (Ared A) := isArtinianRing_Ared k A
  let e : P k A ≃ₐ[k] Ebar k A := (AlgEquiv.ofInjective (lift k A) (lift_injective k A)).symm
  refine (Algebra.Etale.iff_exists_algEquiv_prod k (P k A)).mpr
    ⟨MaximalSpectrum (Ared A), inferInstance,
      fun I => separableClosure k (Fi A I), inferInstance, inferInstance,
      e.trans (EbarEquiv k A), fun I => ⟨inferInstance, inferInstance⟩⟩

private theorem red_mem_Ebar (S : Subalgebra k A) [Algebra.Etale k S] (s : S) :
    red k A (s : A) ∈ Ebar k A := by
  rw [mem_Ebar]
  intro I
  let ψ : S →ₐ[k] Fi A I :=
    (Pi.evalAlgHom k (fun J => Fi A J) I).comp
      ((piEquiv k A : Ared A →ₐ[k] ∀ J, Fi A J).comp ((red k A).comp S.val))
  exact isSeparable_apply_of_etale k ψ s

private theorem le_P (S : Subalgebra k A) (hS : Algebra.Etale k S) : S ≤ P k A := by
  intro s hs

  let ρ : S →ₐ[k] Ebar k A :=
    ((red k A).comp S.val).codRestrict (Ebar k A) (fun x => red_mem_Ebar k A S x)
  let φ : S →ₐ[k] A := (lift k A).comp ρ
  have hφ : S.val = φ := by
    refine Algebra.FormallyUnramified.ext (nilradical A)
      (isNilpotent_nilradical_aux k A) fun x => ?_
    show red k A (x : A) = red k A (lift k A (ρ x))
    rw [red_lift]
    rfl
  have : (⟨s, hs⟩ : S).val = φ ⟨s, hs⟩ := by rw [← hφ]; rfl
  rw [show s = φ ⟨s, hs⟩ from this]
  exact ⟨ρ ⟨s, hs⟩, rfl⟩

private theorem exists_pow_sub_isNilpotent (x : A) :
    ∃ (n : ℕ) (y : A), y ∈ P k A ∧ IsNilpotent (x ^ ringExpChar k ^ n - y) := by
  classical
  haveI : IsArtinianRing (Ared A) := isArtinianRing_Ared k A
  haveI := Fintype.ofFinite (MaximalSpectrum (Ared A))
  let q := ringExpChar k

  have hI : ∀ I : MaximalSpectrum (Ared A), ∃ n : ℕ,
      IsSeparable k ((piEquiv k A (red k A x) I) ^ q ^ n) := by
    intro I
    haveI : ExpChar (separableClosure k (Fi A I)) q :=
      expChar_of_injective_algebraMap (algebraMap k _).injective q
    haveI : Algebra.IsAlgebraic k (Fi A I) := Algebra.IsAlgebraic.of_finite k _
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (separableClosure k (Fi A I)) q
      (piEquiv k A (red k A x) I)
    refine ⟨n, ?_⟩
    obtain ⟨z, hz⟩ := hn
    rw [← hz]
    exact (mem_separableClosure_iff).mp z.2
  choose n hn using hI
  refine ⟨Finset.univ.sup n, ?_⟩
  have hmem : red k A (x ^ q ^ Finset.univ.sup n) ∈ Ebar k A := by
    rw [mem_Ebar]
    intro I
    rw [map_pow, map_pow, Pi.pow_apply]
    have hle : n I ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ I)
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [hm, pow_add, pow_mul]
    exact (mem_separableClosure_iff).mp (pow_mem ((mem_separableClosure_iff).mpr (hn I)) _)
  refine ⟨lift k A ⟨_, hmem⟩, ⟨_, rfl⟩, ?_⟩
  have h : red k A (x ^ q ^ Finset.univ.sup n - lift k A ⟨_, hmem⟩) = 0 := by
    rw [map_sub, red_lift, sub_self]
  have h' : Ideal.Quotient.mk (nilradical A)
      (x ^ q ^ Finset.univ.sup n - lift k A ⟨_, hmem⟩) = 0 := h
  rw [← mem_nilradical]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'

private theorem core : ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) :=
  ⟨P k A, etale_P k A, le_P k A, exists_pow_sub_isNilpotent k A⟩

end Main

end MaximalEtaleSubalgebraAux

namespace Algebra

/-- A finite algebra over a field has a largest étale subalgebra: every
étale subalgebra is contained in it, and every element has a
`ringExpChar`-power congruent to an element of it modulo nilpotents. -/
public theorem
    exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) :=
  MaximalEtaleSubalgebraAux.core k A

end Algebra
