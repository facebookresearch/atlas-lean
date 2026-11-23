/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgHom_length_quotient_congruenceIdeal_le_length_cotangent.lean`
and
`P2M/Sol/S_AlgHom_length_quotient_congruenceIdeal_le_length_cotangent.lean`
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

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

set_option autoImplicit false

open IsLocalRing Module
open scoped Matrix

namespace AlgHomCotangentAux

section LengthPID

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]

private theorem length_quotient_span_mul (a b : 𝒪) (hb : b ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {a * b}) =
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {a}) + Module.length 𝒪 (𝒪 ⧸ Ideal.span {b}) := by

  let f : (𝒪 ⧸ Ideal.span {a}) →ₗ[𝒪] (𝒪 ⧸ Ideal.span {a * b}) :=
    Submodule.mapQ (Ideal.span {a}) (Ideal.span {a * b}) (LinearMap.lsmul 𝒪 𝒪 b) (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      change b • (c * a) ∈ Ideal.span {a * b}
      exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [smul_eq_mul]; ring⟩)
  let g : (𝒪 ⧸ Ideal.span {a * b}) →ₗ[𝒪] (𝒪 ⧸ Ideal.span {b}) :=
    Submodule.mapQ (Ideal.span {a * b}) (Ideal.span {b}) LinearMap.id (by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact Ideal.mem_span_singleton'.mpr ⟨c * a, by simp [mul_assoc]⟩)
  have hfx : ∀ x : 𝒪, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (b * x) := fun x => rfl
  have hgx : ∀ x : 𝒪, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => rfl
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hfx, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    have : x = c * a := by
      have h1 : b * x = b * (c * a) := by rw [← hc]; ring
      exact mul_left_cancel₀ hb h1
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton'.mpr ⟨c, this.symm⟩)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, hgx y⟩
  have hfg : Function.Exact f g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      rw [hgx, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨Submodule.Quotient.mk c, by rw [hfx]; exact congrArg _ (mul_comm b c)⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hfx] at hx
      rw [← hx, hgx, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_comm]⟩
  rw [Module.length_eq_add_of_exact f g hf hg hfg]

private theorem length_quotient_span_prod {ι : Type*} (s : Finset ι) (a : ι → 𝒪)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {∏ i ∈ s, a i}) =
      ∑ i ∈ s, Module.length 𝒪 (𝒪 ⧸ Ideal.span {a i}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine Module.length_eq_zero_iff.mpr ?_
    rw [Submodule.Quotient.subsingleton_iff, Finset.prod_empty]
    exact Ideal.span_singleton_one
  | insert j s hj ih =>
    have e := Submodule.quotEquivOfEq (Ideal.span {∏ i ∈ insert j s, a i})
      (Ideal.span {(∏ i ∈ s, a i) * a j}) (by rw [Finset.prod_insert hj, mul_comm])
    rw [e.length_eq, Finset.sum_insert hj,
      length_quotient_span_mul _ _ (ha j (Finset.mem_insert_self j s)), add_comm,
      ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))]

end LengthPID



section Cotangent

variable {𝒪 : Type*} [CommRing 𝒪] {R : Type*} [CommRing R] [Algebra 𝒪 R] (π : R →ₐ[𝒪] 𝒪)

private theorem smul_cotangent_eq (r : R) (m : (RingHom.ker π).Cotangent) : r • m = (π r) • m := by
  obtain ⟨x, rfl⟩ := (RingHom.ker π).toCotangent_surjective m
  rw [← IsScalarTower.algebraMap_smul R (π r), ← sub_eq_zero, ← sub_smul, ← map_smul,
    Ideal.toCotangent_eq_zero, sq]
  refine Ideal.mul_mem_mul ?_ x.2
  simp [RingHom.mem_ker]

variable {n : ℕ} (a : Fin n → R) (hI : Ideal.span (Set.range a) = RingHom.ker π)

private def gen (i : Fin n) : RingHom.ker π := ⟨a i, hI ▸ Ideal.subset_span (Set.mem_range_self i)⟩

@[scoped simp] private theorem coe_gen (i : Fin n) : (gen π a hI i : R) = a i := rfl

private noncomputable def psi : (Fin n → 𝒪) →ₗ[𝒪] (RingHom.ker π).Cotangent :=
  Fintype.linearCombination 𝒪 (fun i => (RingHom.ker π).toCotangent (gen π a hI i))

private theorem psi_apply (w : Fin n → 𝒪) :
    psi π a hI w = (RingHom.ker π).toCotangent (∑ i, algebraMap 𝒪 R (w i) • gen π a hI i) := by
  simp only [psi, Fintype.linearCombination_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IsScalarTower.algebraMap_smul]

include hI in
private theorem psi_surjective : Function.Surjective (psi π a hI) := by
  intro m
  obtain ⟨x, rfl⟩ := (RingHom.ker π).toCotangent_surjective m
  have hx : (x : R) ∈ Ideal.span (Set.range a) := by rw [hI]; exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  refine ⟨fun i => π (c i), ?_⟩
  rw [psi_apply]
  have hx' : x = ∑ i, c i • gen π a hI i := by
    apply Subtype.ext
    simp [← hc]
  rw [hx', map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, IsScalarTower.algebraMap_smul, ← smul_cotangent_eq]

private theorem exists_syzygy_of_psi_eq_zero (w : Fin n → 𝒪) (hw : psi π a hI w = 0) :
    ∃ c : Fin n → R, (∀ i, c i ∈ RingHom.ker π) ∧
      ∑ i, (algebraMap 𝒪 R (w i) - c i) * a i = 0 := by
  classical
  rw [psi_apply, Ideal.toCotangent_eq_zero] at hw
  have h2 : (RingHom.ker π) ^ 2 = (RingHom.ker π) • Ideal.span (Set.range a) := by
    rw [sq, hI]; rfl
  rw [h2] at hw
  have hw' : (∑ i, algebraMap 𝒪 R (w i) * a i) ∈
      (RingHom.ker π) • Submodule.span R (Set.range a) := by
    convert hw using 1
    simp [Algebra.smul_def]
  obtain ⟨cf, hcf, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp hw'
  refine ⟨fun i => cf i, hcf, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)] at hsum
  simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
  rw [← hsum]
  simp [smul_eq_mul]

private theorem det_mem_eta (v : Fin n → (Fin n → 𝒪)) (hv : ∀ j, psi π a hI (v j) = 0) :
    (Matrix.of fun i j => v j i).det ∈ (RingHom.ker π).annihilator.map π := by
  classical
  choose C hC hCsum using fun j => exists_syzygy_of_psi_eq_zero π a hI (v j) (hv j)
  let V : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => algebraMap 𝒪 R (v j i) - C j i
  have hVa : V *ᵥ a = 0 := by
    ext j
    simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact hCsum j
  have hdet : ∀ i, V.det * a i = 0 := by
    intro i
    have h := congrArg (fun u => (V.adjugate *ᵥ u) i) hVa
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Pi.zero_apply] at h
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simpa using h
  have hann : V.det ∈ (RingHom.ker π).annihilator := by
    rw [← hI, show Ideal.span (Set.range a) = Submodule.span R (Set.range a) from rfl,
      Submodule.mem_annihilator_span]
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hdet i
  have hmap : π V.det = (Matrix.of fun i j => v j i).det := by
    rw [AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext i j
    have : π (C j i) = 0 := hC j i
    simp [V, Matrix.transpose_apply, AlgHom.mapMatrix_apply, this]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hann

end Cotangent

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
  {R : Type*} [CommRing R] [Algebra 𝒪 R]

omit [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] in

private theorem basisFun_det_eq {n : ℕ} (v : Fin n → (Fin n → 𝒪)) :
    (Pi.basisFun 𝒪 (Fin n)).det v = (Matrix.of fun i j => v j i).det := by
  rw [Basis.det_apply]
  congr 1

private theorem length_quotient_eta_le_length_cotangent (π : R →ₐ[𝒪] 𝒪) (hfg : (RingHom.ker π).FG) :
    Module.length 𝒪 (𝒪 ⧸ (RingHom.ker π).annihilator.map π) ≤
      Module.length 𝒪 (RingHom.ker π).Cotangent := by
  classical
  obtain ⟨s, hs⟩ := hfg
  set n := s.card
  let a : Fin n → R := fun i => ((s.equivFin.symm i : s) : R)
  have hrange : Set.range a = (s : Set R) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
    · intro hx; exact ⟨s.equivFin ⟨x, hx⟩, by simp [a]⟩
  have hI : Ideal.span (Set.range a) = RingHom.ker π := by rw [hrange, hs]

  set ψ := psi π a hI
  have hψ := psi_surjective π a hI
  set N := LinearMap.ker ψ
  have hΦ : Module.length 𝒪 (RingHom.ker π).Cotangent = Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) :=
    ((ψ.quotKerEquivOfSurjective hψ).length_eq).symm
  rw [hΦ]
  set e := Pi.basisFun 𝒪 (Fin n)
  obtain ⟨m, snf⟩ := N.smithNormalForm e
  by_cases hmn : m = n
  ·
    have h : Module.finrank 𝒪 N = Module.finrank 𝒪 (Fin n → 𝒪) := by
      rw [Module.finrank_eq_card_basis snf.bN, Module.finrank_fin_fun, Fintype.card_fin, hmn]
    set c := Submodule.smithNormalFormCoeffs e h
    have hc : ∀ i, c i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero e h

    have hlen : Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) =
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {∏ i, c i}) := by
      rw [(Submodule.quotientEquivPiSpan N e h).length_eq, Module.length_pi_of_fintype,
        length_quotient_span_prod _ _ (fun i _ => hc i)]

    have hprod : (∏ i, c i) ∈ (RingHom.ker π).annihilator.map π := by
      let v : Fin n → (Fin n → 𝒪) :=
        fun j => (Submodule.smithNormalFormBotBasis e h j : (Fin n → 𝒪))
      have hv : ∀ j, ψ (v j) = 0 := fun j =>
        LinearMap.mem_ker.mp (Submodule.smithNormalFormBotBasis e h j).2
      have hdet := det_mem_eta π a hI v hv
      rw [← basisFun_det_eq] at hdet
      have hv' : v = fun j => c j • Submodule.smithNormalFormTopBasis e h j := by
        funext j; exact Submodule.smithNormalFormBotBasis_def e h j
      rw [hv', AlternatingMap.map_smul_univ] at hdet
      obtain ⟨u, hu⟩ := e.isUnit_det (Submodule.smithNormalFormTopBasis e h)
      rw [← hu, smul_eq_mul] at hdet
      have := Ideal.mul_mem_right (↑u⁻¹ : 𝒪) _ hdet
      rwa [mul_assoc, Units.mul_inv, mul_one] at this
    rw [hlen]

    refine Module.length_le_of_surjective
      (Submodule.mapQ (Ideal.span {∏ i, c i})
        ((RingHom.ker π).annihilator.map π) LinearMap.id ?_) ?_
    · simpa [Ideal.span_le] using hprod
    · intro y; obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk y, rfl⟩
  ·
    have hns : ∃ i, i ∉ Set.range snf.f := by
      by_contra hcon
      have hsurj : Function.Surjective snf.f := fun i => by
        by_contra h'
        exact hcon ⟨i, fun ⟨j, hj⟩ => h' ⟨j, hj⟩⟩
      have := Fintype.card_le_of_surjective _ hsurj
      have := Fintype.card_le_of_embedding snf.f
      simp only [Fintype.card_fin] at *
      omega
    obtain ⟨i, hi⟩ := hns
    have hle := snf.le_ker_coord_of_notMem_range hi
    let lam : ((Fin n → 𝒪) ⧸ N) →ₗ[𝒪] 𝒪 := N.liftQ (snf.bM.coord i) hle
    have hlam : Function.Surjective lam := by
      intro o
      refine ⟨Submodule.Quotient.mk (o • snf.bM i), ?_⟩
      simp [lam]
    calc Module.length 𝒪 (𝒪 ⧸ (RingHom.ker π).annihilator.map π)
        ≤ Module.length 𝒪 𝒪 := Module.length_le_of_surjective
            (Submodule.mkQ ((RingHom.ker π).annihilator.map π)) (Submodule.mkQ_surjective _)
      _ ≤ Module.length 𝒪 ((Fin n → 𝒪) ⧸ N) := Module.length_le_of_surjective lam hlam

end Main
end AlgHomCotangentAux

/-- For a surjective algebra map compatible with augmentations to a principal
ideal domain, the length of the quotient by the congruence ideal is at most
the length of the cotangent module of the source augmentation. -/
public theorem AlgHom.length_quotient_congruenceIdeal_le_length_cotangent
    {𝒪 : Type*} {R : Type*} {T : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hfg : (RingHom.ker πR).FG) :
    Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ≤
      Module.length 𝒪 (RingHom.ker πR).Cotangent := by

  have hη : (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πT).annihilator.map πT := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Ideal.mem_comap, show πR x = πT (φ x) from (AlgHom.congr_fun hπ x).symm]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Submodule.mem_annihilator] at hx ⊢
    intro t ht
    obtain ⟨r, rfl⟩ := hφ t
    have hr : r ∈ RingHom.ker πR := by
      rw [RingHom.mem_ker, ← AlgHom.congr_fun hπ r]; exact ht
    rw [smul_eq_mul, ← map_mul, ← smul_eq_mul, hx r hr, map_zero]
  calc Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT)
      ≤ Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πR).annihilator.map πR) :=
        Module.length_le_of_surjective
          (Submodule.mapQ _ _ LinearMap.id (by simpa using hη))
          (by intro y; obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
              exact ⟨Submodule.Quotient.mk y, rfl⟩)
    _ ≤ Module.length 𝒪 (RingHom.ker πR).Cotangent :=
        AlgHomCotangentAux.length_quotient_eta_le_length_cotangent πR hfg