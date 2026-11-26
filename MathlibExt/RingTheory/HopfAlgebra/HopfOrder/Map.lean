/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfOrder_isHopfOrder_map.lean`,
`P2M/Sol/S_HopfOrder_isHopfOrder_map.lean`,
`Theorems/Thm_HopfOrder_map_hopfKer_eq_inf_hopfKer.lean`, and
`P2M/Sol/S_HopfOrder_map_hopfKer_eq_inf_hopfKer.lean`
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

public import MathlibExt.RingTheory.HopfAlgebra.HopfKer
public import MathlibExt.RingTheory.HopfAlgebra.HopfOrder.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Flat.Domain
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Images of Hopf orders and their Hopf kernels

Let `R` be a principal ideal domain with fraction field `K`, and let `A` and `Ā` be commutative
Hopf algebras over `K` with compatible `R`-algebra structures. The image of a finite Hopf order
in `A` that spans `A` over `K` under a surjective bialgebra map `A → Ā` is a finite Hopf order in
`Ā` that spans `Ā` over `K` (`HopfOrder.isHopfOrder_map`). For a Hopf algebra `H` over `R`, free
as an `R`-module and embedded in `A` as a subalgebra `S`, and a compatible map to a free Hopf
algebra over `R` embedded in `Ā`, the image of the Hopf kernel of the integral map is the
intersection of `S` with the Hopf kernel over `K` (`HopfOrder.map_hopfKer_eq_inf_hopfKer`).
-/

@[expose] public section

open scoped TensorProduct

namespace HopfOrder

/-- **The image of a Hopf order is a Hopf order.** Let `R` be a principal ideal domain with
fraction field `K`, and `A`, `Ā` commutative Hopf algebras over `K` with compatible `R`-algebra
structures. Let `S` be an `R`-subalgebra of `A` that is finite over `R`, spans `A` over `K`, is
stable under the antipode, whose comultiplication lands in the image of `S ⊗[R] S` in
`A ⊗[K] A`, and whose counit takes values in the image of `R`. For a surjective `K`-bialgebra map
`π : A → Ā`, the image of `S` under `π` has the same five properties in `Ā`. -/
theorem isHopfOrder_map
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π) :
    Module.Finite R ↥((S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    Submodule.span K (((S.map ((π : A →ₐ[K] Ā).restrictScalars R)) : Subalgebra R Ā) : Set Ā) = ⊤ ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp
              ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp
              ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), HopfAlgebra.antipode K (A := Ā) x ∈
        (S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.counit (R := K) (A := Ā) x ∈
        (algebraMap R K).range) := by
  have hf : ∀ a : A, ((π : A →ₐ[K] Ā).restrictScalars R) a = π a := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hfin
    let g : ↥S →ₗ[R] ↥(Subalgebra.toSubmodule (S.map ((π : A →ₐ[K] Ā).restrictScalars R))) :=
      (((π : A →ₐ[K] Ā).restrictScalars R).toLinearMap ∘ₗ S.val.toLinearMap).codRestrict
        (Subalgebra.toSubmodule (S.map ((π : A →ₐ[K] Ā).restrictScalars R)))
        (fun s => Subalgebra.mem_map.mpr ⟨(s : A), s.2, rfl⟩)
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Module.Finite.of_surjective g hg
  · refine Submodule.eq_top_iff'.mpr fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have hx : x ∈ Submodule.span K (S : Set A) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem s hs =>
        exact Submodule.subset_span (Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul k a _ ha => rw [map_smul]; exact Submodule.smul_mem _ k ha
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    rw [hf]
    have hmap := congrArg (fun g : A →ₗ[K] Ā ⊗[K] Ā => g x) (CoalgHomClass.map_comp_comul π)
    simp only [LinearMap.comp_apply] at hmap
    have hco : Coalgebra.comul (R := K) (π x)
        = TensorProduct.map (π : A →ₐc[K] Ā).toLinearMap (π : A →ₐc[K] Ā).toLinearMap
            (Coalgebra.comul (R := K) x) := hmap.symm
    obtain ⟨t, ht⟩ : ∃ t, tensorSqHom (K := K) S t = Coalgebra.comul (R := K) x :=
      (AlgHom.mem_range _).mp (hcomul x hx)
    change Coalgebra.comul (R := K) (π x) ∈
      (tensorSqHom (K := K) (S.map ((π : A →ₐ[K] Ā).restrictScalars R))).range
    rw [hco, ← ht]
    clear ht
    induction t with
    | tmul s s' =>
        rw [tensorSqHom_tmul, TensorProduct.map_tmul]
        exact tmul_mem_range_tensorSqHom (K := K)
          (Subalgebra.mem_map.mpr ⟨(s : A), s.2, rfl⟩) (Subalgebra.mem_map.mpr
              ⟨(s' : A), s'.2, rfl⟩)
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add]; exact Subalgebra.add_mem _ h₁ h₂
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    rw [hf]
    exact Subalgebra.mem_map.mpr
      ⟨HopfAlgebra.antipode K x, hanti x hx, HopfAlgebra.HopfKerHopf.map_antipode π x⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    rw [hf]
    have hcu : Coalgebra.counit (π x) = Coalgebra.counit (R := K) x := by
      have h := congrArg (fun g : A →ₗ[K] K => g x) (CoalgHomClass.counit_comp π)
      simp
    rw [hcu]
    exact hcounit x hx

/-- **Hopf kernels of integral maps.** Let `R` be a principal ideal domain with fraction field
`K`, `A` and `Ā` commutative Hopf algebras over `K` with compatible `R`-algebra structures, and
`H`, `Hbar` commutative Hopf algebras over `R` that are free as `R`-modules. Let `e : H → A` be
an injective `R`-algebra map with image `S` such that the comultiplication of `e h` in
`A ⊗[K] A` is the image of the comultiplication of `h` under `e ⊗ e`, let `π : A → Ā` be a
`K`-bialgebra map and `q : H → Hbar` an `R`-bialgebra map, and let `ebar : Hbar → Ā` be an
injective `R`-algebra map with `ebar (q h) = π (e h)` for all `h`. Then the image under `e` of
the Hopf kernel of `q` is the intersection of `S` with the Hopf kernel of `π`. -/
theorem map_hopfKer_eq_inf_hopfKer
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Free R H]
    (e : H →ₐ[R] A) (he : Function.Injective e) (heS : e.range = S)
    (he_comul : ∀ h : H, Coalgebra.comul (R := K) (e h) =
        Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (Coalgebra.comul (R := R) h))
    (π : A →ₐc[K] Ā)
    {Hbar : Type*} [CommRing Hbar] [HopfAlgebra R Hbar] [Module.Free R Hbar]
    (q : H →ₐc[R] Hbar) (ebar : Hbar →ₐ[R] Ā) (hebar : Function.Injective ebar)
    (hsq : ∀ h : H, ebar (q h) = π (e h)) :
    (HopfAlgebra.hopfKer q).map e = S ⊓ (HopfAlgebra.hopfKer π).restrictScalars R := by
  classical
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : H ⊗[R] Hbar →ₐ[R] A ⊗[K] Ā, Φ =
      Algebra.TensorProduct.productMap
        (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] Ā).restrictScalars R).comp e)
        (((Algebra.TensorProduct.includeRight : Ā →ₐ[K] A ⊗[K] Ā).restrictScalars R).comp ebar) :=
    ⟨_, rfl⟩
  have hΦ_tmul : ∀ (x : H) (y : Hbar), Φ (x ⊗ₜ[R] y) = e x ⊗ₜ[K] ebar y := by
    intro x y
    rw [hΦdef, Algebra.TensorProduct.productMap_apply_tmul]
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hsquare : ∀ h : H, HopfAlgebra.coaction π (e h) = Φ (HopfAlgebra.coaction q h) := by
    intro h
    have hmaps :
        ((Algebra.TensorProduct.map (AlgHom.id K A) (π : A →ₐ[K] Ā)).restrictScalars R).comp
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e))
        = Φ.comp (Algebra.TensorProduct.map (AlgHom.id R H) (q : H →ₐ[R] Hbar)) := by
      ext x
      · simp [hΦ_tmul]
      · simp [hΦ_tmul, hsq]
    have happ := AlgHom.congr_fun hmaps (Coalgebra.comul (R := R) h)
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at happ
    rw [HopfAlgebra.coaction_apply, HopfAlgebra.coaction_apply, he_comul]
    exact happ
  have hΦinj : Function.Injective Φ := by
    obtain ⟨⟨ιH, bH⟩⟩ := Module.Free.exists_basis (R := R) (M := H)
    obtain ⟨⟨ιB, bB⟩⟩ := Module.Free.exists_basis (R := R) (M := Hbar)
    have hu : LinearIndependent K (fun i => e (bH i)) :=
      (LinearIndependent.iff_fractionRing R K).mp
        (bH.linearIndependent.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr he))
    have hw : LinearIndependent K (fun j => ebar (bB j)) :=
      (LinearIndependent.iff_fractionRing R K).mp
        (bB.linearIndependent.map' ebar.toLinearMap (LinearMap.ker_eq_bot.mpr hebar))
    have hT' := (LinearIndependent.iff_fractionRing R K).mpr (hu.tmul_of_isDomain hw)
    have hT : LinearIndependent R (fun ij : ιH × ιB => e (bH ij.1) ⊗ₜ[K] ebar (bB ij.2)) := by
      exact hT'
    have hfam : (Φ.toLinearMap ∘ (bH.tensorProduct bB) : ιH × ιB → A ⊗[K] Ā) =
        fun ij => e (bH ij.1) ⊗ₜ[K] ebar (bB ij.2) := by
      funext ij
      simp only [Function.comp_apply, Module.Basis.tensorProduct_apply', AlgHom.toLinearMap_apply,
        hΦ_tmul]
    intro x y hxy
    have key : Φ.toLinearMap (Finsupp.linearCombination R (bH.tensorProduct bB)
          ((bH.tensorProduct bB).repr x)) =
        Φ.toLinearMap (Finsupp.linearCombination R (bH.tensorProduct bB)
          ((bH.tensorProduct bB).repr y)) := by
      simpa only [Module.Basis.linearCombination_repr, AlgHom.toLinearMap_apply] using hxy
    rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination, hfam] at key
    exact (bH.tensorProduct bB).repr.injective
      ((linearIndependent_iff_injective_finsuppLinearCombination.mp hT) key)
  ext a
  simp only [Subalgebra.mem_map, Algebra.mem_inf, Subalgebra.mem_restrictScalars,
    HopfAlgebra.mem_hopfKer_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← heS]; exact e.mem_range_self h
    · rw [hsquare, hh, hΦ_tmul, map_one]
  · rintro ⟨haS, ha⟩
    have haR : a ∈ e.range := by rw [heS]; exact haS
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range e).mp haR
    refine ⟨h, ?_, rfl⟩
    apply hΦinj
    rw [← hsquare, ha, hΦ_tmul, map_one]

end HopfOrder
