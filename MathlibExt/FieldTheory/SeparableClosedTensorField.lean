/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.lean`
and
`P2M/Sol/S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.lean`
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

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.LinearDisjoint
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic

@[expose] public section

open Polynomial
open scoped TensorProduct IntermediateField

universe u v w

section Minpoly

variable {k F M : Type*} [Field k] [Field F] [Field M] [Algebra k F] [Algebra F M]
  [Algebra k M] [IsScalarTower k F M]

private theorem natDegree_minpoly_eq_aux
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range)
    {β : M} (hβ : IsSeparable k β) :
    (minpoly F β).natDegree = (minpoly k β).natDegree := by
  set K₁ : IntermediateField k F := algebraicClosure k F with hK₁
  haveI : IsPurelyInseparable k K₁ := by
    rw [isPurelyInseparable_iff]
    intro x
    refine ⟨Algebra.IsIntegral.isIntegral x, fun hx => ?_⟩
    have hx' : IsSeparable k (x : F) :=
      (isSeparable_map_iff K₁.val Subtype.val_injective).mpr hx
    obtain ⟨c, hc⟩ := hsc _ hx'
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hc]
    rfl
  have h1 : (minpoly k β).map (algebraMap k K₁) = minpoly K₁ β :=
    minpoly.map_eq_of_isSeparable_of_isPurelyInseparable K₁ β hβ
  have hβi : IsIntegral k β := hβ.isIntegral
  have hβ1 : IsIntegral K₁ β := hβi.tower_top
  have hPm : (minpoly k β).Monic := minpoly.monic hβi
  have hQm : (minpoly F β).Monic := minpoly.monic hβi.tower_top
  have hdvd : minpoly F β ∣ (minpoly k β).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F β
  have hlift : minpoly F β ∈ lifts (algebraMap K₁ F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F hPm hQm hdvd
    rw [lifts_iff_coeff_lifts] at h1
    obtain ⟨c, hc⟩ := h1 n
    exact ⟨⟨(c : F), c.2⟩, hc⟩
  obtain ⟨Q₁, hQ₁, hdeg, hQ₁m⟩ := lifts_and_natDegree_eq_and_monic hlift hQm
  have haeval : aeval β Q₁ = 0 := by
    rw [← aeval_map_algebraMap F β Q₁, hQ₁]
    exact minpoly.aeval F β
  have hd1 : (minpoly K₁ β).natDegree ≤ Q₁.natDegree :=
    natDegree_le_of_dvd (minpoly.dvd K₁ β haeval) hQ₁m.ne_zero
  have hd2 : (minpoly F β).natDegree ≤ (minpoly K₁ β).natDegree := by
    have hle := natDegree_le_of_dvd (minpoly.dvd_map_of_isScalarTower K₁ F β)
      ((minpoly.monic hβ1).map _).ne_zero
    rwa [natDegree_map] at hle
  have h3 : (minpoly K₁ β).natDegree = (minpoly k β).natDegree := by
    rw [← h1, natDegree_map]
  omega

end Minpoly

section Overfield

variable {k F K Ω : Type*} [Field k] [Field F] [Field K] [Field Ω]
  [Algebra k F] [Algebra k K] [Algebra k Ω] (fa : F →ₐ[k] Ω) (fb : K →ₐ[k] Ω)

private theorem hsc_range_aux
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range)
    (y : fa.fieldRange) (hy : IsSeparable k y) :
    y ∈ (algebraMap k fa.fieldRange).range := by
  have h0 : IsSeparable k (fa.fieldRange.val y) :=
    (isSeparable_map_iff fa.fieldRange.val Subtype.val_injective).mpr hy
  obtain ⟨y, z, rfl⟩ := y
  have hz : IsSeparable k z := (isSeparable_map_iff fa fa.injective).mp h0
  obtain ⟨c, hc⟩ := hsc z hz
  refine ⟨c, Subtype.ext ?_⟩
  change algebraMap k Ω c = fa z
  rw [← hc, fa.commutes]

private theorem linearDisjoint_adjoin_singleton_aux
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range)
    {x : Ω} (hx : IsSeparable k x) :
    fa.fieldRange.toSubalgebra.LinearDisjoint (Algebra.adjoin k {x}) := by
  have hxi : IsIntegral k x := hx.isIntegral
  let pb := Algebra.adjoin.powerBasis hxi
  refine Subalgebra.LinearDisjoint.of_basis_right _ _ pb.basis ?_
  have hfam : ((Algebra.adjoin k {x}).val ∘ pb.basis : Fin pb.dim → Ω) =
      fun i : Fin pb.dim => x ^ (i : ℕ) := by
    funext i
    simp only [Function.comp_apply, PowerBasis.coe_basis]
    rw [map_pow]
    congr 1
  rw [hfam]
  have hdim : pb.dim = (minpoly fa.fieldRange x).natDegree := by
    rw [Algebra.adjoin.powerBasis_dim hxi,
      natDegree_minpoly_eq_aux (k := k) (F := fa.fieldRange) (M := Ω) (hsc_range_aux fa hsc) hx]
  have hli : LinearIndependent fa.fieldRange
      fun i : Fin (minpoly fa.fieldRange x).natDegree => x ^ (i : ℕ) :=
    linearIndependent_pow (K := fa.fieldRange) x
  rw [← hdim] at hli
  exact hli

private theorem exists_le_adjoin_singleton_aux [Algebra.IsSeparable k K]
    (B' : Subalgebra k Ω) (hB' : B' ≤ fb.range) [Module.Finite k B'] :
    ∃ β : K, B' ≤ Algebra.adjoin k {fb β} := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := k) (M := B')
  have hpre : ∀ i, ∃ y : K, fb y = (s i : Ω) := fun i => hB' (s i).2
  choose y hy using hpre
  let S : Set K := Set.range y
  let K₀ : IntermediateField k K := IntermediateField.adjoin k S
  haveI : FiniteDimensional k K₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Algebra.IsSeparable k K₀ := Algebra.isSeparable_tower_bot_of_isSeparable k K₀ K
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k K₀
  refine ⟨(α : K), ?_⟩
  have hK₀ : K₀ = k⟮(α : K)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple k K₀ α, hα, IntermediateField.lift_top]
  have hβint : IsIntegral k (α : K) := Algebra.IsIntegral.isIntegral _
  have hmem : ∀ i, (s i : Ω) ∈ Algebra.adjoin k {fb (α : K)} := by
    intro i
    have hyi : y i ∈ K₀ := IntermediateField.subset_adjoin k S ⟨i, rfl⟩
    rw [hK₀, ← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβint.isAlgebraic] at hyi
    rw [← hy i, ← Set.image_singleton, Algebra.adjoin_image]
    exact Subalgebra.mem_map.mpr ⟨y i, hyi, rfl⟩
  intro t ht
  have ht' : (⟨t, ht⟩ : B') ∈ Submodule.span k (Set.range s) := by
    rw [hs]; exact Submodule.mem_top
  have himg : t ∈ (Submodule.span k (Set.range s)).map B'.val.toLinearMap :=
    ⟨⟨t, ht⟩, ht', rfl⟩
  rw [Submodule.map_span] at himg
  refine (Submodule.span_le.mpr ?_ : Submodule.span k _ ≤
    Subalgebra.toSubmodule (Algebra.adjoin k {fb (α : K)})) himg
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hmem i

private theorem linearDisjoint_range_aux [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    fa.fieldRange.toSubalgebra.LinearDisjoint fb.range := by
  haveI : Algebra.IsIntegral k fb.range := by
    refine ⟨fun x => ?_⟩
    obtain ⟨_, y, rfl⟩ := x
    exact (isIntegral_algHom_iff fb.range.val Subtype.val_injective).mp
      ((Algebra.IsIntegral.isIntegral (R := k) y).map fb)
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right _ _ fun B' hB' _ => ?_
  obtain ⟨β, hβ⟩ := exists_le_adjoin_singleton_aux fb B' hB'
  exact (linearDisjoint_adjoin_singleton_aux fa hsc
    ((Algebra.IsSeparable.isSeparable k β).map fb fb.injective)).of_le_right_of_flat hβ

end Overfield

namespace Algebra.TensorProduct

/-- If `k` is relatively separably closed in `F` (every element of `F`
separable over `k` lies in the image of `k`) and `K / k` is a separable
algebraic field extension, then `F ⊗[k] K` is a field. The fields may live
in arbitrary universes. -/
public theorem isField_of_isSeparable_of_forall_isSeparable_mem_range
    (k : Type u) (F : Type v) (K : Type w) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) := by
  apply IntermediateField.LinearDisjoint.isField_of_forall
  intro Ω _ _ fa fb
  rw [IntermediateField.linearDisjoint_iff]
  have hr : (IsScalarTower.toAlgHom k (↥fb.fieldRange) Ω).range = fb.range := by
    ext x
    constructor
    · rintro ⟨⟨_, z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨fb z, z, rfl⟩, rfl⟩
  rw [hr]
  exact linearDisjoint_range_aux fa fb hsc

end Algebra.TensorProduct
