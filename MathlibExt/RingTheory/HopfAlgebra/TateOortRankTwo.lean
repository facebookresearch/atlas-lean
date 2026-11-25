/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_exists_basis_tateOort_two.lean`
and
`P2M/Sol/S_HopfAlgebra_exists_basis_tateOort_two.lean`
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

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

@[expose] public section

open scoped TensorProduct
open Coalgebra

universe u v

private theorem exists_basis_one_counit_zero {R : Type u} [CommRing R] {H : Type v}
    [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) :
    ∃ e : Module.Basis (Fin 2) R H, e 0 = 1 ∧ counit (R := R) (e 1) = 0 := by
  haveI : Nontrivial R := by
    by_contra hR
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have : Module.finrank R H = 1 := by simp
    omega
  let e' : Module.Basis (Fin 2) R H := Module.finBasisOfFinrankEq R H hrank
  set α := e'.repr 1 0 with hα
  set β := e'.repr 1 1 with hβ
  set u := counit (R := R) (e' 0) with hu
  set v := counit (R := R) (e' 1) with hv
  have h1 : (1 : H) = α • e' 0 + β • e' 1 := by
    conv_lhs => rw [← e'.sum_repr 1]
    rw [Fin.sum_univ_two]
  have huv : α * u + β * v = 1 := by
    have := congr(counit (R := R) $h1)
    rw [Bialgebra.counit_one, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact this.symm
  set x : H := v • e' 0 - u • e' 1 with hxdef
  have hx : counit (R := R) x = 0 := by
    simp only [hxdef, map_sub, map_smul, smul_eq_mul]
    rw [← hu, ← hv]; ring
  have hli : LinearIndependent R ![(1 : H), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [h1, hxdef] at hst
    have hst' : (s * α + t * v) • e' 0 + (s * β - t * u) • e' 1 = 0 := by
      rw [← hst]; module
    have key := Fintype.linearIndependent_iff.mp e'.linearIndependent
      ![s * α + t * v, s * β - t * u]
      (by simpa [Fin.sum_univ_two] using hst')
    have k0 : s * α + t * v = 0 := by simpa using key 0
    have k1 : s * β - t * u = 0 := by simpa using key 1
    constructor
    · linear_combination -s * huv + u * k0 + v * k1
    · linear_combination -t * huv + β * k0 - α * k1
  have he0 : e' 0 = u • (1 : H) + β • x := by
    rw [h1, hxdef]
    linear_combination (norm := module) -huv • e' 0
  have he1 : e' 1 = v • (1 : H) - α • x := by
    rw [h1, hxdef]
    linear_combination (norm := module) -huv • e' 1
  have hsp : ⊤ ≤ Submodule.span R (Set.range ![(1 : H), x]) := by
    rw [← e'.span_eq, Submodule.span_le]
    have h1mem : (1 : H) ∈ Submodule.span R (Set.range ![(1 : H), x]) :=
      Submodule.subset_span ⟨0, rfl⟩
    have hxmem : x ∈ Submodule.span R (Set.range ![(1 : H), x]) :=
      Submodule.subset_span ⟨1, rfl⟩
    have hall : ∀ i : Fin 2, e' i ∈ Submodule.span R (Set.range ![(1 : H), x]) := by
      rw [Fin.forall_fin_two, he0, he1]
      exact ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ h1mem) (Submodule.smul_mem _ _ hxmem),
        Submodule.sub_mem _ (Submodule.smul_mem _ _ h1mem) (Submodule.smul_mem _ _ hxmem)⟩
    rintro _ ⟨i, rfl⟩
    exact hall i
  refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩
  · simp [Module.Basis.mk_apply]
  · simpa [Module.Basis.mk_apply] using hx

/-- In a commutative Hopf algebra free of rank two over a commutative ring,
there is a basis `1, x` and scalars `a, b` with `a * b = 2`, counit of `x`
equal to zero, `x * x = a • x`, comultiplication of `x` as displayed, and
antipode of `x` equal to `x`. -/
public theorem HopfAlgebra.exists_basis_tateOort_two {R : Type u} [CommRing R] {H : Type v}
    [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) :
    ∃ (e : Module.Basis (Fin 2) R H) (a b : R),
      e 0 = 1 ∧ a * b = 2 ∧ Coalgebra.counit (R := R) (e 1) = 0 ∧ e 1 * e 1 = a • e 1 ∧
      Coalgebra.comul (R := R) (e 1) = e 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] e 1 - b • (e 1 ⊗ₜ[R] e 1) ∧
      HopfAlgebra.antipode R (e 1) = e 1 := by
  obtain ⟨e, he0, hε⟩ := exists_basis_one_counit_zero (R := R) (H := H) hrank
  set x := e 1 with hxdef
  have hrepr : ∀ h : H, h = e.repr h 0 • (1 : H) + e.repr h 1 • x := fun h => by
    conv_lhs => rw [← e.sum_repr h]
    rw [Fin.sum_univ_two, he0]
  have hr1 : e.repr 1 = Finsupp.single 0 1 := by rw [← he0, e.repr_self]
  have hrx : e.repr x = Finsupp.single 1 1 := by rw [hxdef, e.repr_self]
  set a := e.repr (x * x) 1 with hadef
  have hxx : x * x = a • x := by
    have h := hrepr (x * x)
    have hc : e.repr (x * x) 0 = 0 := by
      have := congr(counit (R := R) $h)
      rw [Bialgebra.counit_mul, map_add, map_smul, map_smul, Bialgebra.counit_one, hε, smul_eq_mul,
        smul_eq_mul, mul_zero, mul_one, mul_zero, add_zero] at this
      exact this.symm
    rw [hc, zero_smul, zero_add] at h
    exact h
  let e2 := e.tensorProduct e
  set c : Fin 2 × Fin 2 → R := fun ij => e2.repr (comul (R := R) x) ij with hcdef
  have hcomul : comul (R := R) x
      = c (0, 0) • ((1 : H) ⊗ₜ[R] (1 : H)) + c (0, 1) • ((1 : H) ⊗ₜ[R] x)
        + c (1, 0) • (x ⊗ₜ[R] (1 : H)) + c (1, 1) • (x ⊗ₜ[R] x) := by
    conv_lhs => rw [← e2.sum_repr (comul (R := R) x)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, e2, Module.Basis.tensorProduct_apply, he0, ← hxdef, hcdef]
    abel
  have hA := Coalgebra.rTensor_counit_comul (R := R) x
  rw [hcomul] at hA
  simp only [map_add, map_smul, LinearMap.rTensor_tmul, Bialgebra.counit_one, hε] at hA
  have hA' := congr(TensorProduct.lid R H $hA)
  simp only [map_add, map_smul, TensorProduct.lid_tmul, one_smul, zero_smul, smul_zero,
    add_zero] at hA'
  have hB := Coalgebra.lTensor_counit_comul (R := R) x
  rw [hcomul] at hB
  simp only [map_add, map_smul, LinearMap.lTensor_tmul, Bialgebra.counit_one, hε] at hB
  have hB' := congr(TensorProduct.rid R H $hB)
  simp only [map_add, map_smul, TensorProduct.rid_tmul, one_smul, zero_smul, smul_zero,
    add_zero] at hB'
  have c00 : c (0, 0) = 0 := by
    have := congr(e.repr $hA' 0)
    simpa [hr1, hrx] using this
  have c01 : c (0, 1) = 1 := by
    have := congr(e.repr $hA' 1)
    simpa [hr1, hrx] using this
  have c10 : c (1, 0) = 1 := by
    have := congr(e.repr $hB' 1)
    simpa [hr1, hrx, c00] using this
  set d := c (1, 1) with hddef
  have hΔ : comul (R := R) x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x + d • (x ⊗ₜ[R] x) := by
    rw [hcomul, c00, c01, c10, zero_smul, zero_add, one_smul, one_smul]
    abel
  have hsq : (x ⊗ₜ[R] (1 : H) + (1 : H) ⊗ₜ[R] x + d • (x ⊗ₜ[R] x))
        * (x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x + d • (x ⊗ₜ[R] x))
      = a • (x ⊗ₜ[R] (1 : H)) + a • ((1 : H) ⊗ₜ[R] x)
        + (a * a * d * d + 4 * a * d + 2) • (x ⊗ₜ[R] x) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, hxx, TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
    module
  have hrel : a * a * d * d + 3 * a * d + 2 = 0 := by
    have hm := Bialgebra.comul_mul (R := R) x x
    rw [hxx, map_smul, hΔ, hsq] at hm
    have := congr(e2.repr $hm (1, 1))
    simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      e2, Module.Basis.tensorProduct_repr_tmul_apply, hr1, hrx, smul_eq_mul] at this
    simp at this
    linear_combination -this
  set s := e.repr (HopfAlgebra.antipode R x) 1 with hsdef
  set t := e.repr (HopfAlgebra.antipode R x) 0 with htdef
  have hS : HopfAlgebra.antipode R x = t • (1 : H) + s • x := hrepr _
  have hax := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) x
  rw [hΔ, hε, map_zero] at hax
  simp only [map_add, map_smul, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
    HopfAlgebra.antipode_one, one_mul, mul_one] at hax
  rw [hS] at hax
  have hax' : t • (1 : H) + (s + 1 + d * t + d * s * a) • x = 0 := by
    rw [← hax]
    simp only [add_mul, smul_mul_assoc, one_mul, hxx, smul_smul]
    module
  have ht : t = 0 := by
    have := congr(e.repr $hax' 0)
    simpa [hr1, hrx] using this
  have hs : s * (1 + a * d) = -1 := by
    have := congr(e.repr $hax' 1)
    simp [hrx, ht] at this
    linear_combination this
  have had : a * d = -2 := by
    linear_combination (a * d + 2) * hs - s * hrel
  have hs1 : s = 1 := by
    linear_combination -hs + s * had
  refine ⟨e, a, -d, he0, ?_, hε, hxx, ?_, ?_⟩
  · linear_combination -had
  · rw [← hxdef, hΔ, neg_smul, sub_neg_eq_add]
  · rw [← hxdef, hS, ht, hs1, zero_smul, zero_add, one_smul]
