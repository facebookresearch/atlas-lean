/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_HopfAlgebra_HopfOrderData.lean`
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

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Hopf orders: Hopf algebra structure on an integral subalgebra

Let `R` be a domain with fraction field `K` and `A` a commutative Hopf algebra over `K` that is
also an `R`-algebra. A flat `R`-subalgebra `S` of `A` whose comultiplication lands in the image
of `S ⊗[R] S`, whose counit takes values in `R` and which is stable under the antipode
inherits an `R`-Hopf algebra structure (`HopfOrder.hopfAlgebra`). Bialgebra maps and
inclusions between such subalgebras give bialgebra maps (`HopfOrder.mapBialgHom`,
`HopfOrder.inclusion`). When `R` is a principal ideal domain, every `R`-subalgebra of a
`K`-algebra that is finite over `R` is free, hence flat, over `R`.
-/

@[expose] public section

universe u v w w'

open scoped TensorProduct

namespace HopfOrder

section Comparison

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
variable (S : Subalgebra R A)

/-- **Square of the inclusion of a subalgebra.** Let `R` be a commutative ring, `K` a field with
an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible `R`-algebra structure,
and `S` an `R`-subalgebra of `A`. This is the `R`-algebra map `S ⊗[R] S → A ⊗[K] A` sending
`s ⊗ t` to `s ⊗ t`, induced by the inclusion of `S` into `A`. -/
noncomputable def tensorSqHom : (↥S ⊗[R] ↥S) →ₐ[R] (A ⊗[K] A) :=
  Algebra.TensorProduct.productMap
    (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
    (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)

@[simp]
lemma tensorSqHom_tmul (t t' : ↥S) :
    tensorSqHom S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp [tensorSqHom, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

variable {S} in
lemma tmul_mem_range_tensorSqHom {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    x ⊗ₜ[K] y ∈ (tensorSqHom (K := K) S).range :=
  ((tensorSqHom S).mem_range).mpr ⟨(⟨x, hx⟩ : ↥S) ⊗ₜ[R] (⟨y, hy⟩ : ↥S), by rw [tensorSqHom_tmul]⟩


/-- **Base change of a subalgebra to the field.** Let `R` be a commutative ring, `K` a field with
an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible `R`-algebra structure,
and `S` an `R`-subalgebra of `A`. This is the `K`-algebra map `K ⊗[R] S → A` sending `k ⊗ s` to
`k • s`. -/
private noncomputable def baseChangeHom : (K ⊗[R] ↥S) →ₐ[K] A :=
  AlgHom.liftEquiv R K (↥S) A S.val

private lemma baseChangeHom_tmul (k : K) (t : ↥S) : baseChangeHom S (k ⊗ₜ[R] t) = k • (t : A) := rfl

private lemma baseChangeHom_one_tmul (t : ↥S) : baseChangeHom S ((1 : K) ⊗ₜ[R] t) = (t : A) := by
  rw [baseChangeHom_tmul, one_smul]

/-- **Base-changed comparison map for `S ⊗[R] S`.** Let `R` be a commutative ring, `K` a field
with an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible `R`-algebra
structure, and `S` an `R`-subalgebra of `A`. This is the `K`-linear map
`K ⊗[R] (S ⊗[R] S) → A ⊗[K] A` sending `k ⊗ (s ⊗ t)` to `k • (s ⊗ t)`. -/
private noncomputable def doubleEval : (K ⊗[R] (↥S ⊗[R] ↥S)) →ₗ[K] (A ⊗[K] A) :=
  (TensorProduct.map (baseChangeHom S).toLinearMap (baseChangeHom S).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S ↥S).toLinearMap

/-- **Comparison of `S ⊗[R] S` with `A ⊗[K] A`.** Let `R` be a commutative ring, `K` a field with
an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible `R`-algebra structure,
and `S` an `R`-subalgebra of `A`. This is the map `S ⊗[R] S → A ⊗[K] A` sending `z` to the image
of `1 ⊗ z` under `HopfOrder.doubleEval S`; it sends `s ⊗ t` to `s ⊗ t`. -/
private noncomputable def doubleCmp (z : ↥S ⊗[R] ↥S) : A ⊗[K] A :=
  doubleEval S ((1 : K) ⊗ₜ[R] z)

private lemma doubleCmp_tmul (t t' : ↥S) :
    doubleCmp S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp only [doubleCmp, doubleEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply]
  rw [baseChangeHom_one_tmul, baseChangeHom_one_tmul]

private lemma doubleCmp_add (z w : ↥S ⊗[R] ↥S) :
    doubleCmp (K := K) S (z + w) = doubleCmp (K := K) S z + doubleCmp (K := K) S w := by
  change doubleEval S ((1 : K) ⊗ₜ[R] (z + w))
    = doubleEval S ((1 : K) ⊗ₜ[R] z) + doubleEval S ((1 : K) ⊗ₜ[R] w)
  rw [TensorProduct.tmul_add, map_add]

private theorem doubleCmp_eq_tensorSqHom (z : ↥S ⊗[R] ↥S) :
    doubleCmp (K := K) S z = tensorSqHom (K := K) S z := by
  induction z with
  | tmul t t' => rw [doubleCmp_tmul, tensorSqHom_tmul]
  | add z w hz hw => rw [doubleCmp_add, map_add, hz, hw]

/-- **Base-changed comparison map for `S ⊗[R] (S ⊗[R] S)`.** Let `R` be a commutative ring, `K`
a field with an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible
`R`-algebra structure, and `S` an `R`-subalgebra of `A`. This is the `K`-linear map
`K ⊗[R] (S ⊗[R] (S ⊗[R] S)) → A ⊗[K] (A ⊗[K] A)` sending `k ⊗ (s ⊗ (t ⊗ u))` to
`k • (s ⊗ (t ⊗ u))`. -/
private noncomputable def tripleEval :
    (K ⊗[R] (↥S ⊗[R] (↥S ⊗[R] ↥S))) →ₗ[K] (A ⊗[K] (A ⊗[K] A)) :=
  (TensorProduct.map (baseChangeHom S).toLinearMap (doubleEval S)).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S (↥S ⊗[R] ↥S)).toLinearMap

/-- **Comparison of `S ⊗[R] (S ⊗[R] S)` with `A ⊗[K] (A ⊗[K] A)`.** Let `R` be a commutative
ring, `K` a field with an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible
`R`-algebra structure, and `S` an `R`-subalgebra of `A`. This is the map sending `w` to the image
of `1 ⊗ w` under `HopfOrder.tripleEval S`; it sends `s ⊗ (t ⊗ u)` to `s ⊗ (t ⊗ u)`. -/
private noncomputable def tripleCmpR (w : ↥S ⊗[R] (↥S ⊗[R] ↥S)) : A ⊗[K] (A ⊗[K] A) :=
  tripleEval S ((1 : K) ⊗ₜ[R] w)

private lemma tripleCmpR_add (w w' : ↥S ⊗[R] (↥S ⊗[R] ↥S)) :
    tripleCmpR (K := K) S (w + w') = tripleCmpR (K := K) S w + tripleCmpR (K := K) S w' := by
  change tripleEval S ((1 : K) ⊗ₜ[R] (w + w'))
    = tripleEval S ((1 : K) ⊗ₜ[R] w) + tripleEval S ((1 : K) ⊗ₜ[R] w')
  rw [TensorProduct.tmul_add, map_add]

private lemma tripleCmpR_tmul (t : ↥S) (z : ↥S ⊗[R] ↥S) :
    tripleCmpR S (t ⊗ₜ[R] z) = (t : A) ⊗ₜ[K] doubleCmp S z := by
  simp only [tripleCmpR, tripleEval, doubleCmp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply]
  rw [baseChangeHom_one_tmul]

/-- **Base-changed comparison map for `(S ⊗[R] S) ⊗[R] S`.** Let `R` be a commutative ring, `K`
a field with an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible
`R`-algebra structure, and `S` an `R`-subalgebra of `A`. This is the `K`-linear map
`K ⊗[R] ((S ⊗[R] S) ⊗[R] S) → (A ⊗[K] A) ⊗[K] A` sending `k ⊗ ((s ⊗ t) ⊗ u)` to
`k • ((s ⊗ t) ⊗ u)`. -/
private noncomputable def tripleEvalL :
    (K ⊗[R] ((↥S ⊗[R] ↥S) ⊗[R] ↥S)) →ₗ[K] ((A ⊗[K] A) ⊗[K] A) :=
  (TensorProduct.map (doubleEval S) (baseChangeHom S).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K (↥S ⊗[R] ↥S) ↥S).toLinearMap

/-- **Comparison of `(S ⊗[R] S) ⊗[R] S` with `(A ⊗[K] A) ⊗[K] A`.** Let `R` be a commutative
ring, `K` a field with an `R`-algebra structure, `A` a commutative `K`-algebra with a compatible
`R`-algebra structure, and `S` an `R`-subalgebra of `A`. This is the map sending `w` to the image
of `1 ⊗ w` under `HopfOrder.tripleEvalL S`; it sends `(s ⊗ t) ⊗ u` to `(s ⊗ t) ⊗ u`. -/
private noncomputable def tripleCmpL (w : (↥S ⊗[R] ↥S) ⊗[R] ↥S) : (A ⊗[K] A) ⊗[K] A :=
  tripleEvalL S ((1 : K) ⊗ₜ[R] w)

private lemma tripleCmpL_add (w w' : (↥S ⊗[R] ↥S) ⊗[R] ↥S) :
    tripleCmpL (K := K) S (w + w') = tripleCmpL (K := K) S w + tripleCmpL (K := K) S w' := by
  change tripleEvalL S ((1 : K) ⊗ₜ[R] (w + w'))
    = tripleEvalL S ((1 : K) ⊗ₜ[R] w) + tripleEvalL S ((1 : K) ⊗ₜ[R] w')
  rw [TensorProduct.tmul_add, map_add]

private lemma tripleCmpL_tmul (z : ↥S ⊗[R] ↥S) (t : ↥S) :
    tripleCmpL S (z ⊗ₜ[R] t) = doubleCmp S z ⊗ₜ[K] (t : A) := by
  simp only [tripleCmpL, tripleEvalL, doubleCmp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply]
  rw [baseChangeHom_one_tmul]

private lemma tripleCmpR_assoc_tmul (z : ↥S ⊗[R] ↥S) (c : ↥S) :
    tripleCmpR S (TensorProduct.assoc R ↥S ↥S ↥S (z ⊗ₜ[R] c))
      = TensorProduct.assoc K A A A (tripleCmpL S (z ⊗ₜ[R] c)) := by
  induction z with
  | tmul a b =>
      rw [TensorProduct.assoc_tmul, tripleCmpR_tmul, doubleCmp_tmul, tripleCmpL_tmul,
        doubleCmp_tmul, TensorProduct.assoc_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [TensorProduct.add_tmul, map_add, tripleCmpR_add, h₁, h₂, tripleCmpL_add, map_add]

private lemma tripleCmpR_assoc (w : (↥S ⊗[R] ↥S) ⊗[R] ↥S) :
    tripleCmpR S (TensorProduct.assoc R ↥S ↥S ↥S w)
      = TensorProduct.assoc K A A A (tripleCmpL S w) := by
  induction w with
  | tmul z c => exact tripleCmpR_assoc_tmul S z c
  | add w₁ w₂ h₁ h₂ =>
      rw [map_add, tripleCmpR_add, h₁, h₂, tripleCmpL_add, map_add]

section Domain

variable [IsDomain R] [IsFractionRing R K]

omit S in
private theorem exists_nonzero_smul_eq_one_tmul {M : Type*} [AddCommGroup M] [Module R M]
    (x : K ⊗[R] M) :
    ∃ (r : R) (m : M), r ≠ 0 ∧ (algebraMap R K r) • x = (1 : K) ⊗ₜ[R] m := by
  induction x with
  | tmul f g =>
      obtain ⟨p, hs⟩ := IsLocalization.surj (nonZeroDivisors R) f
      refine ⟨p.2, p.1 • g, nonZeroDivisors.coe_ne_zero p.2, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, hs, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      obtain ⟨r₁, g₁, h₁, e₁⟩ := hx
      obtain ⟨r₂, g₂, h₂, e₂⟩ := hy
      refine ⟨r₁ * r₂, r₂ • g₁ + r₁ • g₂, mul_ne_zero h₁ h₂, ?_⟩
      have hx' : (algebraMap R K (r₁ * r₂)) • x = (1 : K) ⊗ₜ[R] (r₂ • g₁) := by
        rw [map_mul, mul_comm, mul_smul, e₁, TensorProduct.tmul_smul, algebraMap_smul]
      have hy' : (algebraMap R K (r₁ * r₂)) • y = (1 : K) ⊗ₜ[R] (r₁ • g₂) := by
        rw [map_mul, mul_smul, e₂, TensorProduct.tmul_smul, algebraMap_smul]
      rw [smul_add, hx', hy', ← TensorProduct.tmul_add]

omit S [IsDomain R] in
private theorem one_tmul_injective {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (fun m : M => (1 : K) ⊗ₜ[R] m) := by
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hfact : (fun m : M => (1 : K) ⊗ₜ[R] m) =
      (LinearMap.rTensor M (Algebra.linearMap R K)) ∘ (TensorProduct.lid R M).symm := by
    ext m; simp [TensorProduct.lid_symm_apply, Algebra.linearMap_apply]
  rw [hfact]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ hRK).comp
    (TensorProduct.lid R M).symm.injective

private theorem baseChangeHom_injective : Function.Injective (baseChangeHom (K := K) S) := by
  have key : ∀ z : K ⊗[R] ↥S, baseChangeHom S z = 0 → z = 0 := by
    intro z hz
    obtain ⟨r, h, hr, e⟩ := exists_nonzero_smul_eq_one_tmul (R := R) (K := K) z
    have hru : (algebraMap R K r) ≠ 0 := fun hc =>
      hr (IsFractionRing.injective R K (by rw [hc, map_zero]))
    have h1 : baseChangeHom S ((algebraMap R K r) • z) = 0 := by
      rw [map_smul, hz, smul_zero]
    rw [e, baseChangeHom_one_tmul] at h1
    have h2 : h = 0 := Subtype.ext h1
    rw [h2, TensorProduct.tmul_zero] at e
    have h3 := congrArg (fun w => (algebraMap R K r)⁻¹ • w) e
    simpa only [smul_smul, inv_mul_cancel₀ hru, one_smul, smul_zero] using h3
  intro x y hxy
  have hsub : baseChangeHom S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

private theorem doubleEval_injective : Function.Injective (doubleEval (K := K) S) := by
  have : Module.Free K (K ⊗[R] ↥S) := Module.Free.of_divisionRing K _
  have : Module.Flat K (K ⊗[R] ↥S) := Module.Flat.of_free
  have : Module.Free K A := Module.Free.of_divisionRing K _
  have : Module.Flat K A := Module.Flat.of_free
  have hψ : Function.Injective (baseChangeHom (K := K) S).toLinearMap :=
    baseChangeHom_injective S
  have hmap : Function.Injective
      (TensorProduct.map (baseChangeHom (K := K) S).toLinearMap
        (baseChangeHom (K := K) S).toLinearMap) := by
    rw [← LinearMap.rTensor_comp_lTensor]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hψ).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hψ)
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S ↥S).injective
  apply hmap
  simpa only [doubleEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap] using hxy

private theorem doubleCmp_injective [Module.Flat R ↥S] :
    Function.Injective (doubleCmp (K := K) S) := by
  intro x y hxy
  have h1 : Function.Injective (fun z : ↥S ⊗[R] ↥S => (1 : K) ⊗ₜ[R] z) :=
    one_tmul_injective
  exact h1 (doubleEval_injective S hxy)

private theorem tensorSqHom_injective [Module.Flat R ↥S] :
    Function.Injective (tensorSqHom (K := K) S) := by
  intro x y h
  apply doubleCmp_injective (K := K) S
  rw [doubleCmp_eq_tensorSqHom, doubleCmp_eq_tensorSqHom, h]

private theorem tripleEval_injective : Function.Injective (tripleEval (K := K) S) := by
  have : Module.Free K (K ⊗[R] ↥S) := Module.Free.of_divisionRing K _
  have : Module.Flat K (K ⊗[R] ↥S) := Module.Flat.of_free
  have : Module.Free K (A ⊗[K] A) := Module.Free.of_divisionRing K _
  have : Module.Flat K (A ⊗[K] A) := Module.Flat.of_free
  have hψ : Function.Injective (baseChangeHom (K := K) S).toLinearMap :=
    baseChangeHom_injective S
  have hd : Function.Injective (doubleEval (K := K) S) := doubleEval_injective S
  have hmap : Function.Injective
      (TensorProduct.map (baseChangeHom (K := K) S).toLinearMap (doubleEval (K := K) S)) := by
    rw [← LinearMap.rTensor_comp_lTensor]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hψ).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hd)
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S (↥S ⊗[R] ↥S)).injective
  apply hmap
  simpa only [tripleEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap] using hxy

private theorem tripleCmpR_injective [Module.Flat R ↥S] :
    Function.Injective (tripleCmpR (K := K) S) := by
  intro x y hxy
  have h1 : Function.Injective
      (fun w : ↥S ⊗[R] (↥S ⊗[R] ↥S) => (1 : K) ⊗ₜ[R] w) :=
    one_tmul_injective
  exact h1 (tripleEval_injective S hxy)

end Domain

end Comparison

section Descent

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable {S : Subalgebra R A}

/-- **Restricted antipode.** Let `R` be a commutative ring, `K` a field with an `R`-algebra
structure, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and
`S` an `R`-subalgebra of `A` that is stable under the antipode of `A`. This is the `R`-linear map
`S → S` given by the antipode of `A`. -/
noncomputable def antipodeS
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    ↥S →ₗ[R] ↥S where
  toFun t := ⟨HopfAlgebra.antipode K (t : A), hantipode (t : A) t.2⟩
  map_add' t t' := by
    apply Subtype.ext
    change HopfAlgebra.antipode K (((t + t') : ↥S) : A)
      = HopfAlgebra.antipode K (t : A) + HopfAlgebra.antipode K (t' : A)
    rw [Subalgebra.coe_add, map_add]
  map_smul' r t := by
    apply Subtype.ext
    change HopfAlgebra.antipode K (r • (t : A)) = r • HopfAlgebra.antipode K (t : A)
    rw [← algebraMap_smul K r (t : A), map_smul, algebraMap_smul]

private theorem coe_antipodeS (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (t : ↥S) :
    ((antipodeS hantipode t : ↥S) : A) = HopfAlgebra.antipode K (t : A) := rfl

/-- **The comultiplication of an order comes from `S ⊗[R] S`.** Let `R` be a commutative ring,
`K` a field with an `R`-algebra structure, `A` a commutative Hopf algebra over `K` with a
compatible `R`-algebra structure, and `S` an `R`-subalgebra of `A` whose comultiplication lands in
the image of `S ⊗[R] S` in `A ⊗[K] A`. For every `t : S` there is `z : S ⊗[R] S` whose image
`HopfOrder.tensorSqHom S z` is the comultiplication of `t` in `A ⊗[K] A`. -/
lemma exists_tensorSqHom_eq_comul
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (t : ↥S) :
    ∃ z : ↥S ⊗[R] ↥S, tensorSqHom S z = Coalgebra.comul (R := K) (t : A) :=
  (tensorSqHom S).mem_range.mp (hcomul (t : A) t.2)

omit [IsScalarTower R K A] in
/-- **The counit of an order comes from `R`.** Let `R` be a commutative ring, `K` a field with an
`R`-algebra structure, `A` a commutative Hopf algebra over `K` that is also an `R`-algebra, and
`S` an `R`-subalgebra of `A` whose counit takes values in the image of `R` in `K`. For every
`t : S` there is `r : R` whose image in `K` is the counit of `t`. -/
lemma exists_algebraMap_eq_counit
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (t : ↥S) :
    ∃ r : R, algebraMap R K r = Coalgebra.counit (R := K) (t : A) :=
  RingHom.mem_range.mp (hcounit (t : A) t.2)

variable [IsFractionRing R K]

/-- **Restricted counit.** Let `R` be a commutative ring with fraction field `K`, `A` a commutative
Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an `R`-subalgebra of `A`
whose counit takes values in the image of `R`. This is the `R`-linear map `S → R` sending `t` to
the element of `R` whose image in `K` is the counit of `t`. -/
noncomputable def counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    ↥S →ₗ[R] R where
  toFun t := (exists_algebraMap_eq_counit hcounit t).choose
  map_add' t t' := by
    apply IsFractionRing.injective R K
    rw [map_add, (exists_algebraMap_eq_counit hcounit (t + t')).choose_spec,
      (exists_algebraMap_eq_counit hcounit t).choose_spec,
      (exists_algebraMap_eq_counit hcounit t').choose_spec]
    rw [Subalgebra.coe_add, map_add]
  map_smul' r t := by
    apply IsFractionRing.injective R K
    rw [RingHom.id_apply, (exists_algebraMap_eq_counit hcounit (r • t)).choose_spec,
      smul_eq_mul, map_mul, (exists_algebraMap_eq_counit hcounit t).choose_spec,
      Subalgebra.coe_smul, ← algebraMap_smul K r (t : A), map_smul, smul_eq_mul]

private theorem algebraMap_counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (t : ↥S) :
    algebraMap R K (counitS hcounit t) = Coalgebra.counit (R := K) (t : A) :=
  (exists_algebraMap_eq_counit hcounit t).choose_spec

variable [IsDomain R] [Module.Flat R ↥S]

/-- **Restricted comultiplication.** Let `R` be a domain with fraction field `K`, `A` a commutative
Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an `R`-subalgebra of `A`
that is flat over `R` and whose comultiplication lands in the image of `S ⊗[R] S` in
`A ⊗[K] A`. This is the `R`-linear map `S → S ⊗[R] S` lifting the comultiplication of `A` along
`HopfOrder.tensorSqHom S`; by flatness `HopfOrder.tensorSqHom S` is injective, so the lift is
unique. -/
noncomputable def comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range) :
    ↥S →ₗ[R] ↥S ⊗[R] ↥S where
  toFun t := (exists_tensorSqHom_eq_comul hcomul t).choose
  map_add' t t' := by
    apply tensorSqHom_injective (K := K) S
    rw [map_add, (exists_tensorSqHom_eq_comul hcomul (t + t')).choose_spec,
      (exists_tensorSqHom_eq_comul hcomul t).choose_spec,
      (exists_tensorSqHom_eq_comul hcomul t').choose_spec]
    rw [Subalgebra.coe_add, map_add]
  map_smul' r t := by
    apply tensorSqHom_injective (K := K) S
    rw [RingHom.id_apply, map_smul,
      (exists_tensorSqHom_eq_comul hcomul (r • t)).choose_spec,
      (exists_tensorSqHom_eq_comul hcomul t).choose_spec]
    rw [Subalgebra.coe_smul, ← algebraMap_smul K r (t : A), map_smul, algebraMap_smul]

private theorem tensorSqHom_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (t : ↥S) :
    tensorSqHom S (comulS hcomul t) = Coalgebra.comul (R := K) (t : A) :=
  (exists_tensorSqHom_eq_comul hcomul t).choose_spec

private lemma doubleCmp_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (t : ↥S) :
    doubleCmp S (comulS hcomul t) = Coalgebra.comul (R := K) (t : A) := by
  rw [doubleCmp_eq_tensorSqHom, tensorSqHom_comulS]

omit [IsDomain R] [Module.Flat R ↥S] in
private lemma val_lid_rTensor_counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (z : ↥S ⊗[R] ↥S) :
    ((TensorProduct.lid R ↥S ((counitS hcounit).rTensor ↥S z) : ↥S) : A)
      = TensorProduct.lid K A
          ((Coalgebra.counit (R := K) (A := A)).rTensor A (doubleCmp S z)) := by
  induction z with
  | tmul a b =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, doubleCmp_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Subalgebra.coe_smul,
        ← algebraMap_counitS hcounit a, algebraMap_smul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

omit [IsDomain R] [Module.Flat R ↥S] in
private lemma val_rid_lTensor_counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (z : ↥S ⊗[R] ↥S) :
    ((TensorProduct.rid R ↥S ((counitS hcounit).lTensor ↥S z) : ↥S) : A)
      = TensorProduct.rid K A
          ((Coalgebra.counit (R := K) (A := A)).lTensor A (doubleCmp S z)) := by
  induction z with
  | tmul a b =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, doubleCmp_tmul,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Subalgebra.coe_smul,
        ← algebraMap_counitS hcounit b, algebraMap_smul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

omit [IsDomain R] [Module.Flat R ↥S] in
/-- **The restricted counit preserves `1`.** Let `R` be a commutative ring with fraction field
`K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` whose counit takes values in the image of `R`. Then the restricted counit
`HopfOrder.counitS` sends `1` to `1`. -/
theorem counitS_one (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    counitS hcounit (1 : ↥S) = 1 := by
  apply IsFractionRing.injective R K
  rw [algebraMap_counitS, OneMemClass.coe_one, Bialgebra.counit_one, map_one]

omit [IsDomain R] [Module.Flat R ↥S] in
/-- **The restricted counit is multiplicative.** Let `R` be a commutative ring with fraction
field `K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and
`S` an `R`-subalgebra of `A` whose counit takes values in the image of `R`. Then the restricted
counit `HopfOrder.counitS` is multiplicative. -/
theorem counitS_mul (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (a b : ↥S) :
    counitS hcounit (a * b) = counitS hcounit a * counitS hcounit b := by
  apply IsFractionRing.injective R K
  rw [algebraMap_counitS hcounit (a * b), map_mul, algebraMap_counitS hcounit a,
    algebraMap_counitS hcounit b, MulMemClass.coe_mul, Bialgebra.counit_mul]

omit [IsFractionRing R K] [IsDomain R] [Module.Flat R ↥S] in
private lemma val_mul'_rTensor_antipodeS (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S)
    (z : ↥S ⊗[R] ↥S) :
    ((LinearMap.mul' R ↥S ((antipodeS hantipode).rTensor ↥S z) : ↥S) : A)
      = LinearMap.mul' K A ((HopfAlgebra.antipode K (A := A)).rTensor A (doubleCmp S z)) := by
  induction z with
  | tmul a b =>
      rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, MulMemClass.coe_mul,
        coe_antipodeS, doubleCmp_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

omit [IsFractionRing R K] [IsDomain R] [Module.Flat R ↥S] in
private lemma val_mul'_lTensor_antipodeS (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S)
    (z : ↥S ⊗[R] ↥S) :
    ((LinearMap.mul' R ↥S ((antipodeS hantipode).lTensor ↥S z) : ↥S) : A)
      = LinearMap.mul' K A ((HopfAlgebra.antipode K (A := A)).lTensor A (doubleCmp S z)) := by
  induction z with
  | tmul a b =>
      rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply, MulMemClass.coe_mul,
        coe_antipodeS, doubleCmp_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

private lemma tripleCmpL_rTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (z : ↥S ⊗[R] ↥S) :
    tripleCmpL S ((comulS hcomul).rTensor ↥S z)
      = (Coalgebra.comul (R := K) (A := A)).rTensor A (doubleCmp S z) := by
  induction z with
  | tmul a b =>
      rw [LinearMap.rTensor_tmul, tripleCmpL_tmul, doubleCmp_comulS, doubleCmp_tmul,
        LinearMap.rTensor_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, tripleCmpL_add, h₁, h₂, doubleCmp_add, map_add]

private lemma tripleCmpR_lTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (z : ↥S ⊗[R] ↥S) :
    tripleCmpR S ((comulS hcomul).lTensor ↥S z)
      = (Coalgebra.comul (R := K) (A := A)).lTensor A (doubleCmp S z) := by
  induction z with
  | tmul a b =>
      rw [LinearMap.lTensor_tmul, tripleCmpR_tmul, doubleCmp_comulS, doubleCmp_tmul,
        LinearMap.lTensor_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, tripleCmpR_add, h₁, h₂, doubleCmp_add, map_add]

/-- **The restricted comultiplication is coassociative.** Let `R` be a domain with fraction field
`K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R` and whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A`. Then the restricted comultiplication `Δ = HopfOrder.comulS` satisfies
`assoc ∘ (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. -/
theorem comulS_coassoc
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range) :
    ↑(TensorProduct.assoc R ↥S ↥S ↥S) ∘ₗ
        (comulS hcomul).rTensor ↥S ∘ₗ comulS hcomul
      = (comulS hcomul).lTensor ↥S ∘ₗ comulS hcomul := by
  apply LinearMap.ext
  intro t
  apply tripleCmpR_injective (K := K) S
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tripleCmpR_assoc, tripleCmpL_rTensor_comulS, doubleCmp_comulS,
    Coalgebra.coassoc_apply, ← doubleCmp_comulS hcomul t, ← tripleCmpR_lTensor_comulS]

/-- **Left counit law for the restricted structure.** Let `R` be a domain with fraction field `K`,
`A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A` and whose counit takes values in the image of `R`. Then the restricted
comultiplication `Δ` and counit `ε` satisfy `(ε ⊗ id) (Δ s) = 1 ⊗ s` for all `s : S`. -/
theorem counitS_rTensor_comp_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    (counitS hcounit).rTensor ↥S ∘ₗ comulS hcomul = TensorProduct.mk R R ↥S 1 := by
  apply LinearMap.ext
  intro t
  have hinj : ∀ a b : R ⊗[R] ↥S,
      ((TensorProduct.lid R ↥S a : ↥S) : A) = ((TensorProduct.lid R ↥S b : ↥S) : A) → a = b :=
    fun a b hab => (TensorProduct.lid R ↥S).injective (Subtype.val_injective hab)
  apply hinj
  simp only [LinearMap.comp_apply]
  rw [val_lid_rTensor_counitS hcounit (comulS hcomul t), doubleCmp_comulS,
    Coalgebra.rTensor_counit_comul, TensorProduct.mk_apply, TensorProduct.lid_tmul,
    TensorProduct.lid_tmul, one_smul, one_smul]

/-- **Right counit law for the restricted structure.** Let `R` be a domain with fraction field
`K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A` and whose counit takes values in the image of `R`. Then the restricted
comultiplication `Δ` and counit `ε` satisfy `(id ⊗ ε) (Δ s) = s ⊗ 1` for all `s : S`. -/
theorem counitS_lTensor_comp_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    (counitS hcounit).lTensor ↥S ∘ₗ comulS hcomul = (TensorProduct.mk R ↥S R).flip 1 := by
  apply LinearMap.ext
  intro t
  have hinj : ∀ a b : ↥S ⊗[R] R,
      ((TensorProduct.rid R ↥S a : ↥S) : A) = ((TensorProduct.rid R ↥S b : ↥S) : A) → a = b :=
    fun a b hab => (TensorProduct.rid R ↥S).injective (Subtype.val_injective hab)
  apply hinj
  simp only [LinearMap.comp_apply, LinearMap.flip_apply]
  rw [val_rid_lTensor_counitS hcounit (comulS hcomul t), doubleCmp_comulS,
    Coalgebra.lTensor_counit_comul, TensorProduct.mk_apply, TensorProduct.rid_tmul,
    TensorProduct.rid_tmul, one_smul, one_smul]

variable (S) in
/-- **Coalgebra structure on a flat order.** Let `R` be a domain with fraction field `K`, `A` a
commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A` and whose counit takes values in the image of `R`. This is the
`R`-coalgebra structure on `S` whose comultiplication and counit are the restrictions of those
of `A`. -/
@[reducible]
noncomputable def coalgebra
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Coalgebra R ↥S where
  comul := comulS hcomul
  counit := counitS hcounit
  coassoc := comulS_coassoc hcomul
  rTensor_counit_comp_comul := counitS_rTensor_comp_comulS hcomul hcounit
  lTensor_counit_comp_comul := counitS_lTensor_comp_comulS hcomul hcounit

/-- **The restricted comultiplication preserves `1`.** Let `R` be a domain with fraction field
`K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R` and whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A`. Then `HopfOrder.comulS` sends `1` to `1 ⊗ 1`. -/
theorem comulS_one
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range) :
    comulS hcomul (1 : ↥S) = 1 := by
  apply tensorSqHom_injective (K := K) S
  rw [tensorSqHom_comulS, OneMemClass.coe_one, Bialgebra.comul_one, map_one]

/-- **The restricted comultiplication is multiplicative.** Let `R` be a domain with fraction
field `K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and
`S` an `R`-subalgebra of `A` that is flat over `R` and whose comultiplication lands in the image
of `S ⊗[R] S` in `A ⊗[K] A`. Then `HopfOrder.comulS` is multiplicative. -/
theorem comulS_mul
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range) (a b : ↥S) :
    comulS hcomul (a * b) = comulS hcomul a * comulS hcomul b := by
  apply tensorSqHom_injective (K := K) S
  rw [tensorSqHom_comulS hcomul (a * b), MulMemClass.coe_mul, Bialgebra.comul_mul,
    map_mul, tensorSqHom_comulS, tensorSqHom_comulS]

variable (S) in
/-- **Bialgebra structure on a flat order.** Let `R` be a domain with fraction field `K`, `A` a
commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A` and whose counit takes values in the image of `R`. This is the
`R`-bialgebra structure on `S` whose comultiplication and counit are the restrictions of those
of `A`. -/
@[reducible]
noncomputable def bialgebra
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Bialgebra R ↥S :=
  letI : Coalgebra R ↥S := HopfOrder.coalgebra S hcomul hcounit
  Bialgebra.mk' R ↥S (counitS_one hcounit) (fun {a b} => counitS_mul hcounit a b)
    (comulS_one hcomul) (fun {a b} => comulS_mul hcomul a b)

/-- **Left antipode law for the restricted structure.** Let `R` be a domain with fraction field
`K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A`, whose counit takes values in the image of `R`, and which is stable
under the antipode. Then the restricted maps satisfy `m ∘ (antipode ⊗ id) ∘ Δ = η ∘ ε`, where
`m` is the multiplication of `S` and `η : R → S` its unit. -/
theorem mul_antipodeS_rTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    LinearMap.mul' R ↥S ∘ₗ (antipodeS hantipode).rTensor ↥S ∘ₗ comulS hcomul
      = (Algebra.linearMap R ↥S) ∘ₗ counitS hcounit := by
  apply LinearMap.ext
  intro t
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [val_mul'_rTensor_antipodeS hantipode (comulS hcomul t), doubleCmp_comulS,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, ← algebraMap_counitS hcounit t,
    ← IsScalarTower.algebraMap_apply R K A]
  rfl

/-- **Right antipode law for the restricted structure.** Let `R` be a domain with fraction field
`K`, `A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A`, whose counit takes values in the image of `R`, and which is stable
under the antipode. Then the restricted maps satisfy `m ∘ (id ⊗ antipode) ∘ Δ = η ∘ ε`, where
`m` is the multiplication of `S` and `η : R → S` its unit. -/
theorem mul_antipodeS_lTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    LinearMap.mul' R ↥S ∘ₗ (antipodeS hantipode).lTensor ↥S ∘ₗ comulS hcomul
      = (Algebra.linearMap R ↥S) ∘ₗ counitS hcounit := by
  apply LinearMap.ext
  intro t
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [val_mul'_lTensor_antipodeS hantipode (comulS hcomul t), doubleCmp_comulS,
    HopfAlgebra.mul_antipode_lTensor_comul_apply, ← algebraMap_counitS hcounit t,
    ← IsScalarTower.algebraMap_apply R K A]
  rfl

variable (S) in
/-- **Hopf algebra structure on a flat Hopf order.** Let `R` be a domain with fraction field `K`,
`A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A`, whose counit takes values in the image of `R`, and which is stable
under the antipode. This is the `R`-Hopf algebra structure on `S` whose comultiplication, counit
and antipode are the restrictions of those of `A`. -/
@[reducible]
noncomputable def hopfAlgebra
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    HopfAlgebra R ↥S :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  { antipode := antipodeS hantipode
    mul_antipode_rTensor_comul := mul_antipodeS_rTensor_comulS hcomul hcounit hantipode
    mul_antipode_lTensor_comul := mul_antipodeS_lTensor_comulS hcomul hcounit hantipode }

/-- **Comultiplication of a Hopf order inside `A`.** Let `R` be a domain with fraction field `K`,
`A` a commutative Hopf algebra over `K` with a compatible `R`-algebra structure, and `S` an
`R`-subalgebra of `A` that is flat over `R`, whose comultiplication lands in the image of
`S ⊗[R] S` in `A ⊗[K] A`, whose counit takes values in the image of `R`, and which is stable
under the antipode. For `h : S`, the comultiplication of `h` in `A` is the image of its
comultiplication for `HopfOrder.hopfAlgebra` under the map `S ⊗[R] S → A ⊗[K] A`. -/
theorem val_comul
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (h : ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    Coalgebra.comul (R := K) (S.val h) =
      Algebra.TensorProduct.productMap
        (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
        (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
        (Coalgebra.comul (R := R) h) :=
  (tensorSqHom_comulS hcomul h).symm

end Descent

section Functorial

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable {B : Type w'} [CommRing B] [HopfAlgebra K B] [Algebra R B] [IsScalarTower R K B]
variable [IsDomain R] [IsFractionRing R K]

omit [IsDomain R] [IsFractionRing R K] in
private lemma map_tensorSqHom {S : Subalgebra R A} {T : Subalgebra R B}
    (π : A →ₗ[K] B) (f : ↥S →ₐ[R] ↥T) (hf : ∀ s : ↥S, ((f s : ↥T) : B) = π (s : A))
    (z : ↥S ⊗[R] ↥S) :
    TensorProduct.map π π (tensorSqHom S z)
      = tensorSqHom T (Algebra.TensorProduct.map f f z) := by
  induction z with
  | tmul a b =>
      rw [tensorSqHom_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        tensorSqHom_tmul, hf, hf]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]

/-- **Restriction of a bialgebra map to flat orders.** Let `R` be a domain with fraction field
`K`, and `A`, `B` commutative Hopf algebras over `K` with compatible `R`-algebra structures. Let
`S` and `T` be `R`-subalgebras of `A` and `B` that are flat over `R`, whose comultiplications land
in the images of `S ⊗[R] S` and `T ⊗[R] T`, and whose counits take values in the image of `R`. A
`K`-bialgebra map `π : A → B` with `π x ∈ T` for all `x ∈ S` restricts to an `R`-bialgebra map
`S → T` for the structures `HopfOrder.bialgebra`. -/
noncomputable def mapBialgHom
    {S : Subalgebra R A} [Module.Flat R ↥S] {T : Subalgebra R B} [Module.Flat R ↥T]
    (π : A →ₐc[K] B) (hπ : ∀ x ∈ S, π x ∈ T)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ T, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp T.val)
          (((Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp
              T.val)).range)
    (hcounit' : ∀ x ∈ T, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    letI : Bialgebra R ↥T := HopfOrder.bialgebra T hcomul' hcounit'
    ↥S →ₐc[R] ↥T :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  letI : Bialgebra R ↥T := HopfOrder.bialgebra T hcomul' hcounit'
  let f : ↥S →ₐ[R] ↥T :=
    (((π : A →ₐ[K] B).restrictScalars R).comp S.val).codRestrict T (fun s => hπ (s : A) s.2)
  have hf : ∀ s : ↥S, ((f s : ↥T) : B) = (π : A →ₗ[K] B) (s : A) := fun _ => rfl
  BialgHom.ofAlgHom f
    (by
      apply AlgHom.ext
      intro s
      apply IsFractionRing.injective R K
      change algebraMap R K (counitS hcounit' (f s)) = algebraMap R K (counitS hcounit s)
      rw [algebraMap_counitS, algebraMap_counitS, hf]
      exact CoalgHomClass.counit_comp_apply π (s : A))
    (by
      apply AlgHom.ext
      intro s
      apply tensorSqHom_injective (K := K) T
      change tensorSqHom T (Algebra.TensorProduct.map f f (comulS hcomul s))
        = tensorSqHom T (comulS hcomul' (f s))
      rw [← map_tensorSqHom (π : A →ₗ[K] B) f hf, tensorSqHom_comulS, tensorSqHom_comulS, hf]
      exact CoalgHomClass.map_comp_comul_apply π (s : A))

/-- **Inclusion of nested flat orders.** Let `R` be a domain with fraction field `K` and `A` a
commutative Hopf algebra over `K` with a compatible `R`-algebra structure. Let `S ≤ S'` be
`R`-subalgebras of `A` that are flat over `R`, whose comultiplications land in the images of
`S ⊗[R] S` and `S' ⊗[R] S'`, and whose counits take values in the image of `R`. The inclusion
`S → S'` is an `R`-bialgebra map for the structures `HopfOrder.bialgebra`. -/
noncomputable def inclusion
    {S S' : Subalgebra R A} [Module.Flat R ↥S] [Module.Flat R ↥S'] (h : S ≤ S')
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S'.val)).range)
    (hcounit' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    letI : Bialgebra R ↥S' := HopfOrder.bialgebra S' hcomul' hcounit'
    ↥S →ₐc[R] ↥S' :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  letI : Bialgebra R ↥S' := HopfOrder.bialgebra S' hcomul' hcounit'
  have hf : ∀ s : ↥S, ((Subalgebra.inclusion h s : ↥S') : A) = (LinearMap.id : A →ₗ[K] A) (s : A) :=
    fun _ => rfl
  BialgHom.ofAlgHom (Subalgebra.inclusion h)
    (by
      apply AlgHom.ext
      intro s
      apply IsFractionRing.injective R K
      change algebraMap R K (counitS hcounit' (Subalgebra.inclusion h s))
        = algebraMap R K (counitS hcounit s)
      rw [algebraMap_counitS, algebraMap_counitS]
      rfl)
    (by
      apply AlgHom.ext
      intro s
      apply tensorSqHom_injective (K := K) S'
      change tensorSqHom S' (Algebra.TensorProduct.map (Subalgebra.inclusion h)
          (Subalgebra.inclusion h)
          (comulS hcomul s)) = tensorSqHom S' (comulS hcomul' (Subalgebra.inclusion h s))
      rw [← map_tensorSqHom (LinearMap.id : A →ₗ[K] A) (Subalgebra.inclusion h) hf,
        tensorSqHom_comulS, tensorSqHom_comulS, TensorProduct.map_id, LinearMap.id_apply]
      rfl)

end Functorial

section PID

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type w} [CommRing A]

/-- **Finite subalgebras over a principal ideal domain are free.** Let `R` be a principal ideal
domain with fraction field `K` and `A` a commutative `K`-algebra with a compatible `R`-algebra
structure. Every `R`-subalgebra of `A` that is finite as an `R`-module is free as an
`R`-module. -/
theorem moduleFree_of_finite [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S] : Module.Free R ↥S := by
  have : Module.IsTorsionFree R A := by
    refine Module.IsTorsionFree.mk fun r hr => ?_
    have hr0 : r ≠ 0 := hr.left.ne_zero
    have hK : algebraMap R K r ≠ 0 := fun h =>
      hr0 ((injective_iff_map_eq_zero (algebraMap R K)).mp (IsFractionRing.injective R K) r h)
    intro a b hab
    have hab' : algebraMap R K r • a = algebraMap R K r • b := by
      simpa [IsScalarTower.algebraMap_smul] using hab
    exact smul_right_injective A hK hab'
  have : Module.IsTorsionFree R ↥S :=
    Function.Injective.moduleIsTorsionFree (fun s : ↥S => (s : A)) Subtype.coe_injective
      (fun _ _ => rfl)
  exact Module.free_of_finite_type_torsion_free'

/-- **Finite subalgebras over a principal ideal domain are flat.** Let `R` be a principal ideal
domain with fraction field `K` and `A` a commutative `K`-algebra with a compatible `R`-algebra
structure. Every `R`-subalgebra of `A` that is finite as an `R`-module is flat as an
`R`-module. -/
theorem moduleFlat_of_finite [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S] : Module.Flat R ↥S := by
  have := moduleFree_of_finite (K := K) S
  exact Module.Flat.of_free

end PID

end HopfOrder
