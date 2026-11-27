/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean`
and
`P2M/Sol/S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean`
and
`Theorems/Thm_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.lean`
and
`P2M/Sol/S_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum.lean`
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
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer

@[expose] public section

set_option autoImplicit false

open TensorProduct Algebra.TensorProduct

namespace FaithfullyFlatDescentAux

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (φ : N ⊗[A] B ≃ₗ[A] B ⊗[A] N)

private noncomputable abbrev δ : N →ₗ[A] B ⊗[A] N :=
  (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N) ∘ₗ (TensorProduct.mk A N B).flip 1

private noncomputable abbrev ι : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1

private noncomputable abbrev Msub : Submodule A N := LinearMap.eqLocus (δ φ) ι

private theorem δ_apply (n : N) : δ φ n = φ (n ⊗ₜ 1) := rfl

private theorem ι_apply (n : N) : ι n = (1 : B) ⊗ₜ[A] n := rfl

private theorem mem_Msub {n : N} : n ∈ Msub φ ↔ φ (n ⊗ₜ 1) = 1 ⊗ₜ n := Iff.rfl

private theorem δ_smul_of_mem (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    {m : N} (hm : m ∈ Msub φ) (b : B) : δ φ (b • m) = b ⊗ₜ m := by
  rw [δ_apply, show (b • m) ⊗ₜ[A] (1 : B) = b • (m ⊗ₜ[A] (1 : B)) from
    (TensorProduct.smul_tmul' b m (1 : B)).symm, hφ₁, (mem_Msub φ).mp hm, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

private theorem lTensor_δ_δ
    (hcoc : (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ (TensorProduct.assoc A B N
          B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ (TensorProduct.assoc A N B
            B).toLinearMap)
    (n : N) : (δ φ).lTensor B (δ φ n) = ι.lTensor B (δ φ n) := by
  have h := LinearMap.congr_fun hcoc ((n ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))
  have e1 : ∀ z : B ⊗[A] N, (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B
      (TensorProduct.assoc A B N B (z ⊗ₜ (1 : B))) = (δ φ).lTensor B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b n' => simp [δ_apply]
  have e2 : ∀ z : B ⊗[A] N, (TensorProduct.comm A N B).toLinearMap.lTensor B
      (TensorProduct.assoc A B N B (z ⊗ₜ (1 : B))) = ι.lTensor B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul b n' => simp [ι_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul,
    TensorProduct.assoc_tmul, TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul] at h
  rw [e1, e2] at h
  exact h

private theorem tmul_one_injective [Module.FaithfullyFlat A B] :
    Function.Injective (fun n : N => n ⊗ₜ[A] (1 : B)) := by

  let g : N →ₗ[A] N ⊗[A] B := (TensorProduct.mk A N B).flip 1
  have hg : ⇑g = fun n : N => n ⊗ₜ[A] (1 : B) := rfl
  rw [← hg]
  let r : B ⊗[A] (N ⊗[A] B) →ₗ[A] B ⊗[A] N :=
    (LinearMap.mul' A B).rTensor N ∘ₗ (TensorProduct.assoc A B B N).symm.toLinearMap ∘ₗ
      (TensorProduct.comm A N B).toLinearMap.lTensor B
  have hr : ∀ z, r (g.lTensor B z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b n => simp [r, g]
  have hinj : Function.Injective (g.lTensor B) := Function.LeftInverse.injective hr
  letI : AddCommGroup (N ⊗[A] B) := inferInstance
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective A B g).mp hinj
private theorem isBaseChange_Msub [Module.FaithfullyFlat A B] (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b
    • x) = b • φ x)
    (hcoc : (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
      (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ (TensorProduct.assoc A B N
          B).toLinearMap ∘ₗ
        (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
        (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ (TensorProduct.assoc A N B
            B).toLinearMap) :
    IsBaseChange B (Msub φ).subtype := by
  let θ : B ⊗[A] Msub φ →ₗ[B] N := (Msub φ).subtype.liftBaseChange B
  let κ : B ⊗[A] Msub φ →ₗ[A] B ⊗[A] N := (Msub φ).subtype.lTensor B
  have hδθ : ∀ y, δ φ (θ y) = κ y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      simp only [θ, κ, LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul,
          Submodule.subtype_apply]
      exact δ_smul_of_mem φ hφ₁ m.2 b
  have hκ : Function.Injective κ :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Msub φ).injective_subtype
  have hδ : Function.Injective (δ φ) := φ.injective.comp tmul_one_injective
  have hθ : Function.Bijective θ := by
    constructor
    · intro y₁ y₂ h
      apply hκ
      rw [← hδθ, ← hδθ, h]
    · intro n

      have hmem : δ φ n ∈ LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor A B (δ φ))
          (TensorProduct.AlgebraTensorModule.lTensor A B ι) := by
        change TensorProduct.AlgebraTensorModule.lTensor A B (δ φ) (δ φ n) =
          TensorProduct.AlgebraTensorModule.lTensor A B ι (δ φ n)
        have := lTensor_δ_δ φ hcoc n
        convert this using 1 <;> rfl
      rw [Module.Flat.eqLocus_lTensor_eq] at hmem
      obtain ⟨y, hy⟩ := hmem
      refine ⟨y, hδ ?_⟩
      rw [hδθ]
      convert hy using 1
      rfl
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ hθ) fun m => ?_
  simp [θ, LinearMap.liftBaseChange_tmul]

private theorem φ_tmul_of_mem (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : N ⊗[A] B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (b b' : B) (m : N) (hm : φ (m ⊗ₜ 1) = 1 ⊗ₜ m) :
    φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) := by
  have h1 : (b • m) ⊗ₜ[A] b' = (LinearMap.mulLeft A b').lTensor N ((b • m) ⊗ₜ[A] (1 : B)) := by
    simp
  rw [h1, hφ₂, ← δ_apply, δ_smul_of_mem φ hφ₁ hm, LinearMap.lTensor_tmul,
      DistribSMul.toLinearMap_apply]
private theorem isBaseChange_eqLocus_of_descentDatum [Module.FaithfullyFlat A B]
    (hφ₁ : ∀ (b : B) (x : N ⊗[A] B), φ (b • x) = b • φ x)
    (hφ₂ : ∀ (b : B) (x : N ⊗[A] B),
      φ ((LinearMap.mulLeft A b).lTensor N x) = (DistribSMul.toLinearMap A N b).lTensor B (φ x))
    (hcocycle :
      (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B =
        (TensorProduct.comm A N B).toLinearMap.lTensor B ∘ₗ
          (TensorProduct.assoc A B N B).toLinearMap ∘ₗ
          (φ : N ⊗[A] B →ₗ[A] B ⊗[A] N).rTensor B ∘ₗ
          (TensorProduct.assoc A N B B).symm.toLinearMap ∘ₗ
          (TensorProduct.comm A B B).toLinearMap.lTensor N ∘ₗ
          (TensorProduct.assoc A N B B).toLinearMap) :
    IsBaseChange B (LinearMap.eqLocus
        ((φ : N ⊗[A] B →ₗ[A] B ⊗[A] N) ∘ₗ (TensorProduct.mk A N B).flip 1)
        (TensorProduct.mk A B N 1)).subtype ∧
      ∀ (b b' : B) (m : N), φ (m ⊗ₜ[A] 1) = 1 ⊗ₜ[A] m →
        φ ((b • m) ⊗ₜ[A] b') = b ⊗ₜ[A] (b' • m) :=
  ⟨isBaseChange_Msub φ hφ₁ hcocycle,
    fun b b' m hm => φ_tmul_of_mem φ hφ₁ hφ₂ b b' m hm⟩

end FaithfullyFlatDescentAux

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

/-- Effective faithfully flat descent for algebras: the equalizer subalgebra
of a descent datum on an algebra base-changes back to the original algebra. -/
public theorem Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    {S : Type*} [CommRing S] (S' : Type*) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (A' : Type*) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')

    (hφlin : φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id
        S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))

    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A'
          S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S'
                  S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom)))))
    :
    let A : Subalgebra S A' :=
      AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a
        => Commute.all _ _)) := by
  intro A
  classical

  set φL : A' ⊗[S] S' ≃ₗ[S] S' ⊗[S] A' := φ.toLinearEquiv with hφL
  have φL_apply : ∀ x, φL x = φ x := fun _ => rfl

  have hlin : ∀ (s t : S'), φ (algebraMap S' A' s ⊗ₜ[S] t) = s ⊗ₜ[S] algebraMap S' A' t := by
    intro s t
    have := AlgHom.congr_fun hφlin (s ⊗ₜ[S] t)
    simpa [Algebra.TensorProduct.map_tmul] using this

  have hleft : ∀ (s : S') (y : S' ⊗[S] A'), (s ⊗ₜ[S] (1 : A')) * y = s • y := by
    intro s y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul',
        smul_eq_mul]
    | add y z hy hz => rw [mul_add, hy, hz, smul_add]
  have hright : ∀ (b : S') (y : S' ⊗[S] A'),
      ((1 : S') ⊗ₜ[S] algebraMap S' A' b) * y = (DistribSMul.toLinearMap S A' b).lTensor S' y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        LinearMap.lTensor_tmul]; simp [Algebra.smul_def]
    | add y z hy hz => rw [mul_add, hy, hz, map_add]

  have hφ₁ : ∀ (b : S') (x : A' ⊗[S] S'), φL (b • x) = b • φL x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      rw [φL_apply, φL_apply, TensorProduct.smul_tmul', Algebra.smul_def,
        show (algebraMap S' A' b * a) ⊗ₜ[S] t = (algebraMap S' A' b ⊗ₜ[S] (1 : S')) * (a ⊗ₜ[S] t) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        map_mul, hlin, map_one, hleft]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

  have hφ₂ : ∀ (b : S') (x : A' ⊗[S] S'),
      φL ((LinearMap.mulLeft S b).lTensor A' x) = (DistribSMul.toLinearMap S A' b).lTensor S' (φL
          x) := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, φL_apply, φL_apply,
        show a ⊗ₜ[S] (b * t) = ((1 : A') ⊗ₜ[S] b) * (a ⊗ₜ[S]
            t) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        map_mul, show (1 : A') = algebraMap S' A' 1 from (map_one _).symm, hlin, ← hright]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

  have agree_mapL : ∀ w : S' ⊗[S] (A' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom w = (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S]
          A').lTensor S' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_mapR : ∀ w : (A' ⊗[S] S') ⊗[S] S',
      Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S') w = (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S]
          A').rTensor S' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v s => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_commL : ∀ w : S' ⊗[S] (A' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A' S').toAlgHom w =
        (_root_.TensorProduct.comm S A' S').toLinearMap.lTensor S' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_commN : ∀ w : A' ⊗[S] (S' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S' S').toAlgHom w =
        (_root_.TensorProduct.comm S S' S').toLinearMap.lTensor A' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc1 : ∀ w : (S' ⊗[S] A') ⊗[S] S',
      (Algebra.TensorProduct.assoc S S S S' A' S') w = (_root_.TensorProduct.assoc S S' A' S') w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v s =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul t a => rfl
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc2 : ∀ w : (A' ⊗[S] S') ⊗[S] S',
      (Algebra.TensorProduct.assoc S S S A' S' S') w = (_root_.TensorProduct.assoc S A' S' S') w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v s =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul a t => rfl
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc2s : ∀ w : A' ⊗[S] (S' ⊗[S] S'),
      (Algebra.TensorProduct.assoc S S S A' S' S').symm w = (_root_.TensorProduct.assoc S A' S' S').symm w := by
    intro w
    apply (Algebra.TensorProduct.assoc S S S A' S' S').injective
    rw [AlgEquiv.apply_symm_apply, agree_assoc2, LinearEquiv.apply_symm_apply]

  have hcoc :
      (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').lTensor S' ∘ₗ
          (_root_.TensorProduct.assoc S S' A' S').toLinearMap ∘ₗ
          (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' =
        (_root_.TensorProduct.comm S A' S').toLinearMap.lTensor S' ∘ₗ
          (_root_.TensorProduct.assoc S S' A' S').toLinearMap ∘ₗ
          (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' ∘ₗ
          (_root_.TensorProduct.assoc S A' S' S').symm.toLinearMap ∘ₗ
          (_root_.TensorProduct.comm S S' S').toLinearMap.lTensor A' ∘ₗ
          (_root_.TensorProduct.assoc S A' S' S').toLinearMap := by
    apply LinearMap.ext
    intro w
    have key := AlgHom.congr_fun hφcoc w
    simp only [AlgHom.coe_comp, Function.comp_apply] at key
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [← agree_mapR, ← agree_assoc1, ← agree_mapL, ← agree_assoc2, ← agree_commN, ← agree_assoc2s,
        ← agree_mapR,
      ← agree_assoc1, ← agree_commL]
    exact key

  obtain ⟨hbc, -⟩ := FaithfullyFlatDescentAux.isBaseChange_eqLocus_of_descentDatum φL hφ₁ hφ₂ hcoc
  have hEq : LinearMap.eqLocus ((φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A') ∘ₗ (TensorProduct.mk S A'
      S').flip 1)
      (TensorProduct.mk S S' A' 1) = A.toSubmodule := by
    ext a
    simp only [LinearMap.mem_eqLocus, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, Subalgebra.mem_toSubmodule]
    show φ (a ⊗ₜ[S] 1) = (1 : S') ⊗ₜ[S] a ↔ a ∈ A
    rw [AlgHom.mem_equalizer]
    rfl
  rw [hEq] at hbc

  have hfun : ∀ x : S' ⊗[S] ↥A,
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _
          _) x = hbc.equiv x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      rw [Algebra.TensorProduct.lift_tmul]
      erw [IsBaseChange.equiv_tmul]
      rw [Algebra.smul_def]
      rfl
    | add x y hx hy => rw [map_add, hx, hy]; erw [map_add]
  have : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all
      _ _) :
      S' ⊗[S] ↥A → A') = hbc.equiv := funext hfun
  rw [this]
  exact hbc.equiv.bijective
