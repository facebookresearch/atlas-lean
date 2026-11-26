/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Module
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Multiplication and tensor-valued first-order linearization

Let `R` be a commutative ring, `I` an ideal, and `M` an `R`-module. Multiplication induces a
surjective `R/I`-linear map `(M/IM) ⊗[R/I] (I/I²) → IM/I²M`, given by `[m] ⊗ [i] ↦ [i • m]`.
It is an equivalence when `M` is flat.

For a flat `M`, multiplication also identifies `I ⊗[R] M` with `IM`; the tensors coming from
`I² ⊆ I` correspond exactly to `I²M` inside `IM`.

If `N` is flat and an `R`-linear map `f : M → N` has range in `IN`, composing its first-order
layer map with the inverse multiplication equivalence gives `M/IM → (N/IN) ⊗[R/I] (I/I²)`.
Applying multiplication to this tensor-valued linearization recovers the class `[f m]` in
`IN/I²N`.

References: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapters 2 and 10.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Function
open scoped Pointwise TensorProduct

universe u v w z

namespace Ideal

variable {R : Type u} [CommRing R]

private def mulToIM (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) (i : I) : ↥(I • (⊤ : Submodule R M)) :=
  ⟨i.1 • m, Submodule.smul_mem_smul i.2 Submodule.mem_top⟩

private theorem mulToIM_add_left (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (m n : M) (i : I) :
    mulToIM I M (m + n) i = mulToIM I M m i + mulToIM I M n i := by
  apply Subtype.ext
  exact smul_add i.1 m n

private theorem mulToIM_smul_left (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (m : M) (i : I) :
    mulToIM I M (r • m) i = r • mulToIM I M m i := by
  apply Subtype.ext
  simp only [mulToIM, Submodule.coe_smul_of_tower, smul_smul]
  rw [mul_comm]

private theorem mulToIM_add_right (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) (i j : I) :
    mulToIM I M m (i + j) = mulToIM I M m i + mulToIM I M m j := by
  apply Subtype.ext
  exact add_smul i.1 j.1 m

private theorem mulToIM_smul_right (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (m : M) (i : I) :
    mulToIM I M m (r • i) = r • mulToIM I M m i := by
  apply Subtype.ext
  change (r * i.1) • m = r • (i.1 • m)
  rw [smul_smul]

private def firstOrderMulRaw (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] I →ₗ[R] I.FirstOrderModuleLayer M :=
  LinearMap.mk₂ R
    (fun m i ↦ Submodule.Quotient.mk (mulToIM I M m i))
    (fun m n i ↦ by
      change Submodule.Quotient.mk (mulToIM I M (m + n) i) =
        Submodule.Quotient.mk (mulToIM I M m i + mulToIM I M n i)
      rw [mulToIM_add_left])
    (fun r m i ↦ by
      change Submodule.Quotient.mk (mulToIM I M (r • m) i) =
        Submodule.Quotient.mk (r • mulToIM I M m i)
      rw [mulToIM_smul_left])
    (fun m i j ↦ by
      change Submodule.Quotient.mk (mulToIM I M m (i + j)) =
        Submodule.Quotient.mk (mulToIM I M m i + mulToIM I M m j)
      rw [mulToIM_add_right])
    (fun r m i ↦ by
      change Submodule.Quotient.mk (mulToIM I M m (r • i)) =
        Submodule.Quotient.mk (r • mulToIM I M m i)
      rw [mulToIM_smul_right])

private theorem firstOrderMulRaw_left_ker (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (I • ⊤ : Submodule R M) ≤ (firstOrderMulRaw I M).ker := by
  intro m hm
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro i
  rw [LinearMap.zero_apply]
  change Submodule.Quotient.mk (mulToIM I M m i) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  have hmem := Submodule.smul_mem_smul i.2
    (show (⟨m, hm⟩ : ↥(I • (⊤ : Submodule R M))) ∈
      (⊤ : Submodule R ↥(I • (⊤ : Submodule R M))) by
        exact Submodule.mem_top)
  have heq : mulToIM I M m i =
      i.1 • (⟨m, hm⟩ : ↥(I • (⊤ : Submodule R M))) :=
    Subtype.ext rfl
  rw [heq]
  exact hmem

private theorem firstOrderMulRaw_right_ker (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (I • ⊤ : Submodule R I) ≤ (firstOrderMulRaw I M).flip.ker := by
  intro i hi
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro m
  rw [LinearMap.zero_apply, LinearMap.flip_apply]
  change Submodule.Quotient.mk (mulToIM I M m i) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine Submodule.smul_induction_on
    (p := fun j : I ↦ mulToIM I M m j ∈
      I • (⊤ : Submodule R ↥(I • (⊤ : Submodule R M))))
    hi ?_ ?_
  · intro r hr j _
    rw [mulToIM_smul_right]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [mulToIM_add_right]
    exact (I • (⊤ : Submodule R
      ↥(I • (⊤ : Submodule R M)))).add_mem hx hy

private def firstOrderMulBilinear (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R]
      I.Cotangent →ₗ[R] I.FirstOrderModuleLayer M :=
  (firstOrderMulRaw I M).liftQ₂
    (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R I)
    (firstOrderMulRaw_left_ker I M) (firstOrderMulRaw_right_ker I M)

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M` an `R`-module. Multiplication defines
the `R/I`-linear map `(M/IM) ⊗[R/I] I.Cotangent → I.FirstOrderModuleLayer M`, where
`I.Cotangent = I/I²` and the target is `IM/I²M`. It sends `[m] ⊗ I.toCotangent i` to the class
of `(i : R) • m`. -/
def firstOrderMul (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] I.Cotangent
      →ₗ[R ⧸ I] I.FirstOrderModuleLayer M := by
  let b := firstOrderMulBilinear I M
  let b₁ : (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R]
      I.Cotangent →ₗ[R ⧸ I] I.FirstOrderModuleLayer M :=
    { toFun := fun m ↦
        (b m).extendScalarsOfSurjective
          (Ideal.Quotient.mk_surjective (I := I))
      map_add' := fun x y ↦ by
        apply LinearMap.ext
        intro z
        change b (x + y) z = b x z + b y z
        rw [map_add, LinearMap.add_apply]
      map_smul' := fun r x ↦ by
        apply LinearMap.ext
        intro z
        change b (r • x) z = r • b x z
        rw [map_smul, LinearMap.smul_apply] }
  let b₂ := b₁.extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))
  exact TensorProduct.lift b₂

@[simp]
theorem firstOrderMul_mk_tmul_toCotangent (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) (i : I) :
    firstOrderMul I M
      (Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] I.toCotangent i) =
      Submodule.Quotient.mk
        (⟨i.1 • m, Submodule.smul_mem_smul i.2 Submodule.mem_top⟩ :
          ↥(I • (⊤ : Submodule R M))) := by
  rw [firstOrderMul]
  rfl

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, `firstOrderMul I M : (M/IM)
⊗[R/I] (I/I²) → IM/I²M` is surjective. Every first-order class is a sum of products `[i • m]`
and therefore has a preimage in this tensor product. -/
theorem firstOrderMul_surjective (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Surjective (firstOrderMul I M) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨hx, t, ht⟩ := Submodule.smul_induction_on
    (p := fun m : M ↦ ∃ hm : m ∈ I • (⊤ : Submodule R M),
      ∃ t, firstOrderMul I M t =
        Submodule.Quotient.mk
          (⟨m, hm⟩ : ↥(I • (⊤ : Submodule R M))))
    x.2 (by
      intro i hi m _
      let hm : i • m ∈ I • (⊤ : Submodule R M) :=
        Submodule.smul_mem_smul hi Submodule.mem_top
      refine ⟨hm, Submodule.Quotient.mk m ⊗ₜ[R ⧸ I]
        I.toCotangent ⟨i, hi⟩, ?_⟩
      rw [firstOrderMul_mk_tmul_toCotangent]) (by
      intro x y hx hy
      obtain ⟨hxmem, tx, htx⟩ := hx
      obtain ⟨hymem, ty, hty⟩ := hy
      let hxy : x + y ∈ I • (⊤ : Submodule R M) :=
        (I • (⊤ : Submodule R M)).add_mem hxmem hymem
      refine ⟨hxy, tx + ty, ?_⟩
      rw [map_add, htx, hty]
      congr 1)
  refine ⟨t, ht.trans ?_⟩
  congr 1

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, `tensorSMulMap I M : I ⊗[R]
M →ₗ[R] M` is multiplication, with `i ⊗ m ↦ (i : R) • m`. -/
def tensorSMulMap (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    I ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)

@[simp]
theorem tensorSMulMap_tmul (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (i : I) (m : M) :
    tensorSMulMap I M (i ⊗ₜ[R] m) = i.1 • m := by
  simp [tensorSMulMap]

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, the range of `tensorSMulMap
I M : I ⊗[R] M → M` is exactly `IM = I • (⊤ : Submodule R M)`. -/
theorem tensorSMulMap_range (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    LinearMap.range (tensorSMulMap I M) =
      I • (⊤ : Submodule R M) := by
  rw [tensorSMulMap, LinearMap.range_comp]
  exact Submodule.map_range_rTensor_subtype_lid

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M` a flat `R`-module. Multiplication gives
the `R`-linear equivalence `I ⊗[R] M ≃ₗ[R] IM`, sending `i ⊗ m` to the element of `IM` with
underlying value `(i : R) • m`. -/
@[no_expose]
def tensorSMulEquiv (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    I ⊗[R] M ≃ₗ[R] ↥(I • (⊤ : Submodule R M)) := by
  let f := tensorSMulMap I M
  let fc := f.codRestrict (I • (⊤ : Submodule R M)) fun x ↦ by
    rw [← tensorSMulMap_range I M]
    exact LinearMap.mem_range_self f x
  apply LinearEquiv.ofBijective fc
  constructor
  · intro x y hxy
    apply ((TensorProduct.lid R M).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap
        I.subtype Subtype.val_injective))
    exact congrArg Subtype.val hxy
  · intro y
    have hy : (y : M) ∈ LinearMap.range f := by
      rw [tensorSMulMap_range I M]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

@[simp]
theorem tensorSMulEquiv_tmul (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M]
    (i : I) (m : M) :
    tensorSMulEquiv I M (i ⊗ₜ[R] m) =
      (⟨i.1 • m, Submodule.smul_mem_smul i.2 Submodule.mem_top⟩ :
        ↥(I • (⊤ : Submodule R M))) := by
  rw [tensorSMulEquiv]
  rfl

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M` a flat `R`-module. Under
`tensorSMulEquiv I M : I ⊗[R] M ≃ IM`, the image of the tensor inclusion `(I • ⊤ : Submodule R
I) ⊗[R] M → I ⊗[R] M` is exactly `(I • ⊤ : Submodule R IM)`. Thus the tensors from `I² ⊆ I`
correspond to `I(IM) = I²M` inside `IM`. -/
theorem tensorSMulEquiv_map_range (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Submodule.map (tensorSMulEquiv I M).toLinearMap
        (LinearMap.range
          ((I • ⊤ : Submodule R I).subtype.rTensor M)) =
      I • (⊤ : Submodule R ↥(I • (⊤ : Submodule R M))) := by
  let IM : Submodule R M := I • ⊤
  let J : Submodule R I := I • ⊤
  let h : J →ₗ[R] R := I.subtype.comp J.subtype
  have hrange : LinearMap.range h = (I ^ 2 : Ideal R) := by
    dsimp only [h, J]
    rw [LinearMap.range_comp, Submodule.range_subtype,
      Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
      Ideal.smul_eq_mul, pow_two]
  let eJ : J ≃ₗ[R] (I ^ 2 : Ideal R) :=
    (LinearEquiv.ofInjective h
      (I.subtype_injective.comp J.subtype_injective)).trans
        (LinearEquiv.ofEq _ _ hrange)
  have hmaps :
      (tensorSMulMap I M).comp (J.subtype.rTensor M) =
        ((TensorProduct.lid R M).toLinearMap.comp
          ((I ^ 2 : Ideal R).subtype.rTensor M)).comp
            (eJ.toLinearMap.rTensor M) := by
    apply TensorProduct.ext'
    intro j m
    simp [tensorSMulMap, eJ, h, J]
  apply Submodule.map_injective_of_injective (f := IM.subtype)
    IM.subtype_injective
  have he : IM.subtype.comp (tensorSMulEquiv I M).toLinearMap =
      tensorSMulMap I M := by
    rfl
  have hre : LinearMap.range (eJ.toLinearMap.rTensor M) = ⊤ :=
    LinearMap.range_eq_top.mpr (eJ.rTensor M).surjective
  rw [← Submodule.map_comp, he, ← LinearMap.range_comp, hmaps,
    LinearMap.range_comp, hre, Submodule.map_top,
    LinearMap.range_comp, Submodule.map_range_rTensor_subtype_lid]
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
    ← Submodule.mul_smul, pow_two]

private def firstOrderSourceEquiv (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] I.Cotangent
      ≃ₗ[R ⧸ I] I.Cotangent ⊗[R] M :=
  let q : ((R ⧸ I) ⊗[R] M) ≃ₗ[R]
      (M ⧸ (I • ⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M I
  let qk : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I]
      (M ⧸ (I • ⊤ : Submodule R M)) :=
    q.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
  (TensorProduct.congr qk.symm
      (LinearEquiv.refl (R ⧸ I) I.Cotangent)).trans
    ((TensorProduct.comm (R ⧸ I) _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R (R ⧸ I) (R ⧸ I) I.Cotangent M))

private theorem firstOrderSourceEquiv_mk_tmul_toCotangent
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) (i : I) :
    firstOrderSourceEquiv I M
      (Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] I.toCotangent i) =
        I.toCotangent i ⊗ₜ[R] m := by
  simp [firstOrderSourceEquiv]

private def cotangentQuotientEquiv (I : Ideal R) :
    I.Cotangent ≃ₗ[R] (I ⧸ (I • ⊤ : Submodule R I)) := by
  change (I ⧸ (I • ⊤ : Submodule R I)) ≃ₗ[R]
    (I ⧸ (I • ⊤ : Submodule R I))
  exact LinearEquiv.refl R _

@[simp]
private theorem cotangentQuotientEquiv_toCotangent
    (I : Ideal R) (i : I) :
    cotangentQuotientEquiv I (I.toCotangent i) =
      (Submodule.Quotient.mk i : I ⧸ (I • ⊤ : Submodule R I)) :=
  rfl

private def firstOrderQuotientEquiv (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    I.Cotangent ⊗[R] M ≃ₗ[R] I.FirstOrderModuleLayer M := by
  let J : Submodule R I := I • ⊤
  let D : Submodule R (I ⊗[R] M) :=
    LinearMap.range (TensorProduct.map J.subtype LinearMap.id)
  let E : Submodule R ↥(I • (⊤ : Submodule R M)) := I • ⊤
  exact ((cotangentQuotientEquiv I).rTensor M).trans
    ((TensorProduct.quotientTensorEquiv M J).trans
      (Submodule.Quotient.equiv D E (tensorSMulEquiv I M)
        (by simpa only [D, LinearMap.rTensor_def] using
          tensorSMulEquiv_map_range I M)))

private theorem firstOrderQuotientEquiv_tmul
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Flat R M] (i : I) (m : M) :
    firstOrderQuotientEquiv I M (I.toCotangent i ⊗ₜ[R] m) =
      Submodule.Quotient.mk (mulToIM I M m i) := by
  rw [firstOrderQuotientEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply,
    LinearEquiv.rTensor_tmul, cotangentQuotientEquiv_toCotangent,
    TensorProduct.quotientTensorEquiv_apply_tmul_mk,
    Submodule.Quotient.equiv_apply]
  change Submodule.Quotient.mk
    (tensorSMulEquiv I M (i ⊗ₜ[R] m)) = _
  rw [tensorSMulEquiv_tmul]
  congr 1

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M` a flat `R`-module. The multiplication
map is the `R/I`-linear equivalence `(M/IM) ⊗[R/I] (I/I²) ≃ₗ[R/I] IM/I²M`, with `[m] ⊗ [i] ↦
[i • m]`. -/
@[no_expose]
def firstOrderMulEquiv (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    (M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] I.Cotangent
      ≃ₗ[R ⧸ I] I.FirstOrderModuleLayer M := by
  let d :
      ((M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] I.Cotangent)
        ≃ₗ[R ⧸ I] I.Cotangent ⊗[R] M :=
    firstOrderSourceEquiv I M
  let q : I.Cotangent ⊗[R] M ≃ₗ[R] I.FirstOrderModuleLayer M :=
    firstOrderQuotientEquiv I M
  let fR :
      ((M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] I.Cotangent)
        →ₗ[R] I.FirstOrderModuleLayer M :=
    q.toLinearMap.comp (d.toLinearMap.restrictScalars R)
  let f := fR.extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))
  apply LinearEquiv.ofBijective f
  constructor
  · change Function.Injective (fun x ↦ q (d x))
    exact q.injective.comp d.injective
  · change Function.Surjective (fun x ↦ q (d x))
    exact q.surjective.comp d.surjective

private theorem firstOrderMulEquiv_mk_tmul_toCotangent
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Flat R M] (m : M) (i : I) :
    firstOrderMulEquiv I M
      (Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] I.toCotangent i) =
      Submodule.Quotient.mk (mulToIM I M m i) := by
  rw [firstOrderMulEquiv]
  change firstOrderQuotientEquiv I M
      (firstOrderSourceEquiv I M
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] I.toCotangent i)) = _
  rw [firstOrderSourceEquiv_mk_tmul_toCotangent,
    firstOrderQuotientEquiv_tmul]

/-- For an ideal `I` in a commutative ring `R` and a flat `R`-module `M`, the underlying linear
map of `firstOrderMulEquiv I M` is `firstOrderMul I M`. Both maps have source `(M/IM) ⊗[R/I]
(I/I²)`, target `IM/I²M`, and value `[m] ⊗ [i] ↦ [i • m]`. -/
theorem firstOrderMulEquiv_toLinearMap (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    (firstOrderMulEquiv I M).toLinearMap = firstOrderMul I M := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨i, rfl⟩ := I.toCotangent_surjective y
  exact (firstOrderMulEquiv_mk_tmul_toCotangent I M m i).trans
    (firstOrderMul_mk_tmul_toCotangent I M m i).symm

/-- For an ideal `I` in a commutative ring `R` and a flat `R`-module `M`, `firstOrderMul I M :
(M/IM) ⊗[R/I] (I/I²) → IM/I²M` is bijective. -/
theorem firstOrderMul_bijective_of_flat (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Bijective (firstOrderMul I M) := by
  rw [← firstOrderMulEquiv_toLinearMap]
  exact (firstOrderMulEquiv I M).bijective

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M` a flat `R`-module. This is the inverse
`R/I`-linear equivalence `IM/I²M ≃ₗ[R/I] (M/IM) ⊗[R/I] (I/I²)` to first-order multiplication.
In particular, the class `[i • m]` maps to `[m] ⊗ [i]`. -/
@[no_expose]
def firstOrderLayerEquiv (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    I.FirstOrderModuleLayer M ≃ₗ[R ⧸ I]
      (M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] I.Cotangent :=
  (firstOrderMulEquiv I M).symm

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. Write
`f̄ : M/IM → N/IN` for reduction modulo `I`, `gr₁(f) : IM/I²M → IN/I²N` for the induced layer
map, and `μ_M, μ_N` for first-order multiplication. Then `gr₁(f) ∘ μ_M = μ_N ∘ (f̄ ⊗
id_(I/I²))`. -/
theorem firstOrderMul_naturality (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (firstOrderLayerMap I f).comp (firstOrderMul I M) =
      (firstOrderMul I N).comp
        (TensorProduct.map (f.reduceModIdeal I) LinearMap.id) := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨i, rfl⟩ := I.toCotangent_surjective y
  change firstOrderLayerMap I f
      (firstOrderMul I M
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] I.toCotangent i)) =
    firstOrderMul I N
      (TensorProduct.map (f.reduceModIdeal I) LinearMap.id
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] I.toCotangent i))
  rw [firstOrderMul_mk_tmul_toCotangent, TensorProduct.map_tmul,
    LinearMap.reduceModIdeal_apply, LinearMap.id_apply,
    firstOrderMul_mk_tmul_toCotangent, firstOrderLayerMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact f.map_smul i.1 m

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be flat `R`-modules, and `f : M →ₗ[R] N`.
If `E_M, E_N` denote the inverse first-order equivalences and `f̄, gr₁(f)` the reduced and
layer maps, then `(f̄ ⊗ id_(I/I²)) ∘ E_M = E_N ∘ gr₁(f)` as maps `IM/I²M → (N/IN) ⊗[R/I]
(I/I²)`. -/
theorem firstOrderLayerEquiv_naturality (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N) :
    (TensorProduct.map (f.reduceModIdeal I) LinearMap.id).comp
        (firstOrderLayerEquiv I M).toLinearMap =
      (firstOrderLayerEquiv I N).toLinearMap.comp
        (firstOrderLayerMap I f) := by
  apply LinearMap.ext
  intro x
  change TensorProduct.map (f.reduceModIdeal I) LinearMap.id
      ((firstOrderMulEquiv I M).symm x) =
    (firstOrderMulEquiv I N).symm (firstOrderLayerMap I f x)
  apply (firstOrderMulEquiv I N).injective
  let t := (firstOrderMulEquiv I M).symm x
  have h := LinearMap.congr_fun (firstOrderMul_naturality I f) t
  rw [← firstOrderMulEquiv_toLinearMap I M,
    ← firstOrderMulEquiv_toLinearMap I N] at h
  calc
    _ = firstOrderLayerMap I f (firstOrderMulEquiv I M t) := h.symm
    _ = firstOrderLayerMap I f x := by
      rw [LinearEquiv.apply_symm_apply]
    _ = firstOrderMulEquiv I N
        ((firstOrderMulEquiv I N).symm (firstOrderLayerMap I f x)) := by
      rw [LinearEquiv.apply_symm_apply]

end Ideal

namespace LinearMap

variable {R : Type u} [CommRing R]

/-- Let `R` be a commutative ring, `I : Ideal R`, and `M,N` be `R`-modules with `N` flat. If `f :
M →ₗ[R] N` has range contained in `IN`, this is the `R/I`-linear map `M/IM → (N/IN) ⊗[R/I]
(I/I²)` obtained by taking `[m] ↦ [f m]` in `IN/I²N` and then applying the inverse first-order
multiplication equivalence for `N`. -/
@[no_expose]
def linearizationAtIdeal (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : LinearMap.range f ≤ I • (⊤ : Submodule R N)) :
    (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R ⧸ I]
      (N ⧸ (I • ⊤ : Submodule R N)) ⊗[R ⧸ I] I.Cotangent :=
  (I.firstOrderLayerEquiv N).toLinearMap.comp (f.linearizedLayer I hf)

/-- Let `R` be a commutative ring, `I` an ideal, and `M,N` be `R`-modules with `N` flat. For an
`R`-linear map `f : M → N` whose range lies in `IN`, composing its tensor-valued linearization
with `firstOrderMul I N` gives its layer-valued linearization: `μ_N ∘ λ_I(f) =
f.linearizedLayer I hf`. -/
theorem firstOrderMul_comp_linearizationAtIdeal (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : LinearMap.range f ≤ I • (⊤ : Submodule R N)) :
    (I.firstOrderMul N).comp (f.linearizationAtIdeal I hf) =
      f.linearizedLayer I hf := by
  apply LinearMap.ext
  intro x
  change I.firstOrderMul N
      ((I.firstOrderMulEquiv N).symm (f.linearizedLayer I hf x)) =
    f.linearizedLayer I hf x
  rw [← I.firstOrderMulEquiv_toLinearMap]
  change I.firstOrderMulEquiv N
      ((I.firstOrderMulEquiv N).symm (f.linearizedLayer I hf x)) =
    f.linearizedLayer I hf x
  exact (I.firstOrderMulEquiv N).apply_symm_apply _

/-- Let `R` be a commutative ring, `I` an ideal, and `M,N` be `R`-modules with `N` flat. If `f : M
→ₗ[R] N` has range in `IN`, then for every `x : M`, `firstOrderMul I N (f.linearizationAtIdeal
I hf [x])` is the class `[f x]` in `IN/I²N`. Here `hf` is the range inclusion and `[x]` is the
quotient class in `M/IM`. -/
@[simp]
theorem firstOrderMul_linearizationAtIdeal_mk (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (hf : LinearMap.range f ≤ I • (⊤ : Submodule R N)) (x : M) :
    I.firstOrderMul N
        (f.linearizationAtIdeal I hf (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk
        (⟨f x, hf (LinearMap.mem_range_self f x)⟩ :
          ↥(I • (⊤ : Submodule R N))) := by
  have h := LinearMap.congr_fun
    (firstOrderMul_comp_linearizationAtIdeal I f hf)
    (Submodule.Quotient.mk x)
  simpa only [LinearMap.comp_apply, linearizedLayer_mk] using h

private theorem linearizedLayer_naturality (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {M' : Type z} [AddCommGroup M'] [Module R M']
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (d : M →ₗ[R] N) (e : M' →ₗ[R] N')
    (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (hd : LinearMap.range d ≤ I • (⊤ : Submodule R N))
    (he : LinearMap.range e ≤ I • (⊤ : Submodule R N'))
    (hsq : b.comp d = e.comp a) :
    (I.firstOrderLayerMap b).comp (d.linearizedLayer I hd) =
      (e.linearizedLayer I he).comp (a.reduceModIdeal I) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  change I.firstOrderLayerMap b
      (d.linearizedLayer I hd (Submodule.Quotient.mk x)) =
    e.linearizedLayer I he
      (a.reduceModIdeal I (Submodule.Quotient.mk x))
  calc
    _ = I.firstOrderLayerMap b
        (Submodule.Quotient.mk
          (⟨d x, hd (LinearMap.mem_range_self d x)⟩ :
            ↥(I • (⊤ : Submodule R N)))) := by
      rw [linearizedLayer_mk]
    _ = Submodule.Quotient.mk
        (⟨b (d x),
          (Submodule.smul_top_le_comap_smul_top I b)
            (hd (LinearMap.mem_range_self d x))⟩ :
          ↥(I • (⊤ : Submodule R N'))) :=
      I.firstOrderLayerMap_mk b _
    _ = Submodule.Quotient.mk
        (⟨e (a x), he (LinearMap.mem_range_self e (a x))⟩ :
          ↥(I • (⊤ : Submodule R N'))) := by
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact LinearMap.congr_fun hsq x
    _ = e.linearizedLayer I he (Submodule.Quotient.mk (a x)) :=
      (linearizedLayer_mk I e he (a x)).symm
    _ = e.linearizedLayer I he
        (a.reduceModIdeal I (Submodule.Quotient.mk x)) := by
      rw [LinearMap.reduceModIdeal_apply]

/-- Let `R` be a commutative ring, `I` an ideal, and `M,M',N,N'` be `R`-modules with `N,N'` flat.
Let `d : M → N`, `e : M' → N'`, `a : M → M'`, and `b : N → N'` be `R`-linear maps with `b ∘ d
= e ∘ a`, `d(M) ⊆ IN`, and `e(M') ⊆ IN'`. For the reduced maps `ā,b̄` modulo `I`, their
tensor-valued linearizations satisfy `(b̄ ⊗ id_(I/I²)) ∘ λ_I(d) = λ_I(e) ∘ ā`. -/
theorem linearizationAtIdeal_naturality (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    {M' : Type z} [AddCommGroup M'] [Module R M']
    {N' : Type*} [AddCommGroup N'] [Module R N'] [Module.Flat R N']
    (d : M →ₗ[R] N) (e : M' →ₗ[R] N')
    (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (hd : LinearMap.range d ≤ I • (⊤ : Submodule R N))
    (he : LinearMap.range e ≤ I • (⊤ : Submodule R N'))
    (hsq : b.comp d = e.comp a) :
    (TensorProduct.map (b.reduceModIdeal I) LinearMap.id).comp
        (d.linearizationAtIdeal I hd) =
      (e.linearizationAtIdeal I he).comp (a.reduceModIdeal I) := by
  apply LinearMap.ext
  intro x
  change TensorProduct.map (b.reduceModIdeal I) LinearMap.id
      (I.firstOrderLayerEquiv N (d.linearizedLayer I hd x)) =
    I.firstOrderLayerEquiv N'
      (e.linearizedLayer I he (a.reduceModIdeal I x))
  calc
    _ = I.firstOrderLayerEquiv N'
        (I.firstOrderLayerMap b (d.linearizedLayer I hd x)) :=
      LinearMap.congr_fun (I.firstOrderLayerEquiv_naturality b)
        (d.linearizedLayer I hd x)
    _ = I.firstOrderLayerEquiv N'
        (e.linearizedLayer I he (a.reduceModIdeal I x)) :=
      congrArg (I.firstOrderLayerEquiv N')
        (LinearMap.congr_fun
          (linearizedLayer_naturality I d e a b hd he hsq) x)

end LinearMap
